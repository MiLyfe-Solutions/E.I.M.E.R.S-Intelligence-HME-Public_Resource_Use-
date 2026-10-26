import V185TrunkScan23Chunk1281

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7594900 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7594900 : Nat := 118140960795 + 7594900 * 2 ^ 59
def prefixEnd_7594900 : Nat := 4983230072969 + 3 ^ 40 * 7594900 * 2
def baseEnd_7594900 : Nat := 3899834222832440152521697

theorem tailTrace_7594900 : CollatzResearch.WordTrace tailWord_7594900 prefixEnd_7594900 3899834222832440152521697 := by
  unfold tailWord_7594900
  simp only [CollatzResearch.WordTrace]
  refine ⟨138504380092490940248627077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184672506789987920331502769 138504380092490940248627077)
  ·
    refine ⟨25969571267342051296617577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138504380092490940248627077 25969571267342051296617577)
    ·
      refine ⟨19477178450506538472463183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25969571267342051296617577 19477178450506538472463183)
      ·
        refine ⟨29215767675759807708694775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19477178450506538472463183 29215767675759807708694775)
        ·
          refine ⟨43823651513639711563042163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29215767675759807708694775 43823651513639711563042163)
          ·
            refine ⟨65735477270459567344563245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43823651513639711563042163 65735477270459567344563245)
            ·
              refine ⟨24650803976422337754211217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65735477270459567344563245 24650803976422337754211217)
              ·
                refine ⟨18488102982316753315658413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24650803976422337754211217 18488102982316753315658413)
                ·
                  refine ⟨6933038618368782493371905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18488102982316753315658413 6933038618368782493371905)
                  ·
                    refine ⟨5199778963776586870028929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6933038618368782493371905 5199778963776586870028929)
                    ·
                      refine ⟨3899834222832440152521697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199778963776586870028929 3899834222832440152521697)
                      ·
                        rfl

theorem cell23_7594900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7594900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594900 prefixEnd_7594900 := by exact prefixLift 7594900
  have htrace : WordTrace (prefixWord ++ tailWord_7594900) baseStart_7594900 baseEnd_7594900 := by
    simpa [prefixWord, tailWord_7594900, baseEnd_7594900] using wordTrace_append hprefix tailTrace_7594900
  have hstable : (prefixWord ++ tailWord_7594900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594900).length < 2 ^ (prefixWord ++ tailWord_7594900).sum := by decide
  have hdescent : baseEnd_7594900 < baseStart_7594900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594916 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_7594916 : Nat := 118140960795 + 7594916 * 2 ^ 59
def prefixEnd_7594916 : Nat := 4983230072969 + 3 ^ 40 * 7594916 * 2
def baseEnd_7594916 : Nat := 3899842438522912089921623

theorem tailTrace_7594916 : CollatzResearch.WordTrace tailWord_7594916 prefixEnd_7594916 3899842438522912089921623 := by
  unfold tailWord_7594916
  simp only [CollatzResearch.WordTrace]
  refine ⟨138504671876461957614918301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184672895835282610153224401 138504671876461957614918301)
  ·
    refine ⟨51939251953673234105594363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138504671876461957614918301 51939251953673234105594363)
    ·
      refine ⟨77908877930509851158391545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51939251953673234105594363 77908877930509851158391545)
      ·
        refine ⟨58431658447882388368793659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77908877930509851158391545 58431658447882388368793659)
        ·
          refine ⟨87647487671823582553190489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58431658447882388368793659 87647487671823582553190489)
          ·
            refine ⟨65735615753867686914892867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87647487671823582553190489 65735615753867686914892867)
            ·
              refine ⟨98603423630801530372339301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65735615753867686914892867 98603423630801530372339301)
              ·
                refine ⟨18488141930775286944813619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98603423630801530372339301 18488141930775286944813619)
                ·
                  refine ⟨27732212896162930417220429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18488141930775286944813619 27732212896162930417220429)
                  ·
                    refine ⟨10399579836061098906457661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27732212896162930417220429 10399579836061098906457661)
                    ·
                      refine ⟨3899842438522912089921623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399579836061098906457661 3899842438522912089921623)
                      ·
                        rfl

theorem cell23_7594916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_7594916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594916 prefixEnd_7594916 := by exact prefixLift 7594916
  have htrace : WordTrace (prefixWord ++ tailWord_7594916) baseStart_7594916 baseEnd_7594916 := by
    simpa [prefixWord, tailWord_7594916, baseEnd_7594916] using wordTrace_append hprefix tailTrace_7594916
  have hstable : (prefixWord ++ tailWord_7594916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594916).length < 2 ^ (prefixWord ++ tailWord_7594916).sum := by decide
  have hdescent : baseEnd_7594916 < baseStart_7594916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7594933 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_7594933 : Nat := 118140960795 + 7594933 * 2 ^ 59
def prefixEnd_7594933 : Nat := 4983230072969 + 3 ^ 40 * 7594933 * 2
def baseEnd_7594933 : Nat := 3899851167694038523409045

theorem tailTrace_7594933 : CollatzResearch.WordTrace tailWord_7594933 prefixEnd_7594933 3899851167694038523409045 := by
  unfold tailWord_7594933
  simp only [CollatzResearch.WordTrace]
  refine ⟨277009963793862327133205453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184673309195908218088803635 277009963793862327133205453)
  ·
    refine ⟨103878736422698372674952045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277009963793862327133205453 103878736422698372674952045)
    ·
      refine ⟨38954526158511889753107017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103878736422698372674952045 38954526158511889753107017)
      ·
        refine ⟨29215894618883917314830263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38954526158511889753107017 29215894618883917314830263)
        ·
          refine ⟨43823841928325875972245395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29215894618883917314830263 43823841928325875972245395)
          ·
            refine ⟨65735762892488813958368093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43823841928325875972245395 65735762892488813958368093)
            ·
              refine ⟨24650911084683305234388035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65735762892488813958368093 24650911084683305234388035)
              ·
                refine ⟨36976366627024957851582053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24650911084683305234388035 36976366627024957851582053)
                ·
                  refine ⟨6933068742567179597171635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36976366627024957851582053 6933068742567179597171635)
                  ·
                    refine ⟨10399603113850769395757453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6933068742567179597171635 10399603113850769395757453)
                    ·
                      refine ⟨3899851167694038523409045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10399603113850769395757453 3899851167694038523409045)
                      ·
                        rfl

theorem cell23_7594933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_7594933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7594933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7594933 prefixEnd_7594933 := by exact prefixLift 7594933
  have htrace : WordTrace (prefixWord ++ tailWord_7594933) baseStart_7594933 baseEnd_7594933 := by
    simpa [prefixWord, tailWord_7594933, baseEnd_7594933] using wordTrace_append hprefix tailTrace_7594933
  have hstable : (prefixWord ++ tailWord_7594933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7594933).length < 2 ^ (prefixWord ++ tailWord_7594933).sum := by decide
  have hdescent : baseEnd_7594933 < baseStart_7594933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7594933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595047 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 5]
def baseStart_7595047 : Nat := 118140960795 + 7595047 * 2 ^ 59
def prefixEnd_7595047 : Nat := 4983230072969 + 3 ^ 40 * 7595047 * 2
def baseEnd_7595047 : Nat := 433323300498739008598169

theorem tailTrace_7595047 : CollatzResearch.WordTrace tailWord_7595047 prefixEnd_7595047 433323300498739008598169 := by
  unfold tailWord_7595047
  simp only [CollatzResearch.WordTrace]
  refine ⟨277014121715449324602855395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184676081143632883068570263 277014121715449324602855395)
  ·
    refine ⟨415521182573173986904283093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277014121715449324602855395 415521182573173986904283093)
    ·
      refine ⟨9738777716558765318069135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 415521182573173986904283093 9738777716558765318069135)
      ·
        refine ⟨14608166574838147977103703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738777716558765318069135 14608166574838147977103703)
        ·
          refine ⟨21912249862257221965655555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14608166574838147977103703 21912249862257221965655555)
          ·
            refine ⟨32868374793385832948483333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21912249862257221965655555 32868374793385832948483333)
            ·
              refine ⟨6162820273759843677840625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32868374793385832948483333 6162820273759843677840625)
              ·
                refine ⟨4622115205319882758380469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162820273759843677840625 4622115205319882758380469)
                ·
                  refine ⟨433323300498739008598169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622115205319882758380469 433323300498739008598169)
                  ·
                    rfl

theorem cell23_7595047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 5].length) (baseStart_7595047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595047 prefixEnd_7595047 := by exact prefixLift 7595047
  have htrace : WordTrace (prefixWord ++ tailWord_7595047) baseStart_7595047 baseEnd_7595047 := by
    simpa [prefixWord, tailWord_7595047, baseEnd_7595047] using wordTrace_append hprefix tailTrace_7595047
  have hstable : (prefixWord ++ tailWord_7595047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595047).length < 2 ^ (prefixWord ++ tailWord_7595047).sum := by decide
  have hdescent : baseEnd_7595047 < baseStart_7595047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595086 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_7595086 : Nat := 118140960795 + 7595086 * 2 ^ 59
def prefixEnd_7595086 : Nat := 4983230072969 + 3 ^ 40 * 7595086 * 2
def baseEnd_7595086 : Nat := 433325525581575158310649

theorem tailTrace_7595086 : CollatzResearch.WordTrace tailWord_7595086 prefixEnd_7595086 433325525581575158310649 := by
  unfold tailWord_7595086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626943020288504282940639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184677029441538689509016741 34626943020288504282940639)
  ·
    refine ⟨51940414530432756424410959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34626943020288504282940639 51940414530432756424410959)
    ·
      refine ⟨77910621795649134636616439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51940414530432756424410959 77910621795649134636616439)
      ·
        refine ⟨116865932693473701954924659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77910621795649134636616439 116865932693473701954924659)
        ·
          refine ⟨175298899040210552932386989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116865932693473701954924659 175298899040210552932386989)
          ·
            refine ⟨65737087140078957349645121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175298899040210552932386989 65737087140078957349645121)
            ·
              refine ⟨49302815355059218012233841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65737087140078957349645121 49302815355059218012233841)
              ·
                refine ⟨36977111516294413509175381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49302815355059218012233841 36977111516294413509175381)
                ·
                  refine ⟨433325525581575158310649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36977111516294413509175381 433325525581575158310649)
                  ·
                    rfl

theorem cell23_7595086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_7595086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595086 prefixEnd_7595086 := by exact prefixLift 7595086
  have htrace : WordTrace (prefixWord ++ tailWord_7595086) baseStart_7595086 baseEnd_7595086 := by
    simpa [prefixWord, tailWord_7595086, baseEnd_7595086] using wordTrace_append hprefix tailTrace_7595086
  have hstable : (prefixWord ++ tailWord_7595086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595086).length < 2 ^ (prefixWord ++ tailWord_7595086).sum := by decide
  have hdescent : baseEnd_7595086 < baseStart_7595086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595140 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_7595140 : Nat := 118140960795 + 7595140 * 2 ^ 59
def prefixEnd_7595140 : Nat := 4983230072969 + 3 ^ 40 * 7595140 * 2
def baseEnd_7595140 : Nat := 3899957458189519213520593

theorem tailTrace_7595140 : CollatzResearch.WordTrace tailWord_7595140 prefixEnd_7595140 3899957458189519213520593 := by
  unfold tailWord_7595140
  simp only [CollatzResearch.WordTrace]
  refine ⟨138508756852056200742995437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184678342469408267657327249 138508756852056200742995437)
  ·
    refine ⟨51940783819521075278623289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138508756852056200742995437 51940783819521075278623289)
    ·
      refine ⟨38955587864640806458967467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51940783819521075278623289 38955587864640806458967467)
      ·
        refine ⟨58433381796961209688451201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38955587864640806458967467 58433381796961209688451201)
        ·
          refine ⟨43825036347720907266338401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58433381796961209688451201 43825036347720907266338401)
          ·
            refine ⟨32868777260790680449753801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43825036347720907266338401 32868777260790680449753801)
            ·
              refine ⟨24651582945593010337315351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32868777260790680449753801 24651582945593010337315351)
              ·
                refine ⟨36977374418389515505973027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24651582945593010337315351 36977374418389515505973027)
                ·
                  refine ⟨55466061627584273258959541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36977374418389515505973027 55466061627584273258959541)
                  ·
                    refine ⟨5199943277586025618027457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55466061627584273258959541 5199943277586025618027457)
                    ·
                      refine ⟨3899957458189519213520593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199943277586025618027457 3899957458189519213520593)
                      ·
                        rfl

theorem cell23_7595140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_7595140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595140 prefixEnd_7595140 := by exact prefixLift 7595140
  have htrace : WordTrace (prefixWord ++ tailWord_7595140) baseStart_7595140 baseEnd_7595140 := by
    simpa [prefixWord, tailWord_7595140, baseEnd_7595140] using wordTrace_append hprefix tailTrace_7595140
  have hstable : (prefixWord ++ tailWord_7595140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595140).length < 2 ^ (prefixWord ++ tailWord_7595140).sum := by decide
  have hdescent : baseEnd_7595140 < baseStart_7595140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595150 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_7595150 : Nat := 118140960795 + 7595150 * 2 ^ 59
def prefixEnd_7595150 : Nat := 4983230072969 + 3 ^ 40 * 7595150 * 2
def baseEnd_7595150 : Nat := 1299987530998688058131849

theorem tailTrace_7595150 : CollatzResearch.WordTrace tailWord_7595150 prefixEnd_7595150 1299987530998688058131849 := by
  unfold tailWord_7595150
  simp only [CollatzResearch.WordTrace]
  refine ⟨34627234804259521649231863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184678585622717448795903269 34627234804259521649231863)
  ·
    refine ⟨51940852206389282473847795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34627234804259521649231863 51940852206389282473847795)
    ·
      refine ⟨77911278309583923710771693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51940852206389282473847795 77911278309583923710771693)
      ·
        refine ⟨29216729366093971391539385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77911278309583923710771693 29216729366093971391539385)
        ·
          refine ⟨21912547024570478543654539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29216729366093971391539385 21912547024570478543654539)
          ·
            refine ⟨32868820536855717815481809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21912547024570478543654539 32868820536855717815481809)
            ·
              refine ⟨24651615402641788361611357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32868820536855717815481809 24651615402641788361611357)
              ·
                refine ⟨9244355775990670635604259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24651615402641788361611357 9244355775990670635604259)
                ·
                  refine ⟨13866533663986005953406389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9244355775990670635604259 13866533663986005953406389)
                  ·
                    refine ⟨1299987530998688058131849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13866533663986005953406389 1299987530998688058131849)
                    ·
                      rfl

theorem cell23_7595150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_7595150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595150 prefixEnd_7595150 := by exact prefixLift 7595150
  have htrace : WordTrace (prefixWord ++ tailWord_7595150) baseStart_7595150 baseEnd_7595150 := by
    simpa [prefixWord, tailWord_7595150, baseEnd_7595150] using wordTrace_append hprefix tailTrace_7595150
  have hstable : (prefixWord ++ tailWord_7595150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595150).length < 2 ^ (prefixWord ++ tailWord_7595150).sum := by decide
  have hdescent : baseEnd_7595150 < baseStart_7595150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595173 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7595173 : Nat := 118140960795 + 7595173 * 2 ^ 59
def prefixEnd_7595173 : Nat := 4983230072969 + 3 ^ 40 * 7595173 * 2
def baseEnd_7595173 : Nat := 3899974403051117584407941

theorem tailTrace_7595173 : CollatzResearch.WordTrace tailWord_7595173 prefixEnd_7595173 3899974403051117584407941 := by
  unfold tailWord_7595173
  simp only [CollatzResearch.WordTrace]
  refine ⟨277018717312992848121942173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184679144875328565414628115 277018717312992848121942173)
  ·
    refine ⟨103882018992372318045728315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277018717312992848121942173 103882018992372318045728315)
    ·
      refine ⟨155823028488558477068592473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103882018992372318045728315 155823028488558477068592473)
      ·
        refine ⟨116867271366418857801444355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155823028488558477068592473 116867271366418857801444355)
        ·
          refine ⟨175300907049628286702166533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116867271366418857801444355 175300907049628286702166533)
          ·
            refine ⟨32868920071805303756656225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175300907049628286702166533 32868920071805303756656225)
            ·
              refine ⟨24651690053853977817492169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32868920071805303756656225 24651690053853977817492169)
              ·
                refine ⟨18488767540390483363119127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24651690053853977817492169 18488767540390483363119127)
                ·
                  refine ⟨27733151310585725044678691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18488767540390483363119127 27733151310585725044678691)
                  ·
                    refine ⟨41599726965878587567018037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27733151310585725044678691 41599726965878587567018037)
                    ·
                      refine ⟨3899974403051117584407941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41599726965878587567018037 3899974403051117584407941)
                      ·
                        rfl

theorem cell23_7595173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7595173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595173 prefixEnd_7595173 := by exact prefixLift 7595173
  have htrace : WordTrace (prefixWord ++ tailWord_7595173) baseStart_7595173 baseEnd_7595173 := by
    simpa [prefixWord, tailWord_7595173, baseEnd_7595173] using wordTrace_append hprefix tailTrace_7595173
  have hstable : (prefixWord ++ tailWord_7595173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595173).length < 2 ^ (prefixWord ++ tailWord_7595173).sum := by decide
  have hdescent : baseEnd_7595173 < baseStart_7595173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595200 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_7595200 : Nat := 118140960795 + 7595200 * 2 ^ 59
def prefixEnd_7595200 : Nat := 4983230072969 + 3 ^ 40 * 7595200 * 2
def baseEnd_7595200 : Nat := 3899988267028788978770317

theorem tailTrace_7595200 : CollatzResearch.WordTrace tailWord_7595200 prefixEnd_7595200 3899988267028788978770317 := by
  unfold tailWord_7595200
  simp only [CollatzResearch.WordTrace]
  refine ⟨138509851041947515866587527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184679801389263354488783369 138509851041947515866587527)
  ·
    refine ⟨207764776562921273799881291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138509851041947515866587527 207764776562921273799881291)
    ·
      refine ⟨311647164844381910699821937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207764776562921273799881291 311647164844381910699821937)
      ·
        refine ⟨233735373633286433024866453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311647164844381910699821937 233735373633286433024866453)
        ·
          refine ⟨10956345639060301548040615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233735373633286433024866453 10956345639060301548040615)
          ·
            refine ⟨16434518458590452322060923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956345639060301548040615 16434518458590452322060923)
            ·
              refine ⟨24651777687885678483091385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16434518458590452322060923 24651777687885678483091385)
              ·
                refine ⟨18488833265914258862318539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24651777687885678483091385 18488833265914258862318539)
                ·
                  refine ⟨27733249898871388293477809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18488833265914258862318539 27733249898871388293477809)
                  ·
                    refine ⟨20799937424153541220108357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27733249898871388293477809 20799937424153541220108357)
                    ·
                      refine ⟨3899988267028788978770317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20799937424153541220108357 3899988267028788978770317)
                      ·
                        rfl

theorem cell23_7595200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_7595200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595200 prefixEnd_7595200 := by exact prefixLift 7595200
  have htrace : WordTrace (prefixWord ++ tailWord_7595200) baseStart_7595200 baseEnd_7595200 := by
    simpa [prefixWord, tailWord_7595200, baseEnd_7595200] using wordTrace_append hprefix tailTrace_7595200
  have hstable : (prefixWord ++ tailWord_7595200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595200).length < 2 ^ (prefixWord ++ tailWord_7595200).sum := by decide
  have hdescent : baseEnd_7595200 < baseStart_7595200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595204 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_7595204 : Nat := 118140960795 + 7595204 * 2 ^ 59
def prefixEnd_7595204 : Nat := 4983230072969 + 3 ^ 40 * 7595204 * 2
def baseEnd_7595204 : Nat := 3899990320951406963120299

theorem tailTrace_7595204 : CollatzResearch.WordTrace tailWord_7595204 prefixEnd_7595204 3899990320951406963120299 := by
  unfold tailWord_7595204
  simp only [CollatzResearch.WordTrace]
  refine ⟨138509923987940270208160333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184679898650587026944213777 138509923987940270208160333)
  ·
    refine ⟨51941221495477601328060125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138509923987940270208160333 51941221495477601328060125)
    ·
      refine ⟨19477958060804100498022547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51941221495477601328060125 19477958060804100498022547)
      ·
        refine ⟨29216937091206150747033821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19477958060804100498022547 29216937091206150747033821)
        ·
          refine ⟨10956351409202306530137683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29216937091206150747033821 10956351409202306530137683)
          ·
            refine ⟨16434527113803459795206525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956351409202306530137683 16434527113803459795206525)
            ·
              refine ⟨6162947667676297423202447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16434527113803459795206525 6162947667676297423202447)
              ·
                refine ⟨9244421501514446134803671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162947667676297423202447 9244421501514446134803671)
                ·
                  refine ⟨13866632252271669202205507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9244421501514446134803671 13866632252271669202205507)
                  ·
                    refine ⟨20799948378407503803308261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13866632252271669202205507 20799948378407503803308261)
                    ·
                      refine ⟨3899990320951406963120299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20799948378407503803308261 3899990320951406963120299)
                      ·
                        rfl

theorem cell23_7595204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_7595204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595204 prefixEnd_7595204 := by exact prefixLift 7595204
  have htrace : WordTrace (prefixWord ++ tailWord_7595204) baseStart_7595204 baseEnd_7595204 := by
    simpa [prefixWord, tailWord_7595204, baseEnd_7595204] using wordTrace_append hprefix tailTrace_7595204
  have hstable : (prefixWord ++ tailWord_7595204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595204).length < 2 ^ (prefixWord ++ tailWord_7595204).sum := by decide
  have hdescent : baseEnd_7595204 < baseStart_7595204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595216 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_7595216 : Nat := 118140960795 + 7595216 * 2 ^ 59
def prefixEnd_7595216 : Nat := 4983230072969 + 3 ^ 40 * 7595216 * 2
def baseEnd_7595216 : Nat := 3899996482719260916170243

theorem tailTrace_7595216 : CollatzResearch.WordTrace tailWord_7595216 prefixEnd_7595216 3899996482719260916170243 := by
  unfold tailWord_7595216
  simp only [CollatzResearch.WordTrace]
  refine ⟨138510142825918533232878751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184680190434558044310505001 138510142825918533232878751)
  ·
    refine ⟨207765214238877799849318127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138510142825918533232878751 207765214238877799849318127)
    ·
      refine ⟨311647821358316699773977191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207765214238877799849318127 311647821358316699773977191)
      ·
        refine ⟨467471732037475049660965787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311647821358316699773977191 467471732037475049660965787)
        ·
          refine ⟨701207598056212574491448681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467471732037475049660965787 701207598056212574491448681)
          ·
            refine ⟨525905698542159430868586511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701207598056212574491448681 525905698542159430868586511)
            ·
              refine ⟨788858547813239146302879767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525905698542159430868586511 788858547813239146302879767)
              ·
                refine ⟨1183287821719858719454319651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788858547813239146302879767 1183287821719858719454319651)
                ·
                  refine ⟨1774931732579788079181479477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183287821719858719454319651 1774931732579788079181479477)
                  ·
                    refine ⟨166399849929355132423263701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1774931732579788079181479477 166399849929355132423263701)
                    ·
                      refine ⟨3899996482719260916170243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166399849929355132423263701 3899996482719260916170243)
                      ·
                        rfl

theorem cell23_7595216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_7595216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595216 prefixEnd_7595216 := by exact prefixLift 7595216
  have htrace : WordTrace (prefixWord ++ tailWord_7595216) baseStart_7595216 baseEnd_7595216 := by
    simpa [prefixWord, tailWord_7595216, baseEnd_7595216] using wordTrace_append hprefix tailTrace_7595216
  have hstable : (prefixWord ++ tailWord_7595216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595216).length < 2 ^ (prefixWord ++ tailWord_7595216).sum := by decide
  have hdescent : baseEnd_7595216 < baseStart_7595216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595221 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7595221 : Nat := 118140960795 + 7595221 * 2 ^ 59
def prefixEnd_7595221 : Nat := 4983230072969 + 3 ^ 40 * 7595221 * 2
def baseEnd_7595221 : Nat := 3899999050122533396607721

theorem tailTrace_7595221 : CollatzResearch.WordTrace tailWord_7595221 prefixEnd_7595221 3899999050122533396607721 := by
  unfold tailWord_7595221
  simp only [CollatzResearch.WordTrace]
  refine ⟨277020468016818952319689517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184680312011212634879793011 277020468016818952319689517)
  ·
    refine ⟨103882675506307107119883569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277020468016818952319689517 103882675506307107119883569)
    ·
      refine ⟨77912006629730330339912677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103882675506307107119883569 77912006629730330339912677)
      ·
        refine ⟨14608501243074436938733627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77912006629730330339912677 14608501243074436938733627)
        ·
          refine ⟨21912751864611655408100441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14608501243074436938733627 21912751864611655408100441)
          ·
            refine ⟨16434563898458741556075331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21912751864611655408100441 16434563898458741556075331)
            ·
              refine ⟨24651845847688112334112997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16434563898458741556075331 24651845847688112334112997)
              ·
                refine ⟨4622221096441521062646187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24651845847688112334112997 4622221096441521062646187)
                ·
                  refine ⟨6933331644662281593969281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622221096441521062646187 6933331644662281593969281)
                  ·
                    refine ⟨5199998733496711195476961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6933331644662281593969281 5199998733496711195476961)
                    ·
                      refine ⟨3899999050122533396607721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5199998733496711195476961 3899999050122533396607721)
                      ·
                        rfl

theorem cell23_7595221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7595221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595221 prefixEnd_7595221 := by exact prefixLift 7595221
  have htrace : WordTrace (prefixWord ++ tailWord_7595221) baseStart_7595221 baseEnd_7595221 := by
    simpa [prefixWord, tailWord_7595221, baseEnd_7595221] using wordTrace_append hprefix tailTrace_7595221
  have hstable : (prefixWord ++ tailWord_7595221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595221).length < 2 ^ (prefixWord ++ tailWord_7595221).sum := by decide
  have hdescent : baseEnd_7595221 < baseStart_7595221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595237 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7595237 : Nat := 118140960795 + 7595237 * 2 ^ 59
def prefixEnd_7595237 : Nat := 4983230072969 + 3 ^ 40 * 7595237 * 2
def baseEnd_7595237 : Nat := 3900007265813005334007647

theorem tailTrace_7595237 : CollatzResearch.WordTrace tailWord_7595237 prefixEnd_7595237 3900007265813005334007647 := by
  unfold tailWord_7595237
  simp only [CollatzResearch.WordTrace]
  refine ⟨277021051584760987052271965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184680701056507324701514643 277021051584760987052271965)
  ·
    refine ⟨103882894344285370144601987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277021051584760987052271965 103882894344285370144601987)
    ·
      refine ⟨155824341516428055216902981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103882894344285370144601987 155824341516428055216902981)
      ·
        refine ⟨29217064034330260353169309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155824341516428055216902981 29217064034330260353169309)
        ·
          refine ⟨10956399012873847632438491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29217064034330260353169309 10956399012873847632438491)
          ·
            refine ⟨16434598519310771448657737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956399012873847632438491 16434598519310771448657737)
            ·
              refine ⟨12325948889483078586493303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16434598519310771448657737 12325948889483078586493303)
              ·
                refine ⟨18488923334224617879739955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12325948889483078586493303 18488923334224617879739955)
                ·
                  refine ⟨27733385001336926819609933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18488923334224617879739955 27733385001336926819609933)
                  ·
                    refine ⟨10400019375501347557353725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27733385001336926819609933 10400019375501347557353725)
                    ·
                      refine ⟨3900007265813005334007647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10400019375501347557353725 3900007265813005334007647)
                      ·
                        rfl

theorem cell23_7595237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7595237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595237 prefixEnd_7595237 := by exact prefixLift 7595237
  have htrace : WordTrace (prefixWord ++ tailWord_7595237) baseStart_7595237 baseEnd_7595237 := by
    simpa [prefixWord, tailWord_7595237, baseEnd_7595237] using wordTrace_append hprefix tailTrace_7595237
  have hstable : (prefixWord ++ tailWord_7595237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595237).length < 2 ^ (prefixWord ++ tailWord_7595237).sum := by decide
  have hdescent : baseEnd_7595237 < baseStart_7595237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595273 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_7595273 : Nat := 118140960795 + 7595273 * 2 ^ 59
def prefixEnd_7595273 : Nat := 4983230072969 + 3 ^ 40 * 7595273 * 2
def baseEnd_7595273 : Nat := 3900025751116567193157481

theorem tailTrace_7595273 : CollatzResearch.WordTrace tailWord_7595273 prefixEnd_7595273 3900025751116567193157481 := by
  unfold tailWord_7595273
  simp only [CollatzResearch.WordTrace]
  refine ⟨277022364612630565200582473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184681576408420376800388315 277022364612630565200582473)
  ·
    refine ⟨207766773459472923900436855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277022364612630565200582473 207766773459472923900436855)
    ·
      refine ⟨311650160189209385850655283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207766773459472923900436855 311650160189209385850655283)
      ·
        refine ⟨467475240283814078775982925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311650160189209385850655283 467475240283814078775982925)
        ·
          refine ⟨175303215106430279540993597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467475240283814078775982925 175303215106430279540993597)
          ·
            refine ⟨65738705664911354827872599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175303215106430279540993597 65738705664911354827872599)
            ·
              refine ⟨98608058497367032241808899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65738705664911354827872599 98608058497367032241808899)
              ·
                refine ⟨147912087746050548362713349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98608058497367032241808899 147912087746050548362713349)
                ·
                  refine ⟨27733516452384477818008753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147912087746050548362713349 27733516452384477818008753)
                  ·
                    refine ⟨20800137339288358363506565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27733516452384477818008753 20800137339288358363506565)
                    ·
                      refine ⟨3900025751116567193157481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20800137339288358363506565 3900025751116567193157481)
                      ·
                        rfl

theorem cell23_7595273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_7595273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595273 prefixEnd_7595273 := by exact prefixLift 7595273
  have htrace : WordTrace (prefixWord ++ tailWord_7595273) baseStart_7595273 baseEnd_7595273 := by
    simpa [prefixWord, tailWord_7595273, baseEnd_7595273] using wordTrace_append hprefix tailTrace_7595273
  have hstable : (prefixWord ++ tailWord_7595273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595273).length < 2 ^ (prefixWord ++ tailWord_7595273).sum := by decide
  have hdescent : baseEnd_7595273 < baseStart_7595273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595290 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_7595290 : Nat := 118140960795 + 7595290 * 2 ^ 59
def prefixEnd_7595290 : Nat := 4983230072969 + 3 ^ 40 * 7595290 * 2
def baseEnd_7595290 : Nat := 3900034480287693626644903

theorem tailTrace_7595290 : CollatzResearch.WordTrace tailWord_7595290 prefixEnd_7595290 3900034480287693626644903 := by
  unfold tailWord_7595290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69255746163392244275987831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184681989769045984735967549 69255746163392244275987831)
  ·
    refine ⟨103883619245088366413981747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69255746163392244275987831 103883619245088366413981747)
    ·
      refine ⟨155825428867632549620972621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103883619245088366413981747 155825428867632549620972621)
      ·
        refine ⟨58434535825362206107864733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155825428867632549620972621 58434535825362206107864733)
        ·
          refine ⟨21912950934510827290449275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58434535825362206107864733 21912950934510827290449275)
          ·
            refine ⟨32869426401766240935673913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21912950934510827290449275 32869426401766240935673913)
            ·
              refine ⟨24652069801324680701755435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32869426401766240935673913 24652069801324680701755435)
              ·
                refine ⟨36978104701987021052633153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24652069801324680701755435 36978104701987021052633153)
                ·
                  refine ⟨27733578526490265789474865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36978104701987021052633153 27733578526490265789474865)
                  ·
                    refine ⟨20800183894867699342106149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27733578526490265789474865 20800183894867699342106149)
                    ·
                      refine ⟨3900034480287693626644903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20800183894867699342106149 3900034480287693626644903)
                      ·
                        rfl

theorem cell23_7595290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_7595290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595290 prefixEnd_7595290 := by exact prefixLift 7595290
  have htrace : WordTrace (prefixWord ++ tailWord_7595290) baseStart_7595290 baseEnd_7595290 := by
    simpa [prefixWord, tailWord_7595290, baseEnd_7595290] using wordTrace_append hprefix tailTrace_7595290
  have hstable : (prefixWord ++ tailWord_7595290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595290).length < 2 ^ (prefixWord ++ tailWord_7595290).sum := by decide
  have hdescent : baseEnd_7595290 < baseStart_7595290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595317 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 5]
def baseStart_7595317 : Nat := 118140960795 + 7595317 * 2 ^ 59
def prefixEnd_7595317 : Nat := 4983230072969 + 3 ^ 40 * 7595317 * 2
def baseEnd_7595317 : Nat := 433338704918373891223031

theorem tailTrace_7595317 : CollatzResearch.WordTrace tailWord_7595317 prefixEnd_7595317 433338704918373891223031 := by
  unfold tailWord_7595317
  simp only [CollatzResearch.WordTrace]
  refine ⟨277023969424471160715184205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184682646282980773810122803 277023969424471160715184205)
  ·
    refine ⟨103883988534176685268194077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277023969424471160715184205 103883988534176685268194077)
    ·
      refine ⟨38956495700316256975572779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103883988534176685268194077 38956495700316256975572779)
      ·
        refine ⟨58434743550474385463359169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38956495700316256975572779 58434743550474385463359169)
        ·
          refine ⟨43826057662855789097519377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58434743550474385463359169 43826057662855789097519377)
          ·
            refine ⟨32869543247141841823139533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43826057662855789097519377 32869543247141841823139533)
            ·
              refine ⟨12326078717678190683677325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32869543247141841823139533 12326078717678190683677325)
              ·
                refine ⟨4622279519129321506378997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12326078717678190683677325 4622279519129321506378997)
                ·
                  refine ⟨433338704918373891223031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622279519129321506378997 433338704918373891223031)
                  ·
                    rfl

theorem cell23_7595317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_7595317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595317 prefixEnd_7595317 := by exact prefixLift 7595317
  have htrace : WordTrace (prefixWord ++ tailWord_7595317) baseStart_7595317 baseEnd_7595317 := by
    simpa [prefixWord, tailWord_7595317, baseEnd_7595317] using wordTrace_append hprefix tailTrace_7595317
  have hstable : (prefixWord ++ tailWord_7595317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595317).length < 2 ^ (prefixWord ++ tailWord_7595317).sum := by decide
  have hdescent : baseEnd_7595317 < baseStart_7595317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595320 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_7595320 : Nat := 118140960795 + 7595320 * 2 ^ 59
def prefixEnd_7595320 : Nat := 4983230072969 + 3 ^ 40 * 7595320 * 2
def baseEnd_7595320 : Nat := 3900049884707328509269765

theorem tailTrace_7595320 : CollatzResearch.WordTrace tailWord_7595320 prefixEnd_7595320 3900049884707328509269765 := by
  unfold tailWord_7595320
  simp only [CollatzResearch.WordTrace]
  refine ⟨138512039421730146113771707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184682719228973528151695609 138512039421730146113771707)
  ·
    refine ⟨207768059132595219170657561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138512039421730146113771707 207768059132595219170657561)
    ·
      refine ⟨155826044349446414377993171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207768059132595219170657561 155826044349446414377993171)
      ·
        refine ⟨233739066524169621566989757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155826044349446414377993171 233739066524169621566989757)
        ·
          refine ⟨87652149946563608087621159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233739066524169621566989757 87652149946563608087621159)
          ·
            refine ⟨131478224919845412131431739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87652149946563608087621159 131478224919845412131431739)
            ·
              refine ⟨197217337379768118197147609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131478224919845412131431739 197217337379768118197147609)
              ·
                refine ⟨147913003034826088647860707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197217337379768118197147609 147913003034826088647860707)
                ·
                  refine ⟨221869504552239132971791061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147913003034826088647860707 221869504552239132971791061)
                  ·
                    refine ⟨5200066512943104679026353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 221869504552239132971791061 5200066512943104679026353)
                    ·
                      refine ⟨3900049884707328509269765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200066512943104679026353 3900049884707328509269765)
                      ·
                        rfl

theorem cell23_7595320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_7595320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595320 prefixEnd_7595320 := by exact prefixLift 7595320
  have htrace : WordTrace (prefixWord ++ tailWord_7595320) baseStart_7595320 baseEnd_7595320 := by
    simpa [prefixWord, tailWord_7595320, baseEnd_7595320] using wordTrace_append hprefix tailTrace_7595320
  have hstable : (prefixWord ++ tailWord_7595320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595320).length < 2 ^ (prefixWord ++ tailWord_7595320).sum := by decide
  have hdescent : baseEnd_7595320 < baseStart_7595320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595340 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7595340 : Nat := 118140960795 + 7595340 * 2 ^ 59
def prefixEnd_7595340 : Nat := 4983230072969 + 3 ^ 40 * 7595340 * 2
def baseEnd_7595340 : Nat := 3900060154320418431019673

theorem tailTrace_7595340 : CollatzResearch.WordTrace tailWord_7595340 prefixEnd_7595340 3900060154320418431019673 := by
  unfold tailWord_7595340
  simp only [CollatzResearch.WordTrace]
  refine ⟨138512404151693917821635737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184683205535591890428847649 138512404151693917821635737)
  ·
    refine ⟨103884303113770438366226803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138512404151693917821635737 103884303113770438366226803)
    ·
      refine ⟨155826454670655657549340205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103884303113770438366226803 155826454670655657549340205)
      ·
        refine ⟨58434920501495871581002577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155826454670655657549340205 58434920501495871581002577)
        ·
          refine ⟨43826190376121903685751933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58434920501495871581002577 43826190376121903685751933)
          ·
            refine ⟨16434821391045713882156975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43826190376121903685751933 16434821391045713882156975)
            ·
              refine ⟨24652232086568570823235463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16434821391045713882156975 24652232086568570823235463)
              ·
                refine ⟨36978348129852856234853195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24652232086568570823235463 36978348129852856234853195)
                ·
                  refine ⟨55467522194779284352279793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36978348129852856234853195 55467522194779284352279793)
                  ·
                    refine ⟨41600641646084463264209845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55467522194779284352279793 41600641646084463264209845)
                    ·
                      refine ⟨3900060154320418431019673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41600641646084463264209845 3900060154320418431019673)
                      ·
                        rfl

theorem cell23_7595340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7595340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595340 prefixEnd_7595340 := by exact prefixLift 7595340
  have htrace : WordTrace (prefixWord ++ tailWord_7595340) baseStart_7595340 baseEnd_7595340 := by
    simpa [prefixWord, tailWord_7595340, baseEnd_7595340] using wordTrace_append hprefix tailTrace_7595340
  have hstable : (prefixWord ++ tailWord_7595340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595340).length < 2 ^ (prefixWord ++ tailWord_7595340).sum := by decide
  have hdescent : baseEnd_7595340 < baseStart_7595340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595417 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 3]
def baseStart_7595417 : Nat := 118140960795 + 7595417 * 2 ^ 59
def prefixEnd_7595417 : Nat := 4983230072969 + 3 ^ 40 * 7595417 * 2
def baseEnd_7595417 : Nat := 3900099692330814629756819

theorem tailTrace_7595417 : CollatzResearch.WordTrace tailWord_7595417 prefixEnd_7595417 3900099692330814629756819 := by
  unfold tailWord_7595417
  simp only [CollatzResearch.WordTrace]
  refine ⟨277027616724108877793824505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184685077816072585195883003 277027616724108877793824505)
  ·
    refine ⟨207770712543081658345368379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277027616724108877793824505 207770712543081658345368379)
    ·
      refine ⟨311656068814622487518052569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207770712543081658345368379 311656068814622487518052569)
      ·
        refine ⟨233742051610966865638539427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311656068814622487518052569 233742051610966865638539427)
        ·
          refine ⟨350613077416450298457809141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233742051610966865638539427 350613077416450298457809141)
          ·
            refine ⟨32869976007792215480419607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350613077416450298457809141 32869976007792215480419607)
            ·
              refine ⟨49304964011688323220629411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32869976007792215480419607 49304964011688323220629411)
              ·
                refine ⟨73957446017532484830944117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49304964011688323220629411 73957446017532484830944117)
                ·
                  refine ⟨6933510564143670452901011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73957446017532484830944117 6933510564143670452901011)
                  ·
                    refine ⟨10400265846215505679351517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6933510564143670452901011 10400265846215505679351517)
                    ·
                      refine ⟨3900099692330814629756819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10400265846215505679351517 3900099692330814629756819)
                      ·
                        rfl

theorem cell23_7595417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_7595417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595417 prefixEnd_7595417 := by exact prefixLift 7595417
  have htrace : WordTrace (prefixWord ++ tailWord_7595417) baseStart_7595417 baseEnd_7595417 := by
    simpa [prefixWord, tailWord_7595417, baseEnd_7595417] using wordTrace_append hprefix tailTrace_7595417
  have hstable : (prefixWord ++ tailWord_7595417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595417).length < 2 ^ (prefixWord ++ tailWord_7595417).sum := by decide
  have hdescent : baseEnd_7595417 < baseStart_7595417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595427 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 5, 2]
def baseStart_7595427 : Nat := 118140960795 + 7595427 * 2 ^ 59
def prefixEnd_7595427 : Nat := 4983230072969 + 3 ^ 40 * 7595427 * 2
def baseEnd_7595427 : Nat := 3900104827137359590631773

theorem tailTrace_7595427 : CollatzResearch.WordTrace tailWord_7595427 prefixEnd_7595427 3900104827137359590631773 := by
  unfold tailWord_7595427
  simp only [CollatzResearch.WordTrace]
  refine ⟨277027981454072649501688535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184685320969381766334459023 277027981454072649501688535)
  ·
    refine ⟨415541972181108974252532803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277027981454072649501688535 415541972181108974252532803)
    ·
      refine ⟨623312958271663461378799205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415541972181108974252532803 623312958271663461378799205)
      ·
        refine ⟨116871179675936899008524851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623312958271663461378799205 116871179675936899008524851)
        ·
          refine ⟨175306769513905348512787277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116871179675936899008524851 175306769513905348512787277)
          ·
            refine ⟨65740038567714505692295229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175306769513905348512787277 65740038567714505692295229)
            ·
              refine ⟨24652514462892939634610711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65740038567714505692295229 24652514462892939634610711)
              ·
                refine ⟨36978771694339409451916067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24652514462892939634610711 36978771694339409451916067)
                ·
                  refine ⟨55468157541509114177874101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36978771694339409451916067 55468157541509114177874101)
                  ·
                    refine ⟨5200139769516479454175697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55468157541509114177874101 5200139769516479454175697)
                    ·
                      refine ⟨3900104827137359590631773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200139769516479454175697 3900104827137359590631773)
                      ·
                        rfl

theorem cell23_7595427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_7595427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595427 prefixEnd_7595427 := by exact prefixLift 7595427
  have htrace : WordTrace (prefixWord ++ tailWord_7595427) baseStart_7595427 baseEnd_7595427 := by
    simpa [prefixWord, tailWord_7595427, baseEnd_7595427] using wordTrace_append hprefix tailTrace_7595427
  have hstable : (prefixWord ++ tailWord_7595427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595427).length < 2 ^ (prefixWord ++ tailWord_7595427).sum := by decide
  have hdescent : baseEnd_7595427 < baseStart_7595427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595440 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_7595440 : Nat := 118140960795 + 7595440 * 2 ^ 59
def prefixEnd_7595440 : Nat := 4983230072969 + 3 ^ 40 * 7595440 * 2
def baseEnd_7595440 : Nat := 3900111502385868039769213

theorem tailTrace_7595440 : CollatzResearch.WordTrace tailWord_7595440 prefixEnd_7595440 3900111502385868039769213 := by
  unfold tailWord_7595440
  simp only [CollatzResearch.WordTrace]
  refine ⟨138514227801512776360955887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184685637068683701814607849 138514227801512776360955887)
  ·
    refine ⟨207771341702269164541433831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138514227801512776360955887 207771341702269164541433831)
    ·
      refine ⟨311657012553403746812150747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207771341702269164541433831 311657012553403746812150747)
      ·
        refine ⟨467485518830105620218226121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311657012553403746812150747 467485518830105620218226121)
        ·
          refine ⟨350614139122579215163669591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467485518830105620218226121 350614139122579215163669591)
          ·
            refine ⟨525921208683868822745504387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350614139122579215163669591 525921208683868822745504387)
            ·
              refine ⟨788881813025803234118256581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525921208683868822745504387 788881813025803234118256581)
              ·
                refine ⟨147915339942338106397173109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788881813025803234118256581 147915339942338106397173109)
                ·
                  refine ⟨13867063119594197474734979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147915339942338106397173109 13867063119594197474734979)
                  ·
                    refine ⟨20800594679391296212102469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13867063119594197474734979 20800594679391296212102469)
                    ·
                      refine ⟨3900111502385868039769213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20800594679391296212102469 3900111502385868039769213)
                      ·
                        rfl

theorem cell23_7595440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_7595440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595440 prefixEnd_7595440 := by exact prefixLift 7595440
  have htrace : WordTrace (prefixWord ++ tailWord_7595440) baseStart_7595440 baseEnd_7595440 := by
    simpa [prefixWord, tailWord_7595440, baseEnd_7595440] using wordTrace_append hprefix tailTrace_7595440
  have hstable : (prefixWord ++ tailWord_7595440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595440).length < 2 ^ (prefixWord ++ tailWord_7595440).sum := by decide
  have hdescent : baseEnd_7595440 < baseStart_7595440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595467 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 2, 4]
def baseStart_7595467 : Nat := 118140960795 + 7595467 * 2 ^ 59
def prefixEnd_7595467 : Nat := 4983230072969 + 3 ^ 40 * 7595467 * 2
def baseEnd_7595467 : Nat := 1300041788787846478043863

theorem tailTrace_7595467 : CollatzResearch.WordTrace tailWord_7595467 prefixEnd_7595467 1300041788787846478043863 := by
  unfold tailWord_7595467
  simp only [CollatzResearch.WordTrace]
  refine ⟨277029440373927736333144655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184686293582618490888763103 277029440373927736333144655)
  ·
    refine ⟨415544160560891604499716983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277029440373927736333144655 415544160560891604499716983)
    ·
      refine ⟨623316240841337406749575475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415544160560891604499716983 623316240841337406749575475)
      ·
        refine ⟨934974361262006110124363213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623316240841337406749575475 934974361262006110124363213)
        ·
          refine ⟨350615385473252291296636205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 934974361262006110124363213 350615385473252291296636205)
          ·
            refine ⟨131480769552469609236238577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350615385473252291296636205 131480769552469609236238577)
            ·
              refine ⟨98610577164352206927178933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131480769552469609236238577 98610577164352206927178933)
              ·
                refine ⟨9244741609158019399423025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98610577164352206927178933 9244741609158019399423025)
                ·
                  refine ⟨6933556206868514549567269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9244741609158019399423025 6933556206868514549567269)
                  ·
                    refine ⟨1300041788787846478043863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933556206868514549567269 1300041788787846478043863)
                    ·
                      rfl

theorem cell23_7595467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 4].length) (baseStart_7595467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595467 prefixEnd_7595467 := by exact prefixLift 7595467
  have htrace : WordTrace (prefixWord ++ tailWord_7595467) baseStart_7595467 baseEnd_7595467 := by
    simpa [prefixWord, tailWord_7595467, baseEnd_7595467] using wordTrace_append hprefix tailTrace_7595467
  have hstable : (prefixWord ++ tailWord_7595467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595467).length < 2 ^ (prefixWord ++ tailWord_7595467).sum := by decide
  have hdescent : baseEnd_7595467 < baseStart_7595467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595518 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7595518 : Nat := 118140960795 + 7595518 * 2 ^ 59
def prefixEnd_7595518 : Nat := 4983230072969 + 3 ^ 40 * 7595518 * 2
def baseEnd_7595518 : Nat := 1300050517958972911531285

theorem tailTrace_7595518 : CollatzResearch.WordTrace tailWord_7595518 prefixEnd_7595518 1300050517958972911531285 := by
  unfold tailWord_7595518
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628912562092871505406401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184687533664495314695500805 34628912562092871505406401)
  ·
    refine ⟨25971684421569653629054801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34628912562092871505406401 25971684421569653629054801)
    ·
      refine ⟨19478763316177240221791101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25971684421569653629054801 19478763316177240221791101)
      ·
        refine ⟨7304536243566465083171663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19478763316177240221791101 7304536243566465083171663)
        ·
          refine ⟨10956804365349697624757495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304536243566465083171663 10956804365349697624757495)
          ·
            refine ⟨16435206548024546437136243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956804365349697624757495 16435206548024546437136243)
            ·
              refine ⟨24652809822036819655704365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16435206548024546437136243 24652809822036819655704365)
              ·
                refine ⟨9244803683263807370889137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24652809822036819655704365 9244803683263807370889137)
                ·
                  refine ⟨6933602762447855528166853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9244803683263807370889137 6933602762447855528166853)
                  ·
                    refine ⟨1300050517958972911531285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933602762447855528166853 1300050517958972911531285)
                    ·
                      rfl

theorem cell23_7595518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7595518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595518 prefixEnd_7595518 := by exact prefixLift 7595518
  have htrace : WordTrace (prefixWord ++ tailWord_7595518) baseStart_7595518 baseEnd_7595518 := by
    simpa [prefixWord, tailWord_7595518, baseEnd_7595518] using wordTrace_append hprefix tailTrace_7595518
  have hstable : (prefixWord ++ tailWord_7595518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595518).length < 2 ^ (prefixWord ++ tailWord_7595518).sum := by decide
  have hdescent : baseEnd_7595518 < baseStart_7595518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595577 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7595577 : Nat := 118140960795 + 7595577 * 2 ^ 59
def prefixEnd_7595577 : Nat := 4983230072969 + 3 ^ 40 * 7595577 * 2
def baseEnd_7595577 : Nat := 3900181849235534003756083

theorem tailTrace_7595577 : CollatzResearch.WordTrace tailWord_7595577 prefixEnd_7595577 3900181849235534003756083 := by
  unfold tailWord_7595577
  simp only [CollatzResearch.WordTrace]
  refine ⟨277033452403529225119648985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184688968269019483413099323 277033452403529225119648985)
  ·
    refine ⟨207775089302646918839736739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277033452403529225119648985 207775089302646918839736739)
    ·
      refine ⟨311662633953970378259605109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207775089302646918839736739 311662633953970378259605109)
      ·
        refine ⟨29218371933184722961837979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311662633953970378259605109 29218371933184722961837979)
        ·
          refine ⟨43827557899777084442756969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218371933184722961837979 43827557899777084442756969)
          ·
            refine ⟨32870668424832813332067727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43827557899777084442756969 32870668424832813332067727)
            ·
              refine ⟨49306002637249219998101591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32870668424832813332067727 49306002637249219998101591)
              ·
                refine ⟨73959003955873829997152387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49306002637249219998101591 73959003955873829997152387)
                ·
                  refine ⟨110938505933810744995728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73959003955873829997152387 110938505933810744995728581)
                  ·
                    refine ⟨20800969862589514686699109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110938505933810744995728581 20800969862589514686699109)
                    ·
                      refine ⟨3900181849235534003756083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20800969862589514686699109 3900181849235534003756083)
                      ·
                        rfl

theorem cell23_7595577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7595577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595577 prefixEnd_7595577 := by exact prefixLift 7595577
  have htrace : WordTrace (prefixWord ++ tailWord_7595577) baseStart_7595577 baseEnd_7595577 := by
    simpa [prefixWord, tailWord_7595577, baseEnd_7595577] using wordTrace_append hprefix tailTrace_7595577
  have hstable : (prefixWord ++ tailWord_7595577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595577).length < 2 ^ (prefixWord ++ tailWord_7595577).sum := by decide
  have hdescent : baseEnd_7595577 < baseStart_7595577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595617 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_7595617 : Nat := 118140960795 + 7595617 * 2 ^ 59
def prefixEnd_7595617 : Nat := 4983230072969 + 3 ^ 40 * 7595617 * 2
def baseEnd_7595617 : Nat := 1300067462820571282418633

theorem tailTrace_7595617 : CollatzResearch.WordTrace tailWord_7595617 prefixEnd_7595617 1300067462820571282418633 := by
  unfold tailWord_7595617
  simp only [CollatzResearch.WordTrace]
  refine ⟨277034911323384311951105105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184689940882256207967403403 277034911323384311951105105)
  ·
    refine ⟨207776183492538233963328829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277034911323384311951105105 207776183492538233963328829)
    ·
      refine ⟨77916068809701837736248311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207776183492538233963328829 77916068809701837736248311)
      ·
        refine ⟨116874103214552756604372467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77916068809701837736248311 116874103214552756604372467)
        ·
          refine ⟨175311154821829134906558701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116874103214552756604372467 175311154821829134906558701)
          ·
            refine ⟨65741683058185925589959513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175311154821829134906558701 65741683058185925589959513)
            ·
              refine ⟨49306262293639444192469635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65741683058185925589959513 49306262293639444192469635)
              ·
                refine ⟨73959393440459166288704453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49306262293639444192469635 73959393440459166288704453)
                ·
                  refine ⟨13867386270086093679132085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73959393440459166288704453 13867386270086093679132085)
                  ·
                    refine ⟨1300067462820571282418633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13867386270086093679132085 1300067462820571282418633)
                    ·
                      rfl

theorem cell23_7595617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_7595617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595617 prefixEnd_7595617 := by exact prefixLift 7595617
  have htrace : WordTrace (prefixWord ++ tailWord_7595617) baseStart_7595617 baseEnd_7595617 := by
    simpa [prefixWord, tailWord_7595617, baseEnd_7595617] using wordTrace_append hprefix tailTrace_7595617
  have hstable : (prefixWord ++ tailWord_7595617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595617).length < 2 ^ (prefixWord ++ tailWord_7595617).sum := by decide
  have hdescent : baseEnd_7595617 < baseStart_7595617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595681 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_7595681 : Nat := 118140960795 + 7595681 * 2 ^ 59
def prefixEnd_7595681 : Nat := 4983230072969 + 3 ^ 40 * 7595681 * 2
def baseEnd_7595681 : Nat := 1300078417074533865618535

theorem tailTrace_7595681 : CollatzResearch.WordTrace tailWord_7595681 prefixEnd_7595681 1300078417074533865618535 := by
  unfold tailWord_7595681
  simp only [CollatzResearch.WordTrace]
  refine ⟨277037245595152450881434897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184691497063434967254289931 277037245595152450881434897)
  ·
    refine ⟨207777934196364338161076173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277037245595152450881434897 207777934196364338161076173)
    ·
      refine ⟨77916725323636626810403565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207777934196364338161076173 77916725323636626810403565)
      ·
        refine ⟨29218771996363735053901337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77916725323636626810403565 29218771996363735053901337)
        ·
          refine ⟨21914078997272801290426003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29218771996363735053901337 21914078997272801290426003)
          ·
            refine ⟨32871118495909201935639005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21914078997272801290426003 32871118495909201935639005)
            ·
              refine ⟨12326669435965950725864627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32871118495909201935639005 12326669435965950725864627)
              ·
                refine ⟨18490004153948926088796941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12326669435965950725864627 18490004153948926088796941)
                ·
                  refine ⟨6933751557730847283298853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18490004153948926088796941 6933751557730847283298853)
                  ·
                    refine ⟨1300078417074533865618535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933751557730847283298853 1300078417074533865618535)
                    ·
                      rfl

theorem cell23_7595681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_7595681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595681 prefixEnd_7595681 := by exact prefixLift 7595681
  have htrace : WordTrace (prefixWord ++ tailWord_7595681) baseStart_7595681 baseEnd_7595681 := by
    simpa [prefixWord, tailWord_7595681, baseEnd_7595681] using wordTrace_append hprefix tailTrace_7595681
  have hstable : (prefixWord ++ tailWord_7595681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595681).length < 2 ^ (prefixWord ++ tailWord_7595681).sum := by decide
  have hdescent : baseEnd_7595681 < baseStart_7595681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595732 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_7595732 : Nat := 118140960795 + 7595732 * 2 ^ 59
def prefixEnd_7595732 : Nat := 4983230072969 + 3 ^ 40 * 7595732 * 2
def baseEnd_7595732 : Nat := 1300087146245660299105957

theorem tailTrace_7595732 : CollatzResearch.WordTrace tailWord_7595732 prefixEnd_7595732 1300087146245660299105957 := by
  unfold tailWord_7595732
  simp only [CollatzResearch.WordTrace]
  refine ⟨138519552858983843295770725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184692737145311791061027633 138519552858983843295770725)
  ·
    refine ⟨25972416161059470617957011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138519552858983843295770725 25972416161059470617957011)
    ·
      refine ⟨38958624241589205926935517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25972416161059470617957011 38958624241589205926935517)
      ·
        refine ⟨14609484090595952222600819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38958624241589205926935517 14609484090595952222600819)
        ·
          refine ⟨21914226135893928333901229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14609484090595952222600819 21914226135893928333901229)
          ·
            refine ⟨8217834800960223125212961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21914226135893928333901229 8217834800960223125212961)
            ·
              refine ⟨6163376100720167343909721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217834800960223125212961 6163376100720167343909721)
              ·
                refine ⟨4622532075540125507932291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6163376100720167343909721 4622532075540125507932291)
                ·
                  refine ⟨6933798113310188261898437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622532075540125507932291 6933798113310188261898437)
                  ·
                    refine ⟨1300087146245660299105957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933798113310188261898437 1300087146245660299105957)
                    ·
                      rfl

theorem cell23_7595732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_7595732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595732 prefixEnd_7595732 := by exact prefixLift 7595732
  have htrace : WordTrace (prefixWord ++ tailWord_7595732) baseStart_7595732 baseEnd_7595732 := by
    simpa [prefixWord, tailWord_7595732, baseEnd_7595732] using wordTrace_append hprefix tailTrace_7595732
  have hstable : (prefixWord ++ tailWord_7595732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595732).length < 2 ^ (prefixWord ++ tailWord_7595732).sum := by decide
  have hdescent : baseEnd_7595732 < baseStart_7595732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595744 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_7595744 : Nat := 118140960795 + 7595744 * 2 ^ 59
def prefixEnd_7595744 : Nat := 4983230072969 + 3 ^ 40 * 7595744 * 2
def baseEnd_7595744 : Nat := 3900267600504834850367815

theorem tailTrace_7595744 : CollatzResearch.WordTrace tailWord_7595744 prefixEnd_7595744 3900267600504834850367815 := by
  unfold tailWord_7595744
  simp only [CollatzResearch.WordTrace]
  refine ⟨138519771696962106320489143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184693028929282808427318857 138519771696962106320489143)
  ·
    refine ⟨207779657545443159480733715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138519771696962106320489143 207779657545443159480733715)
    ·
      refine ⟨311669486318164739221100573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207779657545443159480733715 311669486318164739221100573)
      ·
        refine ⟨116876057369311777207912715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311669486318164739221100573 116876057369311777207912715)
        ·
          refine ⟨175314086053967665811869073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116876057369311777207912715 175314086053967665811869073)
          ·
            refine ⟨131485564540475749358901805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175314086053967665811869073 131485564540475749358901805)
            ·
              refine ⟨49307086702678406009588177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131485564540475749358901805 49307086702678406009588177)
              ·
                refine ⟨36980315027008804507191133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49307086702678406009588177 36980315027008804507191133)
                ·
                  refine ⟨13867618135128301690196675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36980315027008804507191133 13867618135128301690196675)
                  ·
                    refine ⟨20801427202692452535295013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13867618135128301690196675 20801427202692452535295013)
                    ·
                      refine ⟨3900267600504834850367815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20801427202692452535295013 3900267600504834850367815)
                      ·
                        rfl

theorem cell23_7595744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_7595744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595744 prefixEnd_7595744 := by exact prefixLift 7595744
  have htrace : WordTrace (prefixWord ++ tailWord_7595744) baseStart_7595744 baseEnd_7595744 := by
    simpa [prefixWord, tailWord_7595744, baseEnd_7595744] using wordTrace_append hprefix tailTrace_7595744
  have hstable : (prefixWord ++ tailWord_7595744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595744).length < 2 ^ (prefixWord ++ tailWord_7595744).sum := by decide
  have hdescent : baseEnd_7595744 < baseStart_7595744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595754 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_7595754 : Nat := 118140960795 + 7595754 * 2 ^ 59
def prefixEnd_7595754 : Nat := 4983230072969 + 3 ^ 40 * 7595754 * 2
def baseEnd_7595754 : Nat := 1300090911770459937080923

theorem tailTrace_7595754 : CollatzResearch.WordTrace tailWord_7595754 prefixEnd_7595754 1300090911770459937080923 := by
  unfold tailWord_7595754
  simp only [CollatzResearch.WordTrace]
  refine ⟨69259977030971996087210579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184693272082591989565894877 69259977030971996087210579)
  ·
    refine ⟨103889965546457994130815869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69259977030971996087210579 103889965546457994130815869)
    ·
      refine ⟨38958737079921747799055951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103889965546457994130815869 38958737079921747799055951)
      ·
        refine ⟨58438105619882621698583927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38958737079921747799055951 58438105619882621698583927)
        ·
          refine ⟨87657158429823932547875891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58438105619882621698583927 87657158429823932547875891)
          ·
            refine ⟨131485737644735898821813837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87657158429823932547875891 131485737644735898821813837)
            ·
              refine ⟨49307151616775962058180189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131485737644735898821813837 49307151616775962058180189)
              ·
                refine ⟨18490181856290985771817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49307151616775962058180189 18490181856290985771817571)
                ·
                  refine ⟨27735272784436478657726357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18490181856290985771817571 27735272784436478657726357)
                  ·
                    refine ⟨1300090911770459937080923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27735272784436478657726357 1300090911770459937080923)
                    ·
                      rfl

theorem cell23_7595754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_7595754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595754 prefixEnd_7595754 := by exact prefixLift 7595754
  have htrace : WordTrace (prefixWord ++ tailWord_7595754) baseStart_7595754 baseEnd_7595754 := by
    simpa [prefixWord, tailWord_7595754, baseEnd_7595754] using wordTrace_append hprefix tailTrace_7595754
  have hstable : (prefixWord ++ tailWord_7595754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595754).length < 2 ^ (prefixWord ++ tailWord_7595754).sum := by decide
  have hdescent : baseEnd_7595754 < baseStart_7595754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595767 : List Nat := [1, 1, 3, 1, 1, 1, 4, 11]
def baseStart_7595767 : Nat := 118140960795 + 7595767 * 2 ^ 59
def prefixEnd_7595767 : Nat := 4983230072969 + 3 ^ 40 * 7595767 * 2
def baseEnd_7595767 : Nat := 144454792983699565199267

theorem tailTrace_7595767 : CollatzResearch.WordTrace tailWord_7595767 prefixEnd_7595767 144454792983699565199267 := by
  unfold tailWord_7595767
  simp only [CollatzResearch.WordTrace]
  refine ⟨277040382272840887569065555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184693588181893925046043703 277040382272840887569065555)
  ·
    refine ⟨415560573409261331353598333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277040382272840887569065555 415560573409261331353598333)
    ·
      refine ⟨155835215028472999257599375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415560573409261331353598333 155835215028472999257599375)
      ·
        refine ⟨233752822542709498886399063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155835215028472999257599375 233752822542709498886399063)
        ·
          refine ⟨350629233814064248329598595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233752822542709498886399063 350629233814064248329598595)
          ·
            refine ⟨525943850721096372494397893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350629233814064248329598595 525943850721096372494397893)
            ·
              refine ⟨98614472010205569842699605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525943850721096372494397893 98614472010205569842699605)
              ·
                refine ⟨144454792983699565199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 98614472010205569842699605 144454792983699565199267)
                ·
                  rfl

theorem cell23_7595767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 11].length) (baseStart_7595767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595767 prefixEnd_7595767 := by exact prefixLift 7595767
  have htrace : WordTrace (prefixWord ++ tailWord_7595767) baseStart_7595767 baseEnd_7595767 := by
    simpa [prefixWord, tailWord_7595767, baseEnd_7595767] using wordTrace_append hprefix tailTrace_7595767
  have hstable : (prefixWord ++ tailWord_7595767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595767).length < 2 ^ (prefixWord ++ tailWord_7595767).sum := by decide
  have hdescent : baseEnd_7595767 < baseStart_7595767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595778 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_7595778 : Nat := 118140960795 + 7595778 * 2 ^ 59
def prefixEnd_7595778 : Nat := 4983230072969 + 3 ^ 40 * 7595778 * 2
def baseEnd_7595778 : Nat := 3900285058847087717342659

theorem tailTrace_7595778 : CollatzResearch.WordTrace tailWord_7595778 prefixEnd_7595778 3900285058847087717342659 := by
  unfold tailWord_7595778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69260195868950259111928997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184693855650534024298477325 69260195868950259111928997)
  ·
    refine ⟨12986286725428173583486687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69260195868950259111928997 12986286725428173583486687)
    ·
      refine ⟨19479430088142260375230031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986286725428173583486687 19479430088142260375230031)
      ·
        refine ⟨29219145132213390562845047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19479430088142260375230031 29219145132213390562845047)
        ·
          refine ⟨43828717698320085844267571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29219145132213390562845047 43828717698320085844267571)
          ·
            refine ⟨65743076547480128766401357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43828717698320085844267571 65743076547480128766401357)
            ·
              refine ⟨24653653705305048287400509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65743076547480128766401357 24653653705305048287400509)
              ·
                refine ⟨9245120139489393107775191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24653653705305048287400509 9245120139489393107775191)
                ·
                  refine ⟨13867680209234089661662787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9245120139489393107775191 13867680209234089661662787)
                  ·
                    refine ⟨20801520313851134492494181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13867680209234089661662787 20801520313851134492494181)
                    ·
                      refine ⟨3900285058847087717342659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20801520313851134492494181 3900285058847087717342659)
                      ·
                        rfl

theorem cell23_7595778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_7595778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595778 prefixEnd_7595778 := by exact prefixLift 7595778
  have htrace : WordTrace (prefixWord ++ tailWord_7595778) baseStart_7595778 baseEnd_7595778 := by
    simpa [prefixWord, tailWord_7595778, baseEnd_7595778] using wordTrace_append hprefix tailTrace_7595778
  have hstable : (prefixWord ++ tailWord_7595778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595778).length < 2 ^ (prefixWord ++ tailWord_7595778).sum := by decide
  have hdescent : baseEnd_7595778 < baseStart_7595778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595811 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3]
def baseStart_7595811 : Nat := 118140960795 + 7595811 * 2 ^ 59
def prefixEnd_7595811 : Nat := 4983230072969 + 3 ^ 40 * 7595811 * 2
def baseEnd_7595811 : Nat := 3900302003708686088230007

theorem tailTrace_7595811 : CollatzResearch.WordTrace tailWord_7595811 prefixEnd_7595811 3900302003708686088230007 := by
  unfold tailWord_7595811
  simp only [CollatzResearch.WordTrace]
  refine ⟨277041987084681483083667287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184694658056454322055778191 277041987084681483083667287)
  ·
    refine ⟨415562980627022224625500931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277041987084681483083667287 415562980627022224625500931)
    ·
      refine ⟨623344470940533336938251397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415562980627022224625500931 623344470940533336938251397)
      ·
        refine ⟨116877088301350000675922137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623344470940533336938251397 116877088301350000675922137)
        ·
          refine ⟨87657816226012500506941603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116877088301350000675922137 87657816226012500506941603)
          ·
            refine ⟨131486724339018750760412405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87657816226012500506941603 131486724339018750760412405)
            ·
              refine ⟨12326880406783007883788663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131486724339018750760412405 12326880406783007883788663)
              ·
                refine ⟨18490320610174511825682995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12326880406783007883788663 18490320610174511825682995)
                ·
                  refine ⟨27735480915261767738524493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18490320610174511825682995 27735480915261767738524493)
                  ·
                    refine ⟨10400805343223162901946685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27735480915261767738524493 10400805343223162901946685)
                    ·
                      refine ⟨3900302003708686088230007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10400805343223162901946685 3900302003708686088230007)
                      ·
                        rfl

theorem cell23_7595811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_7595811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595811 prefixEnd_7595811 := by exact prefixLift 7595811
  have htrace : WordTrace (prefixWord ++ tailWord_7595811) baseStart_7595811 baseEnd_7595811 := by
    simpa [prefixWord, tailWord_7595811, baseEnd_7595811] using wordTrace_append hprefix tailTrace_7595811
  have hstable : (prefixWord ++ tailWord_7595811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595811).length < 2 ^ (prefixWord ++ tailWord_7595811).sum := by decide
  have hdescent : baseEnd_7595811 < baseStart_7595811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595829 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_7595829 : Nat := 118140960795 + 7595829 * 2 ^ 59
def prefixEnd_7595829 : Nat := 4983230072969 + 3 ^ 40 * 7595829 * 2
def baseEnd_7595829 : Nat := 3900311246360467017804925

theorem tailTrace_7595829 : CollatzResearch.WordTrace tailWord_7595829 prefixEnd_7595829 3900311246360467017804925 := by
  unfold tailWord_7595829
  simp only [CollatzResearch.WordTrace]
  refine ⟨277042643598616272157822541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184695095732410848105215027 277042643598616272157822541)
  ·
    refine ⟨103890991349481102059183453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277042643598616272157822541 103890991349481102059183453)
    ·
      refine ⟨38959121756055413272193795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103890991349481102059183453 38959121756055413272193795)
      ·
        refine ⟨58438682634083119908290693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38959121756055413272193795 58438682634083119908290693)
        ·
          refine ⟨10957252993890584982804505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58438682634083119908290693 10957252993890584982804505)
          ·
            refine ⟨8217939745417938737103379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10957252993890584982804505 8217939745417938737103379)
            ·
              refine ⟨12326909618126908105655069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8217939745417938737103379 12326909618126908105655069)
              ·
                refine ⟨4622591106797590539620651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12326909618126908105655069 4622591106797590539620651)
                ·
                  refine ⟨6933886660196385809430977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622591106797590539620651 6933886660196385809430977)
                  ·
                    refine ⟨5200414995147289357073233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6933886660196385809430977 5200414995147289357073233)
                    ·
                      refine ⟨3900311246360467017804925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200414995147289357073233 3900311246360467017804925)
                      ·
                        rfl

theorem cell23_7595829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_7595829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595829 prefixEnd_7595829 := by exact prefixLift 7595829
  have htrace : WordTrace (prefixWord ++ tailWord_7595829) baseStart_7595829 baseEnd_7595829 := by
    simpa [prefixWord, tailWord_7595829, baseEnd_7595829] using wordTrace_append hprefix tailTrace_7595829
  have hstable : (prefixWord ++ tailWord_7595829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595829).length < 2 ^ (prefixWord ++ tailWord_7595829).sum := by decide
  have hdescent : baseEnd_7595829 < baseStart_7595829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595891 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 5]
def baseStart_7595891 : Nat := 118140960795 + 7595891 * 2 ^ 59
def prefixEnd_7595891 : Nat := 4983230072969 + 3 ^ 40 * 7595891 * 2
def baseEnd_7595891 : Nat := 433371453573449530581071

theorem tailTrace_7595891 : CollatzResearch.WordTrace tailWord_7595891 prefixEnd_7595891 433371453573449530581071 := by
  unfold tailWord_7595891
  simp only [CollatzResearch.WordTrace]
  refine ⟨277044904924391656746579527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184696603282927771164386351 277044904924391656746579527)
  ·
    refine ⟨415567357386587485119869291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277044904924391656746579527 415567357386587485119869291)
    ·
      refine ⟨623351036079881227679803937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415567357386587485119869291 623351036079881227679803937)
      ·
        refine ⟨467513277059910920759852953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623351036079881227679803937 467513277059910920759852953)
        ·
          refine ⟨350634957794933190569889715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467513277059910920759852953 350634957794933190569889715)
          ·
            refine ⟨525952436692399785854834573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350634957794933190569889715 525952436692399785854834573)
            ·
              refine ⟨197232163759649919695562965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525952436692399785854834573 197232163759649919695562965)
              ·
                refine ⟨4622628838116794992864757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197232163759649919695562965 4622628838116794992864757)
                ·
                  refine ⟨433371453573449530581071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622628838116794992864757 433371453573449530581071)
                  ·
                    rfl

theorem cell23_7595891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 5].length) (baseStart_7595891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595891 prefixEnd_7595891 := by exact prefixLift 7595891
  have htrace : WordTrace (prefixWord ++ tailWord_7595891) baseStart_7595891 baseEnd_7595891 := by
    simpa [prefixWord, tailWord_7595891, baseEnd_7595891] using wordTrace_append hprefix tailTrace_7595891
  have hstable : (prefixWord ++ tailWord_7595891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595891).length < 2 ^ (prefixWord ++ tailWord_7595891).sum := by decide
  have hdescent : baseEnd_7595891 < baseStart_7595891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595901 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_7595901 : Nat := 118140960795 + 7595901 * 2 ^ 59
def prefixEnd_7595901 : Nat := 4983230072969 + 3 ^ 40 * 7595901 * 2
def baseEnd_7595901 : Nat := 3900348216967590736104593

theorem tailTrace_7595901 : CollatzResearch.WordTrace tailWord_7595901 prefixEnd_7595901 3900348216967590736104593 := by
  unfold tailWord_7595901
  simp only [CollatzResearch.WordTrace]
  refine ⟨277045269654355428454443557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184696846436236952302962371 277045269654355428454443557)
  ·
    refine ⟨51945988060191642835208167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277045269654355428454443557 51945988060191642835208167)
    ·
      refine ⟨77918982090287464252812251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51945988060191642835208167 77918982090287464252812251)
      ·
        refine ⟨116878473135431196379218377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77918982090287464252812251 116878473135431196379218377)
        ·
          refine ⟨87658854851573397284413783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116878473135431196379218377 87658854851573397284413783)
          ·
            refine ⟨131488282277360095926620675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87658854851573397284413783 131488282277360095926620675)
            ·
              refine ⟨197232423416040143889931013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131488282277360095926620675 197232423416040143889931013)
              ·
                refine ⟨36981079390507526979362065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197232423416040143889931013 36981079390507526979362065)
                ·
                  refine ⟨27735809542880645234521549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36981079390507526979362065 27735809542880645234521549)
                  ·
                    refine ⟨10400928578580241962945581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27735809542880645234521549 10400928578580241962945581)
                    ·
                      refine ⟨3900348216967590736104593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10400928578580241962945581 3900348216967590736104593)
                      ·
                        rfl

theorem cell23_7595901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_7595901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595901 prefixEnd_7595901 := by exact prefixLift 7595901
  have htrace : WordTrace (prefixWord ++ tailWord_7595901) baseStart_7595901 baseEnd_7595901 := by
    simpa [prefixWord, tailWord_7595901, baseEnd_7595901] using wordTrace_append hprefix tailTrace_7595901
  have hstable : (prefixWord ++ tailWord_7595901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595901).length < 2 ^ (prefixWord ++ tailWord_7595901).sum := by decide
  have hdescent : baseEnd_7595901 < baseStart_7595901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595938 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7595938 : Nat := 118140960795 + 7595938 * 2 ^ 59
def prefixEnd_7595938 : Nat := 4983230072969 + 3 ^ 40 * 7595938 * 2
def baseEnd_7595938 : Nat := 1300122405250602363780641

theorem tailTrace_7595938 : CollatzResearch.WordTrace tailWord_7595938 prefixEnd_7595938 1300122405250602363780641 := by
  unfold tailWord_7595938
  simp only [CollatzResearch.WordTrace]
  refine ⟨69261654788805345943385117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184697746103480922515693645 69261654788805345943385117)
  ·
    refine ⟨25973120545802004728769419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69261654788805345943385117 25973120545802004728769419)
    ·
      refine ⟨38959680818703007093154129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25973120545802004728769419 38959680818703007093154129)
      ·
        refine ⟨29219760614027255319865597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38959680818703007093154129 29219760614027255319865597)
        ·
          refine ⟨10957410230260220744949599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29219760614027255319865597 10957410230260220744949599)
          ·
            refine ⟨16436115345390331117424399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957410230260220744949599 16436115345390331117424399)
            ·
              refine ⟨24654173018085496676136599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16436115345390331117424399 24654173018085496676136599)
              ·
                refine ⟨36981259527128245014204899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24654173018085496676136599 36981259527128245014204899)
                ·
                  refine ⟨55471889290692367521307349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36981259527128245014204899 55471889290692367521307349)
                  ·
                    refine ⟨1300122405250602363780641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55471889290692367521307349 1300122405250602363780641)
                    ·
                      rfl

theorem cell23_7595938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7595938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595938 prefixEnd_7595938 := by exact prefixLift 7595938
  have htrace : WordTrace (prefixWord ++ tailWord_7595938) baseStart_7595938 baseEnd_7595938 := by
    simpa [prefixWord, tailWord_7595938, baseEnd_7595938] using wordTrace_append hprefix tailTrace_7595938
  have hstable : (prefixWord ++ tailWord_7595938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595938).length < 2 ^ (prefixWord ++ tailWord_7595938).sum := by decide
  have hdescent : baseEnd_7595938 < baseStart_7595938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595951 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 5, 4]
def baseStart_7595951 : Nat := 118140960795 + 7595951 * 2 ^ 59
def prefixEnd_7595951 : Nat := 4983230072969 + 3 ^ 40 * 7595951 * 2
def baseEnd_7595951 : Nat := 1300124630333438513493121

theorem tailTrace_7595951 : CollatzResearch.WordTrace tailWord_7595951 prefixEnd_7595951 1300124630333438513493121 := by
  unfold tailWord_7595951
  simp only [CollatzResearch.WordTrace]
  refine ⟨277047093304174286993763707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184698062202782857995842471 277047093304174286993763707)
  ·
    refine ⟨415570639956261430490645561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277047093304174286993763707 415570639956261430490645561)
    ·
      refine ⟨311677979967196072867984171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415570639956261430490645561 311677979967196072867984171)
      ·
        refine ⟨467516969950794109301976257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311677979967196072867984171 467516969950794109301976257)
        ·
          refine ⟨350637727463095581976482193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467516969950794109301976257 350637727463095581976482193)
          ·
            refine ⟨262978295597321686482361645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350637727463095581976482193 262978295597321686482361645)
            ·
              refine ⟨98616860848995632430885617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262978295597321686482361645 98616860848995632430885617)
              ·
                refine ⟨73962645636746724323164213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98616860848995632430885617 73962645636746724323164213)
                ·
                  refine ⟨6933998028445005405296645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73962645636746724323164213 6933998028445005405296645)
                  ·
                    refine ⟨1300124630333438513493121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933998028445005405296645 1300124630333438513493121)
                    ·
                      rfl

theorem cell23_7595951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_7595951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595951 prefixEnd_7595951 := by exact prefixLift 7595951
  have htrace : WordTrace (prefixWord ++ tailWord_7595951) baseStart_7595951 baseEnd_7595951 := by
    simpa [prefixWord, tailWord_7595951, baseEnd_7595951] using wordTrace_append hprefix tailTrace_7595951
  have hstable : (prefixWord ++ tailWord_7595951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595951).length < 2 ^ (prefixWord ++ tailWord_7595951).sum := by decide
  have hdescent : baseEnd_7595951 < baseStart_7595951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595968 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_7595968 : Nat := 118140960795 + 7595968 * 2 ^ 59
def prefixEnd_7595968 : Nat := 4983230072969 + 3 ^ 40 * 7595968 * 2
def baseEnd_7595968 : Nat := 1300127540057147324655595

theorem tailTrace_7595968 : CollatzResearch.WordTrace tailWord_7595968 prefixEnd_7595968 1300127540057147324655595 := by
  unfold tailWord_7595968
  simp only [CollatzResearch.WordTrace]
  refine ⟨138523856672556349448566279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184698475563408465931421705 138523856672556349448566279)
  ·
    refine ⟨207785785008834524172849419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138523856672556349448566279 207785785008834524172849419)
    ·
      refine ⟨311678677513251786259274129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207785785008834524172849419 311678677513251786259274129)
      ·
        refine ⟨233759008134938839694455597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311678677513251786259274129 233759008134938839694455597)
        ·
          refine ⟨87659628050602064885420849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233759008134938839694455597 87659628050602064885420849)
          ·
            refine ⟨65744721037951548664065637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87659628050602064885420849 65744721037951548664065637)
            ·
              refine ⟨12327135194615915374512307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65744721037951548664065637 12327135194615915374512307)
              ·
                refine ⟨18490702791923873061768461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327135194615915374512307 18490702791923873061768461)
                ·
                  refine ⟨6934013546971452398163173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18490702791923873061768461 6934013546971452398163173)
                  ·
                    refine ⟨1300127540057147324655595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934013546971452398163173 1300127540057147324655595)
                    ·
                      rfl

theorem cell23_7595968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_7595968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595968 prefixEnd_7595968 := by exact prefixLift 7595968
  have htrace : WordTrace (prefixWord ++ tailWord_7595968) baseStart_7595968 baseEnd_7595968 := by
    simpa [prefixWord, tailWord_7595968, baseEnd_7595968] using wordTrace_append hprefix tailTrace_7595968
  have hstable : (prefixWord ++ tailWord_7595968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595968).length < 2 ^ (prefixWord ++ tailWord_7595968).sum := by decide
  have hdescent : baseEnd_7595968 < baseStart_7595968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7595991 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_7595991 : Nat := 118140960795 + 7595991 * 2 ^ 59
def prefixEnd_7595991 : Nat := 4983230072969 + 3 ^ 40 * 7595991 * 2
def baseEnd_7595991 : Nat := 3900394430226495383979179

theorem tailTrace_7595991 : CollatzResearch.WordTrace tailWord_7595991 prefixEnd_7595991 3900394430226495383979179 := by
  unfold tailWord_7595991
  simp only [CollatzResearch.WordTrace]
  refine ⟨277048552224029373825219827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184699034816019582550146551 277048552224029373825219827)
  ·
    refine ⟨415572828336044060737829741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277048552224029373825219827 415572828336044060737829741)
    ·
      refine ⟨155839810626016522776686153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415572828336044060737829741 155839810626016522776686153)
      ·
        refine ⟨116879857969512392082514615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155839810626016522776686153 116879857969512392082514615)
        ·
          refine ⟨175319786954268588123771923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116879857969512392082514615 175319786954268588123771923)
          ·
            refine ⟨262979680431402882185657885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175319786954268588123771923 262979680431402882185657885)
            ·
              refine ⟨98617380161776080819621707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262979680431402882185657885 98617380161776080819621707)
              ·
                refine ⟨147926070242664121229432561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98617380161776080819621707 147926070242664121229432561)
                ·
                  refine ⟨110944552681998090922074421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147926070242664121229432561 110944552681998090922074421)
                  ·
                    refine ⟨10401051813937321023944477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110944552681998090922074421 10401051813937321023944477)
                    ·
                      refine ⟨3900394430226495383979179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401051813937321023944477 3900394430226495383979179)
                      ·
                        rfl

theorem cell23_7595991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_7595991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7595991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7595991 prefixEnd_7595991 := by exact prefixLift 7595991
  have htrace : WordTrace (prefixWord ++ tailWord_7595991) baseStart_7595991 baseEnd_7595991 := by
    simpa [prefixWord, tailWord_7595991, baseEnd_7595991] using wordTrace_append hprefix tailTrace_7595991
  have hstable : (prefixWord ++ tailWord_7595991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7595991).length < 2 ^ (prefixWord ++ tailWord_7595991).sum := by decide
  have hdescent : baseEnd_7595991 < baseStart_7595991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7595991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596025 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 3]
def baseStart_7596025 : Nat := 118140960795 + 7596025 * 2 ^ 59
def prefixEnd_7596025 : Nat := 4983230072969 + 3 ^ 40 * 7596025 * 2
def baseEnd_7596025 : Nat := 3900411888568748250954023

theorem tailTrace_7596025 : CollatzResearch.WordTrace tailWord_7596025 prefixEnd_7596025 3900411888568748250954023 := by
  unfold tailWord_7596025
  simp only [CollatzResearch.WordTrace]
  refine ⟨277049792305906197631957529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184699861537270798421305019 277049792305906197631957529)
  ·
    refine ⟨207787344229429648223968147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277049792305906197631957529 207787344229429648223968147)
    ·
      refine ⟨311681016344144472335952221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207787344229429648223968147 311681016344144472335952221)
      ·
        refine ⟨116880381129054177125982083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311681016344144472335952221 116880381129054177125982083)
        ·
          refine ⟨175320571693581265688973125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116880381129054177125982083 175320571693581265688973125)
          ·
            refine ⟨32872607192546487316682461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175320571693581265688973125 32872607192546487316682461)
            ·
              refine ⟨12327227697204932743755923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32872607192546487316682461 12327227697204932743755923)
              ·
                refine ⟨18490841545807399115633885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327227697204932743755923 18490841545807399115633885)
                ·
                  refine ⟨6934065579677774668362707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18490841545807399115633885 6934065579677774668362707)
                  ·
                    refine ⟨10401098369516662002544061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934065579677774668362707 10401098369516662002544061)
                    ·
                      refine ⟨3900411888568748250954023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401098369516662002544061 3900411888568748250954023)
                      ·
                        rfl

theorem cell23_7596025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_7596025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596025 prefixEnd_7596025 := by exact prefixLift 7596025
  have htrace : WordTrace (prefixWord ++ tailWord_7596025) baseStart_7596025 baseEnd_7596025 := by
    simpa [prefixWord, tailWord_7596025, baseEnd_7596025] using wordTrace_append hprefix tailTrace_7596025
  have hstable : (prefixWord ++ tailWord_7596025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596025).length < 2 ^ (prefixWord ++ tailWord_7596025).sum := by decide
  have hdescent : baseEnd_7596025 < baseStart_7596025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596051 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_7596051 : Nat := 118140960795 + 7596051 * 2 ^ 59
def prefixEnd_7596051 : Nat := 4983230072969 + 3 ^ 40 * 7596051 * 2
def baseEnd_7596051 : Nat := 3900425239065765149228903

theorem tailTrace_7596051 : CollatzResearch.WordTrace tailWord_7596051 prefixEnd_7596051 3900425239065765149228903 := by
  unfold tailWord_7596051
  simp only [CollatzResearch.WordTrace]
  refine ⟨277050740603812004072404007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184700493735874669381602671 277050740603812004072404007)
  ·
    refine ⟨415576110905718006108606011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277050740603812004072404007 415576110905718006108606011)
    ·
      refine ⟨623364166358577009162909017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415576110905718006108606011 623364166358577009162909017)
      ·
        refine ⟨467523124768932756872181763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623364166358577009162909017 467523124768932756872181763)
        ·
          refine ⟨701284687153399135308272645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467523124768932756872181763 701284687153399135308272645)
          ·
            refine ⟨131490878841262337870301121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 701284687153399135308272645 131490878841262337870301121)
            ·
              refine ⟨98618159130946753402725841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131490878841262337870301121 98618159130946753402725841)
              ·
                refine ⟨73963619348210065052044381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98618159130946753402725841 73963619348210065052044381)
                ·
                  refine ⟨27736357255578774394516643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73963619348210065052044381 27736357255578774394516643)
                  ·
                    refine ⟨41604535883368161591774965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27736357255578774394516643 41604535883368161591774965)
                    ·
                      refine ⟨3900425239065765149228903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41604535883368161591774965 3900425239065765149228903)
                      ·
                        rfl

theorem cell23_7596051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_7596051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596051 prefixEnd_7596051 := by exact prefixLift 7596051
  have htrace : WordTrace (prefixWord ++ tailWord_7596051) baseStart_7596051 baseEnd_7596051 := by
    simpa [prefixWord, tailWord_7596051, baseEnd_7596051] using wordTrace_append hprefix tailTrace_7596051
  have hstable : (prefixWord ++ tailWord_7596051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596051).length < 2 ^ (prefixWord ++ tailWord_7596051).sum := by decide
  have hdescent : baseEnd_7596051 < baseStart_7596051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596058 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_7596058 : Nat := 118140960795 + 7596058 * 2 ^ 59
def prefixEnd_7596058 : Nat := 4983230072969 + 3 ^ 40 * 7596058 * 2
def baseEnd_7596058 : Nat := 1300142944476782207280457

theorem tailTrace_7596058 : CollatzResearch.WordTrace tailWord_7596058 prefixEnd_7596058 1300142944476782207280457 := by
  unfold tailWord_7596058
  simp only [CollatzResearch.WordTrace]
  refine ⟨69262748978696661066977207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184700663943191096178605885 69262748978696661066977207)
  ·
    refine ⟨103894123468044991600465811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69262748978696661066977207 103894123468044991600465811)
    ·
      refine ⟨155841185202067487400698717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103894123468044991600465811 155841185202067487400698717)
      ·
        refine ⟨58440444450775307775262019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155841185202067487400698717 58440444450775307775262019)
        ·
          refine ⟨87660666676162961662893029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58440444450775307775262019 87660666676162961662893029)
          ·
            refine ⟨16436375001780555311792443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87660666676162961662893029 16436375001780555311792443)
            ·
              refine ⟨24654562502670832967688665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16436375001780555311792443 24654562502670832967688665)
              ·
                refine ⟨18490921877003124725766499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24654562502670832967688665 18490921877003124725766499)
                ·
                  refine ⟨27736382815504687088649749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18490921877003124725766499 27736382815504687088649749)
                  ·
                    refine ⟨1300142944476782207280457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27736382815504687088649749 1300142944476782207280457)
                    ·
                      rfl

theorem cell23_7596058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_7596058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596058 prefixEnd_7596058 := by exact prefixLift 7596058
  have htrace : WordTrace (prefixWord ++ tailWord_7596058) baseStart_7596058 baseEnd_7596058 := by
    simpa [prefixWord, tailWord_7596058, baseEnd_7596058] using wordTrace_append hprefix tailTrace_7596058
  have hstable : (prefixWord ++ tailWord_7596058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596058).length < 2 ^ (prefixWord ++ tailWord_7596058).sum := by decide
  have hdescent : baseEnd_7596058 < baseStart_7596058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596101 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_7596101 : Nat := 118140960795 + 7596101 * 2 ^ 59
def prefixEnd_7596101 : Nat := 4983230072969 + 3 ^ 40 * 7596101 * 2
def baseEnd_7596101 : Nat := 1300150304366163317867891

theorem tailTrace_7596101 : CollatzResearch.WordTrace tailWord_7596101 prefixEnd_7596101 1300150304366163317867891 := by
  unfold tailWord_7596101
  simp only [CollatzResearch.WordTrace]
  refine ⟨277052564253630862611724157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184701709502420575074482771 277052564253630862611724157)
  ·
    refine ⟨103894711595111573479396559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277052564253630862611724157 103894711595111573479396559)
    ·
      refine ⟨155842067392667360219094839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103894711595111573479396559 155842067392667360219094839)
      ·
        refine ⟨233763101089001040328642259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155842067392667360219094839 233763101089001040328642259)
        ·
          refine ⟨350644651633501560492963389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233763101089001040328642259 350644651633501560492963389)
          ·
            refine ⟨131491744362563085184861271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350644651633501560492963389 131491744362563085184861271)
            ·
              refine ⟨197237616543844627777291907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131491744362563085184861271 197237616543844627777291907)
              ·
                refine ⟨295856424815766941665937861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197237616543844627777291907 295856424815766941665937861)
                ·
                  refine ⟨55473079652956301562363349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295856424815766941665937861 55473079652956301562363349)
                  ·
                    refine ⟨1300150304366163317867891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55473079652956301562363349 1300150304366163317867891)
                    ·
                      rfl

theorem cell23_7596101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_7596101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596101 prefixEnd_7596101 := by exact prefixLift 7596101
  have htrace : WordTrace (prefixWord ++ tailWord_7596101) baseStart_7596101 baseEnd_7596101 := by
    simpa [prefixWord, tailWord_7596101, baseEnd_7596101] using wordTrace_append hprefix tailTrace_7596101
  have hstable : (prefixWord ++ tailWord_7596101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596101).length < 2 ^ (prefixWord ++ tailWord_7596101).sum := by decide
  have hdescent : baseEnd_7596101 < baseStart_7596101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596102 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7596102 : Nat := 118140960795 + 7596102 * 2 ^ 59
def prefixEnd_7596102 : Nat := 4983230072969 + 3 ^ 40 * 7596102 * 2
def baseEnd_7596102 : Nat := 3900451426579144449691169

theorem tailTrace_7596102 : CollatzResearch.WordTrace tailWord_7596102 prefixEnd_7596102 3900451426579144449691169 := by
  unfold tailWord_7596102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657893772707101243203455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184701733817751493188340373 8657893772707101243203455)
  ·
    refine ⟨12986840659060651864805183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8657893772707101243203455 12986840659060651864805183)
    ·
      refine ⟨19480260988590977797207775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986840659060651864805183 19480260988590977797207775)
      ·
        refine ⟨29220391482886466695811663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19480260988590977797207775 29220391482886466695811663)
        ·
          refine ⟨43830587224329700043717495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29220391482886466695811663 43830587224329700043717495)
          ·
            refine ⟨65745880836494550065576243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43830587224329700043717495 65745880836494550065576243)
            ·
              refine ⟨98618821254741825098364365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65745880836494550065576243 98618821254741825098364365)
              ·
                refine ⟨36982057970528184411886637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98618821254741825098364365 36982057970528184411886637)
                ·
                  refine ⟨13868271738948069154457489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36982057970528184411886637 13868271738948069154457489)
                  ·
                    refine ⟨10401203804211051865843117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13868271738948069154457489 10401203804211051865843117)
                    ·
                      refine ⟨3900451426579144449691169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401203804211051865843117 3900451426579144449691169)
                      ·
                        rfl

theorem cell23_7596102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7596102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596102 prefixEnd_7596102 := by exact prefixLift 7596102
  have htrace : WordTrace (prefixWord ++ tailWord_7596102) baseStart_7596102 baseEnd_7596102 := by
    simpa [prefixWord, tailWord_7596102, baseEnd_7596102] using wordTrace_append hprefix tailTrace_7596102
  have hstable : (prefixWord ++ tailWord_7596102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596102).length < 2 ^ (prefixWord ++ tailWord_7596102).sum := by decide
  have hdescent : baseEnd_7596102 < baseStart_7596102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596111 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_7596111 : Nat := 118140960795 + 7596111 * 2 ^ 59
def prefixEnd_7596111 : Nat := 4983230072969 + 3 ^ 40 * 7596111 * 2
def baseEnd_7596111 : Nat := 3900456047905034914478627

theorem tailTrace_7596111 : CollatzResearch.WordTrace tailWord_7596111 prefixEnd_7596111 3900456047905034914478627 := by
  unfold tailWord_7596111
  simp only [CollatzResearch.WordTrace]
  refine ⟨277052928983594634319588187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184701952655729756213058791 277052928983594634319588187)
  ·
    refine ⟨415579393475391951479382281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277052928983594634319588187 415579393475391951479382281)
    ·
      refine ⟨311684545106543963609536711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415579393475391951479382281 311684545106543963609536711)
      ·
        refine ⟨467526817659815945414305067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311684545106543963609536711 467526817659815945414305067)
        ·
          refine ⟨701290226489723918121457601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467526817659815945414305067 701290226489723918121457601)
          ·
            refine ⟨525967669867292938591093201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701290226489723918121457601 525967669867292938591093201)
            ·
              refine ⟨394475752400469703943319901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525967669867292938591093201 394475752400469703943319901)
              ·
                refine ⟨147928407150176138978744963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394475752400469703943319901 147928407150176138978744963)
                ·
                  refine ⟨221892610725264208468117445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147928407150176138978744963 221892610725264208468117445)
                  ·
                    refine ⟨41604864510987039087772021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221892610725264208468117445 41604864510987039087772021)
                    ·
                      refine ⟨3900456047905034914478627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41604864510987039087772021 3900456047905034914478627)
                      ·
                        rfl

theorem cell23_7596111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_7596111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596111 prefixEnd_7596111 := by exact prefixLift 7596111
  have htrace : WordTrace (prefixWord ++ tailWord_7596111) baseStart_7596111 baseEnd_7596111 := by
    simpa [prefixWord, tailWord_7596111, baseEnd_7596111] using wordTrace_append hprefix tailTrace_7596111
  have hstable : (prefixWord ++ tailWord_7596111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596111).length < 2 ^ (prefixWord ++ tailWord_7596111).sum := by decide
  have hdescent : baseEnd_7596111 < baseStart_7596111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596132 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_7596132 : Nat := 118140960795 + 7596132 * 2 ^ 59
def prefixEnd_7596132 : Nat := 4983230072969 + 3 ^ 40 * 7596132 * 2
def baseEnd_7596132 : Nat := 3900466830998779332316031

theorem tailTrace_7596132 : CollatzResearch.WordTrace tailWord_7596132 prefixEnd_7596132 3900466830998779332316031 := by
  unfold tailWord_7596132
  simp only [CollatzResearch.WordTrace]
  refine ⟨138526847458259277453051325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184702463277679036604068433 138526847458259277453051325)
  ·
    refine ⟨51947567796847229044894247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138526847458259277453051325 51947567796847229044894247)
    ·
      refine ⟨77921351695270843567341371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51947567796847229044894247 77921351695270843567341371)
      ·
        refine ⟨116882027542906265351012057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77921351695270843567341371 116882027542906265351012057)
        ·
          refine ⟨87661520657179699013259043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116882027542906265351012057 87661520657179699013259043)
          ·
            refine ⟨131492280985769548519888565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87661520657179699013259043 131492280985769548519888565)
            ·
              refine ⟨12327401342415895173739553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131492280985769548519888565 12327401342415895173739553)
              ·
                refine ⟨9245551006811921380304665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12327401342415895173739553 9245551006811921380304665)
                ·
                  refine ⟨6934163255108941035228499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9245551006811921380304665 6934163255108941035228499)
                  ·
                    refine ⟨10401244882663411552842749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934163255108941035228499 10401244882663411552842749)
                    ·
                      refine ⟨3900466830998779332316031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401244882663411552842749 3900466830998779332316031)
                      ·
                        rfl

theorem cell23_7596132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_7596132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596132 prefixEnd_7596132 := by exact prefixLift 7596132
  have htrace : WordTrace (prefixWord ++ tailWord_7596132) baseStart_7596132 baseEnd_7596132 := by
    simpa [prefixWord, tailWord_7596132, baseEnd_7596132] using wordTrace_append hprefix tailTrace_7596132
  have hstable : (prefixWord ++ tailWord_7596132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596132).length < 2 ^ (prefixWord ++ tailWord_7596132).sum := by decide
  have hdescent : baseEnd_7596132 < baseStart_7596132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596188 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7596188 : Nat := 118140960795 + 7596188 * 2 ^ 59
def prefixEnd_7596188 : Nat := 4983230072969 + 3 ^ 40 * 7596188 * 2
def baseEnd_7596188 : Nat := 3900495585915431113215773

theorem tailTrace_7596188 : CollatzResearch.WordTrace tailWord_7596188 prefixEnd_7596188 3900495585915431113215773 := by
  unfold tailWord_7596188
  simp only [CollatzResearch.WordTrace]
  refine ⟨138527868702157838235070609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184703824936210450980094145 138527868702157838235070609)
  ·
    refine ⟨103895901526618378676302957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138527868702157838235070609 103895901526618378676302957)
    ·
      refine ⟨38960963072481892003613609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103895901526618378676302957 38960963072481892003613609)
      ·
        refine ⟨29220722304361419002710207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38960963072481892003613609 29220722304361419002710207)
        ·
          refine ⟨43831083456542128504065311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29220722304361419002710207 43831083456542128504065311)
          ·
            refine ⟨65746625184813192756097967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43831083456542128504065311 65746625184813192756097967)
            ·
              refine ⟨98619937777219789134146951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65746625184813192756097967 98619937777219789134146951)
              ·
                refine ⟨147929906665829683701220427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98619937777219789134146951 147929906665829683701220427)
                ·
                  refine ⟨221894859998744525551830641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147929906665829683701220427 221894859998744525551830641)
                  ·
                    refine ⟨166421144999058394163872981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221894859998744525551830641 166421144999058394163872981)
                    ·
                      refine ⟨3900495585915431113215773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166421144999058394163872981 3900495585915431113215773)
                      ·
                        rfl

theorem cell23_7596188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7596188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596188 prefixEnd_7596188 := by exact prefixLift 7596188
  have htrace : WordTrace (prefixWord ++ tailWord_7596188) baseStart_7596188 baseEnd_7596188 := by
    simpa [prefixWord, tailWord_7596188, baseEnd_7596188] using wordTrace_append hprefix tailTrace_7596188
  have hstable : (prefixWord ++ tailWord_7596188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596188).length < 2 ^ (prefixWord ++ tailWord_7596188).sum := by decide
  have hdescent : baseEnd_7596188 < baseStart_7596188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596246 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_7596246 : Nat := 118140960795 + 7596246 * 2 ^ 59
def prefixEnd_7596246 : Nat := 4983230072969 + 3 ^ 40 * 7596246 * 2
def baseEnd_7596246 : Nat := 433391707532599098476723

theorem tailTrace_7596246 : CollatzResearch.WordTrace tailWord_7596246 prefixEnd_7596246 433391707532599098476723 := by
  unfold tailWord_7596246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17316115802381597023484537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184705235225403701583835061 17316115802381597023484537)
  ·
    refine ⟨12987086851786197767613403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17316115802381597023484537 12987086851786197767613403)
    ·
      refine ⟨19480630277679296651420105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12987086851786197767613403 19480630277679296651420105)
      ·
        refine ⟨14610472708259472488565079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19480630277679296651420105 14610472708259472488565079)
        ·
          refine ⟨21915709062389208732847619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14610472708259472488565079 21915709062389208732847619)
          ·
            refine ⟨32873563593583813099271429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21915709062389208732847619 32873563593583813099271429)
            ·
              refine ⟨6163793173796964956113393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32873563593583813099271429 6163793173796964956113393)
              ·
                refine ⟨4622844880347723717085045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6163793173796964956113393 4622844880347723717085045)
                ·
                  refine ⟨433391707532599098476723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622844880347723717085045 433391707532599098476723)
                  ·
                    rfl

theorem cell23_7596246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_7596246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596246 prefixEnd_7596246 := by exact prefixLift 7596246
  have htrace : WordTrace (prefixWord ++ tailWord_7596246) baseStart_7596246 baseEnd_7596246 := by
    simpa [prefixWord, tailWord_7596246, baseEnd_7596246] using wordTrace_append hprefix tailTrace_7596246
  have hstable : (prefixWord ++ tailWord_7596246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596246).length < 2 ^ (prefixWord ++ tailWord_7596246).sum := by decide
  have hdescent : baseEnd_7596246 < baseStart_7596246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596255 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 3, 4]
def baseStart_7596255 : Nat := 118140960795 + 7596255 * 2 ^ 59
def prefixEnd_7596255 : Nat := 4983230072969 + 3 ^ 40 * 7596255 * 2
def baseEnd_7596255 : Nat := 1300176663039760783692655

theorem tailTrace_7596255 : CollatzResearch.WordTrace tailWord_7596255 prefixEnd_7596255 1300176663039760783692655 := by
  unfold tailWord_7596255
  simp only [CollatzResearch.WordTrace]
  refine ⟨277058181095072946912830219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184705454063381964608553479 277058181095072946912830219)
  ·
    refine ⟨415587271642609420369245329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277058181095072946912830219 415587271642609420369245329)
    ·
      refine ⟨311690453731957065276933997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415587271642609420369245329 311690453731957065276933997)
      ·
        refine ⟨116883920149483899478850249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311690453731957065276933997 116883920149483899478850249)
        ·
          refine ⟨87662940112112924609137687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116883920149483899478850249 87662940112112924609137687)
          ·
            refine ⟨131494410168169386913706531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87662940112112924609137687 131494410168169386913706531)
            ·
              refine ⟨197241615252254080370559797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131494410168169386913706531 197241615252254080370559797)
              ·
                refine ⟨18491401429898820034739981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197241615252254080370559797 18491401429898820034739981)
                ·
                  refine ⟨6934275536212057513027493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18491401429898820034739981 6934275536212057513027493)
                  ·
                    refine ⟨1300176663039760783692655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934275536212057513027493 1300176663039760783692655)
                    ·
                      rfl

theorem cell23_7596255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_7596255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596255 prefixEnd_7596255 := by exact prefixLift 7596255
  have htrace : WordTrace (prefixWord ++ tailWord_7596255) baseStart_7596255 baseEnd_7596255 := by
    simpa [prefixWord, tailWord_7596255, baseEnd_7596255] using wordTrace_append hprefix tailTrace_7596255
  have hstable : (prefixWord ++ tailWord_7596255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596255).length < 2 ^ (prefixWord ++ tailWord_7596255).sum := by decide
  have hdescent : baseEnd_7596255 < baseStart_7596255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596282 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_7596282 : Nat := 118140960795 + 7596282 * 2 ^ 59
def prefixEnd_7596282 : Nat := 4983230072969 + 3 ^ 40 * 7596282 * 2
def baseEnd_7596282 : Nat := 3900543853096953745440341

theorem tailTrace_7596282 : CollatzResearch.WordTrace tailWord_7596282 prefixEnd_7596282 3900543853096953745440341 := by
  unfold tailWord_7596282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69264791466493782631015775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184706110577316753682708733 69264791466493782631015775)
  ·
    refine ⟨103897187199740673946523663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69264791466493782631015775 103897187199740673946523663)
    ·
      refine ⟨155845780799611010919785495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103897187199740673946523663 155845780799611010919785495)
      ·
        refine ⟨233768671199416516379678243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155845780799611010919785495 233768671199416516379678243)
        ·
          refine ⟨350653006799124774569517365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233768671199416516379678243 350653006799124774569517365)
          ·
            refine ⟨32873719387417947615892253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350653006799124774569517365 32873719387417947615892253)
            ·
              refine ⟨12327644770281730355959595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32873719387417947615892253 12327644770281730355959595)
              ·
                refine ⟨18491467155422595533939393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327644770281730355959595 18491467155422595533939393)
                ·
                  refine ⟨13868600366566946650454545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18491467155422595533939393 13868600366566946650454545)
                  ·
                    refine ⟨10401450274925209987840909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13868600366566946650454545 10401450274925209987840909)
                    ·
                      refine ⟨3900543853096953745440341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401450274925209987840909 3900543853096953745440341)
                      ·
                        rfl

theorem cell23_7596282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_7596282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596282 prefixEnd_7596282 := by exact prefixLift 7596282
  have htrace : WordTrace (prefixWord ++ tailWord_7596282) baseStart_7596282 baseEnd_7596282 := by
    simpa [prefixWord, tailWord_7596282, baseEnd_7596282] using wordTrace_append hprefix tailTrace_7596282
  have hstable : (prefixWord ++ tailWord_7596282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596282).length < 2 ^ (prefixWord ++ tailWord_7596282).sum := by decide
  have hdescent : baseEnd_7596282 < baseStart_7596282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596289 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 1, 4]
def baseStart_7596289 : Nat := 118140960795 + 7596289 * 2 ^ 59
def prefixEnd_7596289 : Nat := 4983230072969 + 3 ^ 40 * 7596289 * 2
def baseEnd_7596289 : Nat := 1300182482487178406017603

theorem tailTrace_7596289 : CollatzResearch.WordTrace tailWord_7596289 prefixEnd_7596289 1300182482487178406017603 := by
  unfold tailWord_7596289
  simp only [CollatzResearch.WordTrace]
  refine ⟨277059421176949770719567921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184706280784633180479711947 277059421176949770719567921)
  ·
    refine ⟨207794565882712328039675941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277059421176949770719567921 207794565882712328039675941)
    ·
      refine ⟨38961481103008561507439239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207794565882712328039675941 38961481103008561507439239)
      ·
        refine ⟨58442221654512842261158859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38961481103008561507439239 58442221654512842261158859)
        ·
          refine ⟨87663332481769263391738289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58442221654512842261158859 87663332481769263391738289)
          ·
            refine ⟨65747499361326947543803717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87663332481769263391738289 65747499361326947543803717)
            ·
              refine ⟨12327656130248802664463197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65747499361326947543803717 12327656130248802664463197)
              ·
                refine ⟨4622871048843300999173699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12327656130248802664463197 4622871048843300999173699)
                ·
                  refine ⟨6934306573264951498760549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622871048843300999173699 6934306573264951498760549)
                  ·
                    refine ⟨1300182482487178406017603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934306573264951498760549 1300182482487178406017603)
                    ·
                      rfl

theorem cell23_7596289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_7596289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596289 prefixEnd_7596289 := by exact prefixLift 7596289
  have htrace : WordTrace (prefixWord ++ tailWord_7596289) baseStart_7596289 baseEnd_7596289 := by
    simpa [prefixWord, tailWord_7596289, baseEnd_7596289] using wordTrace_append hprefix tailTrace_7596289
  have hstable : (prefixWord ++ tailWord_7596289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596289).length < 2 ^ (prefixWord ++ tailWord_7596289).sum := by decide
  have hdescent : baseEnd_7596289 < baseStart_7596289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596335 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_7596335 : Nat := 118140960795 + 7596335 * 2 ^ 59
def prefixEnd_7596335 : Nat := 4983230072969 + 3 ^ 40 * 7596335 * 2
def baseEnd_7596335 : Nat := 3900571067571642038077597

theorem tailTrace_7596335 : CollatzResearch.WordTrace tailWord_7596335 prefixEnd_7596335 3900571067571642038077597 := by
  unfold tailWord_7596335
  simp only [CollatzResearch.WordTrace]
  refine ⟨277061098934783120575742459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184707399289855413717161639 277061098934783120575742459)
  ·
    refine ⟨415591648402174680863613689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277061098934783120575742459 415591648402174680863613689)
    ·
      refine ⟨311693736301631010647710267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415591648402174680863613689 311693736301631010647710267)
      ·
        refine ⟨467540604452446515971565401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311693736301631010647710267 467540604452446515971565401)
        ·
          refine ⟨350655453339334886978674051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467540604452446515971565401 350655453339334886978674051)
          ·
            refine ⟨525983180009002330468011077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350655453339334886978674051 525983180009002330468011077)
            ·
              refine ⟨98621846251687936962752077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525983180009002330468011077 98621846251687936962752077)
              ·
                refine ⟨36983192344382976361032029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98621846251687936962752077 36983192344382976361032029)
                ·
                  refine ⟨13868697129143616135387011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36983192344382976361032029 13868697129143616135387011)
                  ·
                    refine ⟨20803045693715424203080517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13868697129143616135387011 20803045693715424203080517)
                    ·
                      refine ⟨3900571067571642038077597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20803045693715424203080517 3900571067571642038077597)
                      ·
                        rfl

theorem cell23_7596335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_7596335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596335 prefixEnd_7596335 := by exact prefixLift 7596335
  have htrace : WordTrace (prefixWord ++ tailWord_7596335) baseStart_7596335 baseEnd_7596335 := by
    simpa [prefixWord, tailWord_7596335, baseEnd_7596335] using wordTrace_append hprefix tailTrace_7596335
  have hstable : (prefixWord ++ tailWord_7596335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596335).length < 2 ^ (prefixWord ++ tailWord_7596335).sum := by decide
  have hdescent : baseEnd_7596335 < baseStart_7596335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596346 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3]
def baseStart_7596346 : Nat := 118140960795 + 7596346 * 2 ^ 59
def prefixEnd_7596346 : Nat := 4983230072969 + 3 ^ 40 * 7596346 * 2
def baseEnd_7596346 : Nat := 3900576715858841495040047

theorem tailTrace_7596346 : CollatzResearch.WordTrace tailWord_7596346 prefixEnd_7596346 3900576715858841495040047 := by
  unfold tailWord_7596346
  simp only [CollatzResearch.WordTrace]
  refine ⟨69265375034435817363598223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184707666758495512969595261 69265375034435817363598223)
  ·
    refine ⟨103898062551653726045397335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69265375034435817363598223 103898062551653726045397335)
    ·
      refine ⟨155847093827480589068096003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103898062551653726045397335 155847093827480589068096003)
      ·
        refine ⟨233770640741220883602144005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155847093827480589068096003 233770640741220883602144005)
        ·
          refine ⟨43831995138978915675402001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233770640741220883602144005 43831995138978915675402001)
          ·
            refine ⟨32873996354234186756551501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43831995138978915675402001 32873996354234186756551501)
            ·
              refine ⟨12327748632837820033706813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32873996354234186756551501 12327748632837820033706813)
              ·
                refine ⟨4622905737314182512640055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12327748632837820033706813 4622905737314182512640055)
                ·
                  refine ⟨6934358605971273768960083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622905737314182512640055 6934358605971273768960083)
                  ·
                    refine ⟨10401537908956910653440125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934358605971273768960083 10401537908956910653440125)
                    ·
                      refine ⟨3900576715858841495040047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401537908956910653440125 3900576715858841495040047)
                      ·
                        rfl

theorem cell23_7596346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_7596346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596346 prefixEnd_7596346 := by exact prefixLift 7596346
  have htrace : WordTrace (prefixWord ++ tailWord_7596346) baseStart_7596346 baseEnd_7596346 := by
    simpa [prefixWord, tailWord_7596346, baseEnd_7596346] using wordTrace_append hprefix tailTrace_7596346
  have hstable : (prefixWord ++ tailWord_7596346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596346).length < 2 ^ (prefixWord ++ tailWord_7596346).sum := by decide
  have hdescent : baseEnd_7596346 < baseStart_7596346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596355 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5]
def baseStart_7596355 : Nat := 118140960795 + 7596355 * 2 ^ 59
def prefixEnd_7596355 : Nat := 4983230072969 + 3 ^ 40 * 7596355 * 2
def baseEnd_7596355 : Nat := 3900581337184731959827505

theorem tailTrace_7596355 : CollatzResearch.WordTrace tailWord_7596355 prefixEnd_7596355 3900581337184731959827505 := by
  unfold tailWord_7596355
  simp only [CollatzResearch.WordTrace]
  refine ⟨277061828394710663991470519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184707885596473775994313679 277061828394710663991470519)
  ·
    refine ⟨415592742592065995987205779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277061828394710663991470519 415592742592065995987205779)
    ·
      refine ⟨623389113888098993980808669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415592742592065995987205779 623389113888098993980808669)
      ·
        refine ⟨233770917708037122742803251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623389113888098993980808669 233770917708037122742803251)
        ·
          refine ⟨350656376562055684114204877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233770917708037122742803251 350656376562055684114204877)
          ·
            refine ⟨131496141210770881542826829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350656376562055684114204877 131496141210770881542826829)
            ·
              refine ⟨49311052954039080578560061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131496141210770881542826829 49311052954039080578560061)
              ·
                refine ⟨18491644857764655216960023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49311052954039080578560061 18491644857764655216960023)
                ·
                  refine ⟨27737467286646982825440035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18491644857764655216960023 27737467286646982825440035)
                  ·
                    refine ⟨41606200929970474238160053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27737467286646982825440035 41606200929970474238160053)
                    ·
                      refine ⟨3900581337184731959827505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41606200929970474238160053 3900581337184731959827505)
                      ·
                        rfl

theorem cell23_7596355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_7596355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596355 prefixEnd_7596355 := by exact prefixLift 7596355
  have htrace : WordTrace (prefixWord ++ tailWord_7596355) baseStart_7596355 baseEnd_7596355 := by
    simpa [prefixWord, tailWord_7596355, baseEnd_7596355] using wordTrace_append hprefix tailTrace_7596355
  have hstable : (prefixWord ++ tailWord_7596355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596355).length < 2 ^ (prefixWord ++ tailWord_7596355).sum := by decide
  have hdescent : baseEnd_7596355 < baseStart_7596355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596372 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_7596372 : Nat := 118140960795 + 7596372 * 2 ^ 59
def prefixEnd_7596372 : Nat := 4983230072969 + 3 ^ 40 * 7596372 * 2
def baseEnd_7596372 : Nat := 3900590066355858393314927

theorem tailTrace_7596372 : CollatzResearch.WordTrace tailWord_7596372 prefixEnd_7596372 3900590066355858393314927 := by
  unfold tailWord_7596372
  simp only [CollatzResearch.WordTrace]
  refine ⟨138531224217824537947419685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184708298957099383929892913 138531224217824537947419685)
  ·
    refine ⟨25974604540842100865141191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138531224217824537947419685 25974604540842100865141191)
    ·
      refine ⟨38961906811263151297711787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25974604540842100865141191 38961906811263151297711787)
      ·
        refine ⟨58442860216894726946567681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38961906811263151297711787 58442860216894726946567681)
        ·
          refine ⟨43832145162671045209925761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58442860216894726946567681 43832145162671045209925761)
          ·
            refine ⟨32874108872003283907444321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43832145162671045209925761 32874108872003283907444321)
            ·
              refine ⟨24655581654002462930583241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32874108872003283907444321 24655581654002462930583241)
              ·
                refine ⟨18491686240501847197937431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24655581654002462930583241 18491686240501847197937431)
                ·
                  refine ⟨27737529360752770796906147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18491686240501847197937431 27737529360752770796906147)
                  ·
                    refine ⟨41606294041129156195359221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27737529360752770796906147 41606294041129156195359221)
                    ·
                      refine ⟨3900590066355858393314927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41606294041129156195359221 3900590066355858393314927)
                      ·
                        rfl

theorem cell23_7596372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_7596372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596372 prefixEnd_7596372 := by exact prefixLift 7596372
  have htrace : WordTrace (prefixWord ++ tailWord_7596372) baseStart_7596372 baseEnd_7596372 := by
    simpa [prefixWord, tailWord_7596372, baseEnd_7596372] using wordTrace_append hprefix tailTrace_7596372
  have hstable : (prefixWord ++ tailWord_7596372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596372).length < 2 ^ (prefixWord ++ tailWord_7596372).sum := by decide
  have hdescent : baseEnd_7596372 < baseStart_7596372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596375 : List Nat := [1, 1, 3, 2, 3, 1, 4, 8]
def baseStart_7596375 : Nat := 118140960795 + 7596375 * 2 ^ 59
def prefixEnd_7596375 : Nat := 4983230072969 + 3 ^ 40 * 7596375 * 2
def baseEnd_7596375 : Nat := 144466355807326736354719

theorem tailTrace_7596375 : CollatzResearch.WordTrace tailWord_7596375 prefixEnd_7596375 144466355807326736354719 := by
  unfold tailWord_7596375
  simp only [CollatzResearch.WordTrace]
  refine ⟨277062557854638207407198579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184708371903092138271465719 277062557854638207407198579)
  ·
    refine ⟨415593836781957311110797869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277062557854638207407198579 415593836781957311110797869)
    ·
      refine ⟨155847688793233991666549201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415593836781957311110797869 155847688793233991666549201)
      ·
        refine ⟨116885766594925493749911901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155847688793233991666549201 116885766594925493749911901)
        ·
          refine ⟨43832162473097060156216963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116885766594925493749911901 43832162473097060156216963)
          ·
            refine ⟨65748243709645590234325445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43832162473097060156216963 65748243709645590234325445)
            ·
              refine ⟨12327795695558548168936021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65748243709645590234325445 12327795695558548168936021)
              ·
                refine ⟨144466355807326736354719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12327795695558548168936021 144466355807326736354719)
                ·
                  rfl

theorem cell23_7596375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 8].length) (baseStart_7596375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596375 prefixEnd_7596375 := by exact prefixLift 7596375
  have htrace : WordTrace (prefixWord ++ tailWord_7596375) baseStart_7596375 baseEnd_7596375 := by
    simpa [prefixWord, tailWord_7596375, baseEnd_7596375] using wordTrace_append hprefix tailTrace_7596375
  have hstable : (prefixWord ++ tailWord_7596375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596375).length < 2 ^ (prefixWord ++ tailWord_7596375).sum := by decide
  have hdescent : baseEnd_7596375 < baseStart_7596375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596386 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7596386 : Nat := 118140960795 + 7596386 * 2 ^ 59
def prefixEnd_7596386 : Nat := 4983230072969 + 3 ^ 40 * 7596386 * 2
def baseEnd_7596386 : Nat := 3900597255085021338539863

theorem tailTrace_7596386 : CollatzResearch.WordTrace tailWord_7596386 prefixEnd_7596386 3900597255085021338539863 := by
  unfold tailWord_7596386
  simp only [CollatzResearch.WordTrace]
  refine ⟨69265739764399589071462253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184708639371732237523899341 69265739764399589071462253)
  ·
    refine ⟨25974652411649845901798345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69265739764399589071462253 25974652411649845901798345)
    ·
      refine ⟨19480989308737384426348759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25974652411649845901798345 19480989308737384426348759)
      ·
        refine ⟨29221483963106076639523139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19480989308737384426348759 29221483963106076639523139)
        ·
          refine ⟨43832225944659114959284709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29221483963106076639523139 43832225944659114959284709)
          ·
            refine ⟨8218542364623584054865883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43832225944659114959284709 8218542364623584054865883)
            ·
              refine ⟨12327813546935376082298825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218542364623584054865883 12327813546935376082298825)
              ·
                refine ⟨9245860160201532061724119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12327813546935376082298825 9245860160201532061724119)
                ·
                  refine ⟨13868790240302298092586179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9245860160201532061724119 13868790240302298092586179)
                  ·
                    refine ⟨20803185360453447138879269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13868790240302298092586179 20803185360453447138879269)
                    ·
                      refine ⟨3900597255085021338539863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20803185360453447138879269 3900597255085021338539863)
                      ·
                        rfl

theorem cell23_7596386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7596386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596386 prefixEnd_7596386 := by exact prefixLift 7596386
  have htrace : WordTrace (prefixWord ++ tailWord_7596386) baseStart_7596386 baseEnd_7596386 := by
    simpa [prefixWord, tailWord_7596386, baseEnd_7596386] using wordTrace_append hprefix tailTrace_7596386
  have hstable : (prefixWord ++ tailWord_7596386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596386).length < 2 ^ (prefixWord ++ tailWord_7596386).sum := by decide
  have hdescent : baseEnd_7596386 < baseStart_7596386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596389 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_7596389 : Nat := 118140960795 + 7596389 * 2 ^ 59
def prefixEnd_7596389 : Nat := 4983230072969 + 3 ^ 40 * 7596389 * 2
def baseEnd_7596389 : Nat := 3900598795526984826802349

theorem tailTrace_7596389 : CollatzResearch.WordTrace tailWord_7596389 prefixEnd_7596389 3900598795526984826802349 := by
  unfold tailWord_7596389
  simp only [CollatzResearch.WordTrace]
  refine ⟨277063068476587487798208221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184708712317724991865472147 277063068476587487798208221)
  ·
    refine ⟨103898650678720307924328083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277063068476587487798208221 103898650678720307924328083)
    ·
      refine ⟨155847976018080461886492125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103898650678720307924328083 155847976018080461886492125)
      ·
        refine ⟨58442991006780173207434547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155847976018080461886492125 58442991006780173207434547)
        ·
          refine ⟨87664486510170259811151821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58442991006780173207434547 87664486510170259811151821)
          ·
            refine ⟨32874182441313847429181933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87664486510170259811151821 32874182441313847429181933)
            ·
              refine ⟨12327818415492692785943225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32874182441313847429181933 12327818415492692785943225)
              ·
                refine ⟨9245863811619519589457419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12327818415492692785943225 9245863811619519589457419)
                ·
                  refine ⟨13868795717429279384186129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9245863811619519589457419 13868795717429279384186129)
                  ·
                    refine ⟨10401596788071959538139597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13868795717429279384186129 10401596788071959538139597)
                    ·
                      refine ⟨3900598795526984826802349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401596788071959538139597 3900598795526984826802349)
                      ·
                        rfl

theorem cell23_7596389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_7596389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596389 prefixEnd_7596389 := by exact prefixLift 7596389
  have htrace : WordTrace (prefixWord ++ tailWord_7596389) baseStart_7596389 baseEnd_7596389 := by
    simpa [prefixWord, tailWord_7596389, baseEnd_7596389] using wordTrace_append hprefix tailTrace_7596389
  have hstable : (prefixWord ++ tailWord_7596389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596389).length < 2 ^ (prefixWord ++ tailWord_7596389).sum := by decide
  have hdescent : baseEnd_7596389 < baseStart_7596389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596402 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_7596402 : Nat := 118140960795 + 7596402 * 2 ^ 59
def prefixEnd_7596402 : Nat := 4983230072969 + 3 ^ 40 * 7596402 * 2
def baseEnd_7596402 : Nat := 3900605470775493275939789

theorem tailTrace_7596402 : CollatzResearch.WordTrace tailWord_7596402 prefixEnd_7596402 3900605470775493275939789 := by
  unfold tailWord_7596402
  simp only [CollatzResearch.WordTrace]
  refine ⟨69265885656385097754607865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184709028417026927345620973 69265885656385097754607865)
  ·
    refine ⟨51949414242288823315955899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69265885656385097754607865 51949414242288823315955899)
    ·
      refine ⟨77924121363433234973933849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51949414242288823315955899 77924121363433234973933849)
      ·
        refine ⟨58443091022574926230450387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77924121363433234973933849 58443091022574926230450387)
        ·
          refine ⟨87664636533862389345675581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58443091022574926230450387 87664636533862389345675581)
          ·
            refine ⟨32874238700198396004628343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87664636533862389345675581 32874238700198396004628343)
            ·
              refine ⟨49311358050297594006942515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32874238700198396004628343 49311358050297594006942515)
              ·
                refine ⟨73967037075446391010413773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49311358050297594006942515 73967037075446391010413773)
                ·
                  refine ⟨27737638903292396628905165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73967037075446391010413773 27737638903292396628905165)
                  ·
                    refine ⟨10401614588734648735839437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27737638903292396628905165 10401614588734648735839437)
                    ·
                      refine ⟨3900605470775493275939789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401614588734648735839437 3900605470775493275939789)
                      ·
                        rfl

theorem cell23_7596402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_7596402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596402 prefixEnd_7596402 := by exact prefixLift 7596402
  have htrace : WordTrace (prefixWord ++ tailWord_7596402) baseStart_7596402 baseEnd_7596402 := by
    simpa [prefixWord, tailWord_7596402, baseEnd_7596402] using wordTrace_append hprefix tailTrace_7596402
  have hstable : (prefixWord ++ tailWord_7596402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596402).length < 2 ^ (prefixWord ++ tailWord_7596402).sum := by decide
  have hdescent : baseEnd_7596402 < baseStart_7596402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596426 : List Nat := [3, 1, 2, 5, 2, 1, 1, 8]
def baseStart_7596426 : Nat := 118140960795 + 7596426 * 2 ^ 59
def prefixEnd_7596426 : Nat := 4983230072969 + 3 ^ 40 * 7596426 * 2
def baseEnd_7596426 : Nat := 144467325715229673408877

theorem tailTrace_7596426 : CollatzResearch.WordTrace tailWord_7596426 prefixEnd_7596426 144467325715229673408877 := by
  unfold tailWord_7596426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69266104494363360779326283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184709611984968962078203421 69266104494363360779326283)
  ·
    refine ⟨103899156741545041168989425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69266104494363360779326283 103899156741545041168989425)
    ·
      refine ⟨77924367556158780876742069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103899156741545041168989425 77924367556158780876742069)
      ·
        refine ⟨7305409458389885707194569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77924367556158780876742069 7305409458389885707194569)
        ·
          refine ⟨5479057093792414280395927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7305409458389885707194569 5479057093792414280395927)
          ·
            refine ⟨8218585640688621420593891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479057093792414280395927 8218585640688621420593891)
            ·
              refine ⟨12327878461032932130890837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218585640688621420593891 12327878461032932130890837)
              ·
                refine ⟨144467325715229673408877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12327878461032932130890837 144467325715229673408877)
                ·
                  rfl

theorem cell23_7596426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_7596426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596426 prefixEnd_7596426 := by exact prefixLift 7596426
  have htrace : WordTrace (prefixWord ++ tailWord_7596426) baseStart_7596426 baseEnd_7596426 := by
    simpa [prefixWord, tailWord_7596426, baseEnd_7596426] using wordTrace_append hprefix tailTrace_7596426
  have hstable : (prefixWord ++ tailWord_7596426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596426).length < 2 ^ (prefixWord ++ tailWord_7596426).sum := by decide
  have hdescent : baseEnd_7596426 < baseStart_7596426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596436 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7596436 : Nat := 118140960795 + 7596436 * 2 ^ 59
def prefixEnd_7596436 : Nat := 4983230072969 + 3 ^ 40 * 7596436 * 2
def baseEnd_7596436 : Nat := 3900622929117746142914633

theorem tailTrace_7596436 : CollatzResearch.WordTrace tailWord_7596436 prefixEnd_7596436 3900622929117746142914633 := by
  unfold tailWord_7596436
  simp only [CollatzResearch.WordTrace]
  refine ⟨138532391353708607412584581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184709855138278143216779441 138532391353708607412584581)
  ·
    refine ⟨25974823378820363889859609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138532391353708607412584581 25974823378820363889859609)
    ·
      refine ⟨19481117534115272917394707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25974823378820363889859609 19481117534115272917394707)
      ·
        refine ⟨29221676301172909376092061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19481117534115272917394707 29221676301172909376092061)
        ·
          refine ⟨10958128612939841016034523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29221676301172909376092061 10958128612939841016034523)
          ·
            refine ⟨16437192919409761524051785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10958128612939841016034523 16437192919409761524051785)
            ·
              refine ⟨12327894689557321143038839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16437192919409761524051785 12327894689557321143038839)
              ·
                refine ⟨18491842034335981714558259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327894689557321143038839 18491842034335981714558259)
                ·
                  refine ⟨27737763051503972571837389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18491842034335981714558259 27737763051503972571837389)
                  ·
                    refine ⟨10401661144313989714439021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27737763051503972571837389 10401661144313989714439021)
                    ·
                      refine ⟨3900622929117746142914633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401661144313989714439021 3900622929117746142914633)
                      ·
                        rfl

theorem cell23_7596436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7596436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596436 prefixEnd_7596436 := by exact prefixLift 7596436
  have htrace : WordTrace (prefixWord ++ tailWord_7596436) baseStart_7596436 baseEnd_7596436 := by
    simpa [prefixWord, tailWord_7596436, baseEnd_7596436] using wordTrace_append hprefix tailTrace_7596436
  have hstable : (prefixWord ++ tailWord_7596436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596436).length < 2 ^ (prefixWord ++ tailWord_7596436).sum := by decide
  have hdescent : baseEnd_7596436 < baseStart_7596436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596512 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_7596512 : Nat := 118140960795 + 7596512 * 2 ^ 59
def prefixEnd_7596512 : Nat := 4983230072969 + 3 ^ 40 * 7596512 * 2
def baseEnd_7596512 : Nat := 1300220651215829281854761

theorem tailTrace_7596512 : CollatzResearch.WordTrace tailWord_7596512 prefixEnd_7596512 1300220651215829281854761 := by
  unfold tailWord_7596512
  simp only [CollatzResearch.WordTrace]
  refine ⟨138533777327570939902467895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184711703103427919869957193 138533777327570939902467895)
  ·
    refine ⟨207800665991356409853701843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138533777327570939902467895 207800665991356409853701843)
    ·
      refine ⟨311700998987034614780552765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207800665991356409853701843 311700998987034614780552765)
      ·
        refine ⟨116887874620137980542707287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311700998987034614780552765 116887874620137980542707287)
        ·
          refine ⟨175331811930206970814060931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116887874620137980542707287 175331811930206970814060931)
          ·
            refine ⟨262997717895310456221091397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175331811930206970814060931 262997717895310456221091397)
            ·
              refine ⟨49312072105370710541454637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262997717895310456221091397 49312072105370710541454637)
              ·
                refine ⟨18492027039514016453045489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49312072105370710541454637 18492027039514016453045489)
                ·
                  refine ⟨13869020279635512339784117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18492027039514016453045489 13869020279635512339784117)
                  ·
                    refine ⟨1300220651215829281854761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13869020279635512339784117 1300220651215829281854761)
                    ·
                      rfl

theorem cell23_7596512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_7596512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596512 prefixEnd_7596512 := by exact prefixLift 7596512
  have htrace : WordTrace (prefixWord ++ tailWord_7596512) baseStart_7596512 baseEnd_7596512 := by
    simpa [prefixWord, tailWord_7596512, baseEnd_7596512] using wordTrace_append hprefix tailTrace_7596512
  have hstable : (prefixWord ++ tailWord_7596512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596512).length < 2 ^ (prefixWord ++ tailWord_7596512).sum := by decide
  have hdescent : baseEnd_7596512 < baseStart_7596512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596533 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 7]
def baseStart_7596533 : Nat := 118140960795 + 7596533 * 2 ^ 59
def prefixEnd_7596533 : Nat := 4983230072969 + 3 ^ 40 * 7596533 * 2
def baseEnd_7596533 : Nat := 433408081860136918155743

theorem tailTrace_7596533 : CollatzResearch.WordTrace tailWord_7596533 prefixEnd_7596533 433408081860136918155743 := by
  unfold tailWord_7596533
  simp only [CollatzResearch.WordTrace]
  refine ⟨277068320588065800391450253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184712213725377200260966835 277068320588065800391450253)
  ·
    refine ⟨103900620220524675146793845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277068320588065800391450253 103900620220524675146793845)
    ·
      refine ⟨9740683145674188295011923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103900620220524675146793845 9740683145674188295011923)
      ·
        refine ⟨14611024718511282442517885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9740683145674188295011923 14611024718511282442517885)
        ·
          refine ⟨5479134269441730915944207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14611024718511282442517885 5479134269441730915944207)
          ·
            refine ⟨8218701404162596373916311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479134269441730915944207 8218701404162596373916311)
            ·
              refine ⟨12328052106243894560874467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218701404162596373916311 12328052106243894560874467)
              ·
                refine ⟨18492078159365841841311701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12328052106243894560874467 18492078159365841841311701)
                ·
                  refine ⟨433408081860136918155743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18492078159365841841311701 433408081860136918155743)
                  ·
                    rfl

theorem cell23_7596533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_7596533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596533 prefixEnd_7596533 := by exact prefixLift 7596533
  have htrace : WordTrace (prefixWord ++ tailWord_7596533) baseStart_7596533 baseEnd_7596533 := by
    simpa [prefixWord, tailWord_7596533, baseEnd_7596533] using wordTrace_append hprefix tailTrace_7596533
  have hstable : (prefixWord ++ tailWord_7596533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596533).length < 2 ^ (prefixWord ++ tailWord_7596533).sum := by decide
  have hdescent : baseEnd_7596533 < baseStart_7596533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596549 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_7596549 : Nat := 118140960795 + 7596549 * 2 ^ 59
def prefixEnd_7596549 : Nat := 4983230072969 + 3 ^ 40 * 7596549 * 2
def baseEnd_7596549 : Nat := 3900680952431704200801613

theorem tailTrace_7596549 : CollatzResearch.WordTrace tailWord_7596549 prefixEnd_7596549 3900680952431704200801613 := by
  unfold tailWord_7596549
  simp only [CollatzResearch.WordTrace]
  refine ⟨277068904156007835124032701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184712602770671890082688467 277068904156007835124032701)
  ·
    refine ⟨103900839058502938171512263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277068904156007835124032701 103900839058502938171512263)
    ·
      refine ⟨155851258587754407257268395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103900839058502938171512263 155851258587754407257268395)
      ·
        refine ⟨233776887881631610885902593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155851258587754407257268395 233776887881631610885902593)
        ·
          refine ⟨175332665911223708164426945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233776887881631610885902593 175332665911223708164426945)
          ·
            refine ⟨131499499433417781123320209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175332665911223708164426945 131499499433417781123320209)
            ·
              refine ⟨98624624575063335842490157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131499499433417781123320209 98624624575063335842490157)
              ·
                refine ⟨36984234215648750940933809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98624624575063335842490157 36984234215648750940933809)
                ·
                  refine ⟨27738175661736563205700357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36984234215648750940933809 27738175661736563205700357)
                  ·
                    refine ⟨5200907936575605601068817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27738175661736563205700357 5200907936575605601068817)
                    ·
                      refine ⟨3900680952431704200801613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200907936575605601068817 3900680952431704200801613)
                      ·
                        rfl

theorem cell23_7596549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_7596549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596549 prefixEnd_7596549 := by exact prefixLift 7596549
  have htrace : WordTrace (prefixWord ++ tailWord_7596549) baseStart_7596549 baseEnd_7596549 := by
    simpa [prefixWord, tailWord_7596549, baseEnd_7596549] using wordTrace_append hprefix tailTrace_7596549
  have hstable : (prefixWord ++ tailWord_7596549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596549).length < 2 ^ (prefixWord ++ tailWord_7596549).sum := by decide
  have hdescent : baseEnd_7596549 < baseStart_7596549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596586 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7596586 : Nat := 118140960795 + 7596586 * 2 ^ 59
def prefixEnd_7596586 : Nat := 4983230072969 + 3 ^ 40 * 7596586 * 2
def baseEnd_7596586 : Nat := 3900699951215920556038943

theorem tailTrace_7596586 : CollatzResearch.WordTrace tailWord_7596586 prefixEnd_7596586 3900699951215920556038943 := by
  unfold tailWord_7596586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69267563414218447610782403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184713502437915860295419741 69267563414218447610782403)
  ·
    refine ⟨103901345121327671416173605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69267563414218447610782403 103901345121327671416173605)
    ·
      refine ⟨19481502210248938390532551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103901345121327671416173605 19481502210248938390532551)
      ·
        refine ⟨29222253315373407585798827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19481502210248938390532551 29222253315373407585798827)
        ·
          refine ⟨43833379973060111378698241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29222253315373407585798827 43833379973060111378698241)
          ·
            refine ⟨32875034979795083534023681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43833379973060111378698241 32875034979795083534023681)
            ·
              refine ⟨24656276234846312650517761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32875034979795083534023681 24656276234846312650517761)
              ·
                refine ⟨18492207176134734487888321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24656276234846312650517761 18492207176134734487888321)
                ·
                  refine ⟨13869155382101050865916241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18492207176134734487888321 13869155382101050865916241)
                  ·
                    refine ⟨10401866536575788149437181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13869155382101050865916241 10401866536575788149437181)
                    ·
                      refine ⟨3900699951215920556038943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401866536575788149437181 3900699951215920556038943)
                      ·
                        rfl

theorem cell23_7596586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7596586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596586 prefixEnd_7596586 := by exact prefixLift 7596586
  have htrace : WordTrace (prefixWord ++ tailWord_7596586) baseStart_7596586 baseEnd_7596586 := by
    simpa [prefixWord, tailWord_7596586, baseEnd_7596586] using wordTrace_append hprefix tailTrace_7596586
  have hstable : (prefixWord ++ tailWord_7596586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596586).length < 2 ^ (prefixWord ++ tailWord_7596586).sum := by decide
  have hdescent : baseEnd_7596586 < baseStart_7596586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596593 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 1, 4]
def baseStart_7596593 : Nat := 118140960795 + 7596593 * 2 ^ 59
def prefixEnd_7596593 : Nat := 4983230072969 + 3 ^ 40 * 7596593 * 2
def baseEnd_7596593 : Nat := 1300234515193500676217137

theorem tailTrace_7596593 : CollatzResearch.WordTrace tailWord_7596593 prefixEnd_7596593 1300234515193500676217137 := by
  unfold tailWord_7596593
  simp only [CollatzResearch.WordTrace]
  refine ⟨277070508967848430638634433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184713672645232287092422955 277070508967848430638634433)
  ·
    refine ⟨207802881725886322978975825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277070508967848430638634433 207802881725886322978975825)
    ·
      refine ⟨155852161294414742234231869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207802881725886322978975825 155852161294414742234231869)
      ·
        refine ⟨58444560485405528337836951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155852161294414742234231869 58444560485405528337836951)
        ·
          refine ⟨87666840728108292506755427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58444560485405528337836951 87666840728108292506755427)
          ·
            refine ⟨131500261092162438760133141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87666840728108292506755427 131500261092162438760133141)
            ·
              refine ⟨6164074738695114316881241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131500261092162438760133141 6164074738695114316881241)
              ·
                refine ⟨4623056054021335737660931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6164074738695114316881241 4623056054021335737660931)
                ·
                  refine ⟨6934584081032003606491397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623056054021335737660931 6934584081032003606491397)
                  ·
                    refine ⟨1300234515193500676217137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934584081032003606491397 1300234515193500676217137)
                    ·
                      rfl

theorem cell23_7596593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_7596593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596593 prefixEnd_7596593 := by exact prefixLift 7596593
  have htrace : WordTrace (prefixWord ++ tailWord_7596593) baseStart_7596593 baseEnd_7596593 := by
    simpa [prefixWord, tailWord_7596593, baseEnd_7596593] using wordTrace_append hprefix tailTrace_7596593
  have hstable : (prefixWord ++ tailWord_7596593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596593).length < 2 ^ (prefixWord ++ tailWord_7596593).sum := by decide
  have hdescent : baseEnd_7596593 < baseStart_7596593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596626 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_7596626 : Nat := 118140960795 + 7596626 * 2 ^ 59
def prefixEnd_7596626 : Nat := 4983230072969 + 3 ^ 40 * 7596626 * 2
def baseEnd_7596626 : Nat := 3900720490442100399538759

theorem tailTrace_7596626 : CollatzResearch.WordTrace tailWord_7596626 prefixEnd_7596626 3900720490442100399538759 := by
  unfold tailWord_7596626
  simp only [CollatzResearch.WordTrace]
  refine ⟨69267928144182219318646433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184714475051152584849723821 69267928144182219318646433)
  ·
    refine ⟨51950946108136664488984825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69267928144182219318646433 51950946108136664488984825)
    ·
      refine ⟨38963209581102498366738619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51950946108136664488984825 38963209581102498366738619)
      ·
        refine ⟨58444814371653747550107929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38963209581102498366738619 58444814371653747550107929)
        ·
          refine ⟨43833610778740310662580947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58444814371653747550107929 43833610778740310662580947)
          ·
            refine ⟨65750416168110465993871421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43833610778740310662580947 65750416168110465993871421)
            ·
              refine ⟨24656406063041424747701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65750416168110465993871421 24656406063041424747701783)
              ·
                refine ⟨36984609094562137121552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24656406063041424747701783 36984609094562137121552675)
                ·
                  refine ⟨55476913641843205682329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36984609094562137121552675 55476913641843205682329013)
                  ·
                    refine ⟨5200960653922800532718345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55476913641843205682329013 5200960653922800532718345)
                    ·
                      refine ⟨3900720490442100399538759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200960653922800532718345 3900720490442100399538759)
                      ·
                        rfl

theorem cell23_7596626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_7596626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596626 prefixEnd_7596626 := by exact prefixLift 7596626
  have htrace : WordTrace (prefixWord ++ tailWord_7596626) baseStart_7596626 baseEnd_7596626 := by
    simpa [prefixWord, tailWord_7596626, baseEnd_7596626] using wordTrace_append hprefix tailTrace_7596626
  have hstable : (prefixWord ++ tailWord_7596626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596626).length < 2 ^ (prefixWord ++ tailWord_7596626).sum := by decide
  have hdescent : baseEnd_7596626 < baseStart_7596626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596639 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 8, 2]
def baseStart_7596639 : Nat := 118140960795 + 7596639 * 2 ^ 59
def prefixEnd_7596639 : Nat := 4983230072969 + 3 ^ 40 * 7596639 * 2
def baseEnd_7596639 : Nat := 3900727165690608848676199

theorem tailTrace_7596639 : CollatzResearch.WordTrace tailWord_7596639 prefixEnd_7596639 3900727165690608848676199 := by
  unfold tailWord_7596639
  simp only [CollatzResearch.WordTrace]
  refine ⟨277072186725681780494808971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184714791150454520329872647 277072186725681780494808971)
  ·
    refine ⟨415608280088522670742213457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277072186725681780494808971 415608280088522670742213457)
    ·
      refine ⟨311706210066392003056660093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415608280088522670742213457 311706210066392003056660093)
      ·
        refine ⟨116889828774897001146247535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311706210066392003056660093 116889828774897001146247535)
        ·
          refine ⟨175334743162345501719371303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116889828774897001146247535 175334743162345501719371303)
          ·
            refine ⟨263002114743518252579056955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175334743162345501719371303 263002114743518252579056955)
            ·
              refine ⟨394503172115277378868585433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263002114743518252579056955 394503172115277378868585433)
              ·
                refine ⟨295877379086458034151439075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394503172115277378868585433 295877379086458034151439075)
                ·
                  refine ⟨443816068629687051227158613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295877379086458034151439075 443816068629687051227158613)
                  ·
                    refine ⟨5200969554254145131568265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 443816068629687051227158613 5200969554254145131568265)
                    ·
                      refine ⟨3900727165690608848676199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200969554254145131568265 3900727165690608848676199)
                      ·
                        rfl

theorem cell23_7596639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_7596639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596639 prefixEnd_7596639 := by exact prefixLift 7596639
  have htrace : WordTrace (prefixWord ++ tailWord_7596639) baseStart_7596639 baseEnd_7596639 := by
    simpa [prefixWord, tailWord_7596639, baseEnd_7596639] using wordTrace_append hprefix tailTrace_7596639
  have hstable : (prefixWord ++ tailWord_7596639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596639).length < 2 ^ (prefixWord ++ tailWord_7596639).sum := by decide
  have hdescent : baseEnd_7596639 < baseStart_7596639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596659 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3]
def baseStart_7596659 : Nat := 118140960795 + 7596659 * 2 ^ 59
def prefixEnd_7596659 : Nat := 4983230072969 + 3 ^ 40 * 7596659 * 2
def baseEnd_7596659 : Nat := 3900737435303698770426107

theorem tailTrace_7596659 : CollatzResearch.WordTrace tailWord_7596659 prefixEnd_7596659 3900737435303698770426107 := by
  unfold tailWord_7596659
  simp only [CollatzResearch.WordTrace]
  refine ⟨277072916185609323910537031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184715277457072882607024687 277072916185609323910537031)
  ·
    refine ⟨415609374278413985865805547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277072916185609323910537031 415609374278413985865805547)
    ·
      refine ⟨623414061417620978798708321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415609374278413985865805547 623414061417620978798708321)
      ·
        refine ⟨467560546063215734099031241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623414061417620978798708321 467560546063215734099031241)
        ·
          refine ⟨350670409547411800574273431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467560546063215734099031241 350670409547411800574273431)
          ·
            refine ⟨526005614321117700861410147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350670409547411800574273431 526005614321117700861410147)
            ·
              refine ⟨789008421481676551292115221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526005614321117700861410147 789008421481676551292115221)
              ·
                refine ⟨36984769756953588341817901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 789008421481676551292115221 36984769756953588341817901)
                ·
                  refine ⟨13869288658857595628181713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36984769756953588341817901 13869288658857595628181713)
                  ·
                    refine ⟨10401966494143196721136285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13869288658857595628181713 10401966494143196721136285)
                    ·
                      refine ⟨3900737435303698770426107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10401966494143196721136285 3900737435303698770426107)
                      ·
                        rfl

theorem cell23_7596659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_7596659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596659 prefixEnd_7596659 := by exact prefixLift 7596659
  have htrace : WordTrace (prefixWord ++ tailWord_7596659) baseStart_7596659 baseEnd_7596659 := by
    simpa [prefixWord, tailWord_7596659, baseEnd_7596659] using wordTrace_append hprefix tailTrace_7596659
  have hstable : (prefixWord ++ tailWord_7596659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596659).length < 2 ^ (prefixWord ++ tailWord_7596659).sum := by decide
  have hdescent : baseEnd_7596659 < baseStart_7596659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596673 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_7596673 : Nat := 118140960795 + 7596673 * 2 ^ 59
def prefixEnd_7596673 : Nat := 4983230072969 + 3 ^ 40 * 7596673 * 2
def baseEnd_7596673 : Nat := 3900744624032861715651043

theorem tailTrace_7596673 : CollatzResearch.WordTrace tailWord_7596673 prefixEnd_7596673 3900744624032861715651043 := by
  unfold tailWord_7596673
  simp only [CollatzResearch.WordTrace]
  refine ⟨277073426807558604301546673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184715617871705736201031115 277073426807558604301546673)
  ·
    refine ⟨207805070105668953226160005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277073426807558604301546673 207805070105668953226160005)
    ·
      refine ⟨38963450644812928729905001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207805070105668953226160005 38963450644812928729905001)
      ·
        refine ⟨29222587983609696547428751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38963450644812928729905001 29222587983609696547428751)
        ·
          refine ⟨43833881975414544821143127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29222587983609696547428751 43833881975414544821143127)
          ·
            refine ⟨65750822963121817231714691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43833881975414544821143127 65750822963121817231714691)
            ·
              refine ⟨98626234444682725847572037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65750822963121817231714691 98626234444682725847572037)
              ·
                refine ⟨18492418958378011096419757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98626234444682725847572037 18492418958378011096419757)
                ·
                  refine ⟨6934657109391754161157409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18492418958378011096419757 6934657109391754161157409)
                  ·
                    refine ⟨5200992832043815620868057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6934657109391754161157409 5200992832043815620868057)
                    ·
                      refine ⟨3900744624032861715651043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5200992832043815620868057 3900744624032861715651043)
                      ·
                        rfl

theorem cell23_7596673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_7596673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596673 prefixEnd_7596673 := by exact prefixLift 7596673
  have htrace : WordTrace (prefixWord ++ tailWord_7596673) baseStart_7596673 baseEnd_7596673 := by
    simpa [prefixWord, tailWord_7596673, baseEnd_7596673] using wordTrace_append hprefix tailTrace_7596673
  have hstable : (prefixWord ++ tailWord_7596673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596673).length < 2 ^ (prefixWord ++ tailWord_7596673).sum := by decide
  have hdescent : baseEnd_7596673 < baseStart_7596673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596723 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 3]
def baseStart_7596723 : Nat := 118140960795 + 7596723 * 2 ^ 59
def prefixEnd_7596723 : Nat := 4983230072969 + 3 ^ 40 * 7596723 * 2
def baseEnd_7596723 : Nat := 3900770298065586520025813

theorem tailTrace_7596723 : CollatzResearch.WordTrace tailWord_7596723 prefixEnd_7596723 3900770298065586520025813 := by
  unfold tailWord_7596723
  simp only [CollatzResearch.WordTrace]
  refine ⟨277075250457377462840866823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184716833638251641893911215 277075250457377462840866823)
  ·
    refine ⟨415612875686066194261300235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277075250457377462840866823 415612875686066194261300235)
    ·
      refine ⟨623419313529099291391950353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415612875686066194261300235 623419313529099291391950353)
      ·
        refine ⟨467564485146824468543962765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623419313529099291391950353 467564485146824468543962765)
        ·
          refine ⟨175336681930059175703986037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467564485146824468543962765 175336681930059175703986037)
          ·
            refine ⟨16437813930943047722248691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175336681930059175703986037 16437813930943047722248691)
            ·
              refine ⟨24656720896414571583373037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16437813930943047722248691 24656720896414571583373037)
              ·
                refine ⟨9246270336155464343764889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24656720896414571583373037 9246270336155464343764889)
                ·
                  refine ⟨6934702752116598257823667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9246270336155464343764889 6934702752116598257823667)
                  ·
                    refine ⟨10402054128174897386735501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934702752116598257823667 10402054128174897386735501)
                    ·
                      refine ⟨3900770298065586520025813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402054128174897386735501 3900770298065586520025813)
                      ·
                        rfl

theorem cell23_7596723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 3].length) (baseStart_7596723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596723 prefixEnd_7596723 := by exact prefixLift 7596723
  have htrace : WordTrace (prefixWord ++ tailWord_7596723) baseStart_7596723 baseEnd_7596723 := by
    simpa [prefixWord, tailWord_7596723, baseEnd_7596723] using wordTrace_append hprefix tailTrace_7596723
  have hstable : (prefixWord ++ tailWord_7596723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596723).length < 2 ^ (prefixWord ++ tailWord_7596723).sum := by decide
  have hdescent : baseEnd_7596723 < baseStart_7596723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596733 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_7596733 : Nat := 118140960795 + 7596733 * 2 ^ 59
def prefixEnd_7596733 : Nat := 4983230072969 + 3 ^ 40 * 7596733 * 2
def baseEnd_7596733 : Nat := 3900775432872131480900767

theorem tailTrace_7596733 : CollatzResearch.WordTrace tailWord_7596733 prefixEnd_7596733 3900775432872131480900767 := by
  unfold tailWord_7596733
  simp only [CollatzResearch.WordTrace]
  refine ⟨277075615187341234548730853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184717076791560823032487235 277075615187341234548730853)
  ·
    refine ⟨51951677847626481477887035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277075615187341234548730853 51951677847626481477887035)
    ·
      refine ⟨77927516771439722216830553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51951677847626481477887035 77927516771439722216830553)
      ·
        refine ⟨58445637578579791662622915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77927516771439722216830553 58445637578579791662622915)
        ·
          refine ⟨87668456367869687493934373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58445637578579791662622915 87668456367869687493934373)
          ·
            refine ⟨16437835568975566405112695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87668456367869687493934373 16437835568975566405112695)
            ·
              refine ⟨24656753353463349607669043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16437835568975566405112695 24656753353463349607669043)
              ·
                refine ⟨36985130030195024411503565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24656753353463349607669043 36985130030195024411503565)
                ·
                  refine ⟨13869423761323134154313837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36985130030195024411503565 13869423761323134154313837)
                  ·
                    refine ⟨5201033910496175307867689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13869423761323134154313837 5201033910496175307867689)
                    ·
                      refine ⟨3900775432872131480900767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201033910496175307867689 3900775432872131480900767)
                      ·
                        rfl

theorem cell23_7596733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_7596733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596733 prefixEnd_7596733 := by exact prefixLift 7596733
  have htrace : WordTrace (prefixWord ++ tailWord_7596733) baseStart_7596733 baseEnd_7596733 := by
    simpa [prefixWord, tailWord_7596733, baseEnd_7596733] using wordTrace_append hprefix tailTrace_7596733
  have hstable : (prefixWord ++ tailWord_7596733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596733).length < 2 ^ (prefixWord ++ tailWord_7596733).sum := by decide
  have hdescent : baseEnd_7596733 < baseStart_7596733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596757 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7596757 : Nat := 118140960795 + 7596757 * 2 ^ 59
def prefixEnd_7596757 : Nat := 4983230072969 + 3 ^ 40 * 7596757 * 2
def baseEnd_7596757 : Nat := 3900787756407839387000657

theorem tailTrace_7596757 : CollatzResearch.WordTrace tailWord_7596757 prefixEnd_7596757 3900787756407839387000657 := by
  unfold tailWord_7596757
  simp only [CollatzResearch.WordTrace]
  refine ⟨277076490539254286647604525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184717660359502857765069683 277076490539254286647604525)
  ·
    refine ⟨103903683952220357492851697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277076490539254286647604525 103903683952220357492851697)
    ·
      refine ⟨77927762964165268119638773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103903683952220357492851697 77927762964165268119638773)
      ·
        refine ⟨7305727777890493886216135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77927762964165268119638773 7305727777890493886216135)
        ·
          refine ⟨10958591666835740829324203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7305727777890493886216135 10958591666835740829324203)
          ·
            refine ⟨16437887500253611243986305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10958591666835740829324203 16437887500253611243986305)
            ·
              refine ⟨12328415625190208432989729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16437887500253611243986305 12328415625190208432989729)
              ·
                refine ⟨9246311718892656324742297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12328415625190208432989729 9246311718892656324742297)
                ·
                  refine ⟨6934733789169492243556723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9246311718892656324742297 6934733789169492243556723)
                  ·
                    refine ⟨10402100683754238365335085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934733789169492243556723 10402100683754238365335085)
                    ·
                      refine ⟨3900787756407839387000657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402100683754238365335085 3900787756407839387000657)
                      ·
                        rfl

theorem cell23_7596757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7596757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596757 prefixEnd_7596757 := by exact prefixLift 7596757
  have htrace : WordTrace (prefixWord ++ tailWord_7596757) baseStart_7596757 baseEnd_7596757 := by
    simpa [prefixWord, tailWord_7596757, baseEnd_7596757] using wordTrace_append hprefix tailTrace_7596757
  have hstable : (prefixWord ++ tailWord_7596757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596757).length < 2 ^ (prefixWord ++ tailWord_7596757).sum := by decide
  have hdescent : baseEnd_7596757 < baseStart_7596757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596786 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_7596786 : Nat := 118140960795 + 7596786 * 2 ^ 59
def prefixEnd_7596786 : Nat := 4983230072969 + 3 ^ 40 * 7596786 * 2
def baseEnd_7596786 : Nat := 433422516371868863726447

theorem tailTrace_7596786 : CollatzResearch.WordTrace tailWord_7596786 prefixEnd_7596786 433422516371868863726447 := by
  unfold tailWord_7596786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69269387064037306150102553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184718365504099483066940141 69269387064037306150102553)
  ·
    refine ⟨51952040298027979612576915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69269387064037306150102553 51952040298027979612576915)
    ·
      refine ⟨77928060447041969418865373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51952040298027979612576915 77928060447041969418865373)
      ·
        refine ⟨29223022667640738532074515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77928060447041969418865373 29223022667640738532074515)
        ·
          refine ⟨43834534001461107798111773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29223022667640738532074515 43834534001461107798111773)
          ·
            refine ⟨16437950250547915424291915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43834534001461107798111773 16437950250547915424291915)
            ·
              refine ⟨24656925375821873136437873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16437950250547915424291915 24656925375821873136437873)
              ·
                refine ⟨18492694031866404852328405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24656925375821873136437873 18492694031866404852328405)
                ·
                  refine ⟨433422516371868863726447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18492694031866404852328405 433422516371868863726447)
                  ·
                    rfl

theorem cell23_7596786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_7596786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596786 prefixEnd_7596786 := by exact prefixLift 7596786
  have htrace : WordTrace (prefixWord ++ tailWord_7596786) baseStart_7596786 baseEnd_7596786 := by
    simpa [prefixWord, tailWord_7596786, baseEnd_7596786] using wordTrace_append hprefix tailTrace_7596786
  have hstable : (prefixWord ++ tailWord_7596786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596786).length < 2 ^ (prefixWord ++ tailWord_7596786).sum := by decide
  have hdescent : baseEnd_7596786 < baseStart_7596786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596809 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_7596809 : Nat := 118140960795 + 7596809 * 2 ^ 59
def prefixEnd_7596809 : Nat := 4983230072969 + 3 ^ 40 * 7596809 * 2
def baseEnd_7596809 : Nat := 3900814457401873183550417

theorem tailTrace_7596809 : CollatzResearch.WordTrace tailWord_7596809 prefixEnd_7596809 3900814457401873183550417 := by
  unfold tailWord_7596809
  simp only [CollatzResearch.WordTrace]
  refine ⟨277078387135065899528497481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184718924756710599685664987 277078387135065899528497481)
  ·
    refine ⟨207808790351299424646373111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277078387135065899528497481 207808790351299424646373111)
    ·
      refine ⟨311713185526949136969559667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207808790351299424646373111 311713185526949136969559667)
      ·
        refine ⟨467569778290423705454339501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311713185526949136969559667 467569778290423705454339501)
        ·
          refine ⟨175338666858908889545377313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467569778290423705454339501 175338666858908889545377313)
          ·
            refine ⟨131504000144181667159032985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175338666858908889545377313 131504000144181667159032985)
            ·
              refine ⟨98628000108136250369274739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131504000144181667159032985 98628000108136250369274739)
              ·
                refine ⟨147942000162204375553912109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98628000108136250369274739 147942000162204375553912109)
                ·
                  refine ⟨55478250060826640832717041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147942000162204375553912109 55478250060826640832717041)
                  ·
                    refine ⟨41608687545619980624537781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55478250060826640832717041 41608687545619980624537781)
                    ·
                      refine ⟨3900814457401873183550417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41608687545619980624537781 3900814457401873183550417)
                      ·
                        rfl

theorem cell23_7596809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_7596809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596809 prefixEnd_7596809 := by exact prefixLift 7596809
  have htrace : WordTrace (prefixWord ++ tailWord_7596809) baseStart_7596809 baseEnd_7596809 := by
    simpa [prefixWord, tailWord_7596809, baseEnd_7596809] using wordTrace_append hprefix tailTrace_7596809
  have hstable : (prefixWord ++ tailWord_7596809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596809).length < 2 ^ (prefixWord ++ tailWord_7596809).sum := by decide
  have hdescent : baseEnd_7596809 < baseStart_7596809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596854 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7596854 : Nat := 118140960795 + 7596854 * 2 ^ 59
def prefixEnd_7596854 : Nat := 4983230072969 + 3 ^ 40 * 7596854 * 2
def baseEnd_7596854 : Nat := 433426396003480611943079

theorem tailTrace_7596854 : CollatzResearch.WordTrace tailWord_7596854 prefixEnd_7596854 433426396003480611943079 := by
  unfold tailWord_7596854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317501776243929513367851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184720018946601914809257077 17317501776243929513367851)
  ·
    refine ⟨25976252664365894270051777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17317501776243929513367851 25976252664365894270051777)
    ·
      refine ⟨19482189498274420702538833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25976252664365894270051777 19482189498274420702538833)
      ·
        refine ⟨14611642123705815526904125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19482189498274420702538833 14611642123705815526904125)
        ·
          refine ⟨5479365796389680822589047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14611642123705815526904125 5479365796389680822589047)
          ·
            refine ⟨8219048694584521233883571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479365796389680822589047 8219048694584521233883571)
            ·
              refine ⟨12328573041876781850825357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219048694584521233883571 12328573041876781850825357)
              ·
                refine ⟨4623214890703793194059509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12328573041876781850825357 4623214890703793194059509)
                ·
                  refine ⟨433426396003480611943079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4623214890703793194059509 433426396003480611943079)
                  ·
                    rfl

theorem cell23_7596854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7596854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596854 prefixEnd_7596854 := by exact prefixLift 7596854
  have htrace : WordTrace (prefixWord ++ tailWord_7596854) baseStart_7596854 baseEnd_7596854 := by
    simpa [prefixWord, tailWord_7596854, baseEnd_7596854] using wordTrace_append hprefix tailTrace_7596854
  have hstable : (prefixWord ++ tailWord_7596854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596854).length < 2 ^ (prefixWord ++ tailWord_7596854).sum := by decide
  have hdescent : baseEnd_7596854 < baseStart_7596854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596856 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_7596856 : Nat := 118140960795 + 7596856 * 2 ^ 59
def prefixEnd_7596856 : Nat := 4983230072969 + 3 ^ 40 * 7596856 * 2
def baseEnd_7596856 : Nat := 3900838590992634499662701

theorem tailTrace_7596856 : CollatzResearch.WordTrace tailWord_7596856 prefixEnd_7596856 3900838590992634499662701 := by
  unfold tailWord_7596856
  simp only [CollatzResearch.WordTrace]
  refine ⟨138540050682947813277729211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184720067577263751036972281 138540050682947813277729211)
  ·
    refine ⟨207810076024421719916593817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138540050682947813277729211 207810076024421719916593817)
    ·
      refine ⟨155857557018316289937445363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207810076024421719916593817 155857557018316289937445363)
      ·
        refine ⟨233786335527474434906168045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155857557018316289937445363 233786335527474434906168045)
        ·
          refine ⟨87669875822802913089813017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233786335527474434906168045 87669875822802913089813017)
          ·
            refine ⟨65752406867102184817359763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87669875822802913089813017 65752406867102184817359763)
            ·
              refine ⟨98628610300653277226039645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65752406867102184817359763 98628610300653277226039645)
              ·
                refine ⟨36985728862744978959764867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98628610300653277226039645 36985728862744978959764867)
                ·
                  refine ⟨55478593294117468439647301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36985728862744978959764867 55478593294117468439647301)
                  ·
                    refine ⟨10402236242647025332433869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55478593294117468439647301 10402236242647025332433869)
                    ·
                      refine ⟨3900838590992634499662701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402236242647025332433869 3900838590992634499662701)
                      ·
                        rfl

theorem cell23_7596856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_7596856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596856 prefixEnd_7596856 := by exact prefixLift 7596856
  have htrace : WordTrace (prefixWord ++ tailWord_7596856) baseStart_7596856 baseEnd_7596856 := by
    simpa [prefixWord, tailWord_7596856, baseEnd_7596856] using wordTrace_append hprefix tailTrace_7596856
  have hstable : (prefixWord ++ tailWord_7596856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596856).length < 2 ^ (prefixWord ++ tailWord_7596856).sum := by decide
  have hdescent : baseEnd_7596856 < baseStart_7596856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596873 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_7596873 : Nat := 118140960795 + 7596873 * 2 ^ 59
def prefixEnd_7596873 : Nat := 4983230072969 + 3 ^ 40 * 7596873 * 2
def baseEnd_7596873 : Nat := 3900847320163760933150123

theorem tailTrace_7596873 : CollatzResearch.WordTrace tailWord_7596873 prefixEnd_7596873 3900847320163760933150123 := by
  unfold tailWord_7596873
  simp only [CollatzResearch.WordTrace]
  refine ⟨277080721406834038458827273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184720480937889358972551515 277080721406834038458827273)
  ·
    refine ⟨207810541055125528844120455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277080721406834038458827273 207810541055125528844120455)
    ·
      refine ⟨311715811582688293266180683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207810541055125528844120455 311715811582688293266180683)
      ·
        refine ⟨467573717374032439899271025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311715811582688293266180683 467573717374032439899271025)
        ·
          refine ⟨350680288030524329924453269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467573717374032439899271025 350680288030524329924453269)
          ·
            refine ⟨16438138501430827965208747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350680288030524329924453269 16438138501430827965208747)
            ·
              refine ⟨24657207752146241947813121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16438138501430827965208747 24657207752146241947813121)
              ·
                refine ⟨18492905814109681460859841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24657207752146241947813121 18492905814109681460859841)
                ·
                  refine ⟨13869679360582261095644881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18492905814109681460859841 13869679360582261095644881)
                  ·
                    refine ⟨10402259520436695821733661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13869679360582261095644881 10402259520436695821733661)
                    ·
                      refine ⟨3900847320163760933150123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402259520436695821733661 3900847320163760933150123)
                      ·
                        rfl

theorem cell23_7596873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_7596873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596873 prefixEnd_7596873 := by exact prefixLift 7596873
  have htrace : WordTrace (prefixWord ++ tailWord_7596873) baseStart_7596873 baseEnd_7596873 := by
    simpa [prefixWord, tailWord_7596873, baseEnd_7596873] using wordTrace_append hprefix tailTrace_7596873
  have hstable : (prefixWord ++ tailWord_7596873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596873).length < 2 ^ (prefixWord ++ tailWord_7596873).sum := by decide
  have hdescent : baseEnd_7596873 < baseStart_7596873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596876 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 8]
def baseStart_7596876 : Nat := 118140960795 + 7596876 * 2 ^ 59
def prefixEnd_7596876 : Nat := 4983230072969 + 3 ^ 40 * 7596876 * 2
def baseEnd_7596876 : Nat := 433427651178413824601401

theorem tailTrace_7596876 : CollatzResearch.WordTrace tailWord_7596876 prefixEnd_7596876 433427651178413824601401 := by
  unfold tailWord_7596876
  simp only [CollatzResearch.WordTrace]
  refine ⟨138540415412911584985593241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184720553883882113314124321 138540415412911584985593241)
  ·
    refine ⟨103905311559683688739194931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138540415412911584985593241 103905311559683688739194931)
    ·
      refine ⟨155857967339525533108792397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103905311559683688739194931 155857967339525533108792397)
      ·
        refine ⟨58446737752322074915797149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155857967339525533108792397 58446737752322074915797149)
        ·
          refine ⟨21917526657120778093423931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58446737752322074915797149 21917526657120778093423931)
          ·
            refine ⟨32876289985681167140135897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21917526657120778093423931 32876289985681167140135897)
            ·
              refine ⟨24657217489260875355101923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32876289985681167140135897 24657217489260875355101923)
              ·
                refine ⟨36985826233891313032652885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24657217489260875355101923 36985826233891313032652885)
                ·
                  refine ⟨433427651178413824601401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36985826233891313032652885 433427651178413824601401)
                  ·
                    rfl

theorem cell23_7596876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_7596876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596876 prefixEnd_7596876 := by exact prefixLift 7596876
  have htrace : WordTrace (prefixWord ++ tailWord_7596876) baseStart_7596876 baseEnd_7596876 := by
    simpa [prefixWord, tailWord_7596876, baseEnd_7596876] using wordTrace_append hprefix tailTrace_7596876
  have hstable : (prefixWord ++ tailWord_7596876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596876).length < 2 ^ (prefixWord ++ tailWord_7596876).sum := by decide
  have hdescent : baseEnd_7596876 < baseStart_7596876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596937 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 1, 1, 3]
def baseStart_7596937 : Nat := 118140960795 + 7596937 * 2 ^ 59
def prefixEnd_7596937 : Nat := 4983230072969 + 3 ^ 40 * 7596937 * 2
def baseEnd_7596937 : Nat := 3900880182925648682749829

theorem tailTrace_7596937 : CollatzResearch.WordTrace tailWord_7596937 prefixEnd_7596937 3900880182925648682749829 := by
  unfold tailWord_7596937
  simp only [CollatzResearch.WordTrace]
  refine ⟨277083055678602177389157065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184722037119068118259438043 277083055678602177389157065)
  ·
    refine ⟨207812291758951633041867799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277083055678602177389157065 207812291758951633041867799)
    ·
      refine ⟨311718437638427449562801699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207812291758951633041867799 311718437638427449562801699)
      ·
        refine ⟨467577656457641174344202549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311718437638427449562801699 467577656457641174344202549)
        ·
          refine ⟨43835405292903860094768989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 467577656457641174344202549 43835405292903860094768989)
          ·
            refine ⟨16438276984838947535538371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43835405292903860094768989 16438276984838947535538371)
            ·
              refine ⟨24657415477258421303307557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16438276984838947535538371 24657415477258421303307557)
              ·
                refine ⟨4623265401985953994370167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24657415477258421303307557 4623265401985953994370167)
                ·
                  refine ⟨6934898102978930991555251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623265401985953994370167 6934898102978930991555251)
                  ·
                    refine ⟨10402347154468396487332877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934898102978930991555251 10402347154468396487332877)
                    ·
                      refine ⟨3900880182925648682749829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402347154468396487332877 3900880182925648682749829)
                      ·
                        rfl

theorem cell23_7596937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 1, 3].length) (baseStart_7596937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596937 prefixEnd_7596937 := by exact prefixLift 7596937
  have htrace : WordTrace (prefixWord ++ tailWord_7596937) baseStart_7596937 baseEnd_7596937 := by
    simpa [prefixWord, tailWord_7596937, baseEnd_7596937] using wordTrace_append hprefix tailTrace_7596937
  have hstable : (prefixWord ++ tailWord_7596937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596937).length < 2 ^ (prefixWord ++ tailWord_7596937).sum := by decide
  have hdescent : baseEnd_7596937 < baseStart_7596937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596960 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2]
def baseStart_7596960 : Nat := 118140960795 + 7596960 * 2 ^ 59
def prefixEnd_7596960 : Nat := 4983230072969 + 3 ^ 40 * 7596960 * 2
def baseEnd_7596960 : Nat := 3900891992980702092762223

theorem tailTrace_7596960 : CollatzResearch.WordTrace tailWord_7596960 prefixEnd_7596960 3900891992980702092762223 := by
  unfold tailWord_7596960
  simp only [CollatzResearch.WordTrace]
  refine ⟨138541947278759426158622167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184722596371679234878162889 138541947278759426158622167)
  ·
    refine ⟨207812920918139139237933251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138541947278759426158622167 207812920918139139237933251)
    ·
      refine ⟨311719381377208708856899877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207812920918139139237933251 311719381377208708856899877)
      ·
        refine ⟨58447384008226632910668727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311719381377208708856899877 58447384008226632910668727)
        ·
          refine ⟨87671076012339949366003091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58447384008226632910668727 87671076012339949366003091)
          ·
            refine ⟨131506614018509924049004637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87671076012339949366003091 131506614018509924049004637)
            ·
              refine ⟨49314980256941221518376739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131506614018509924049004637 49314980256941221518376739)
              ·
                refine ⟨73972470385411832277565109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49314980256941221518376739 73972470385411832277565109)
                ·
                  refine ⟨6934919098632359276021729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73972470385411832277565109 6934919098632359276021729)
                  ·
                    refine ⟨5201189323974269457016297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6934919098632359276021729 5201189323974269457016297)
                    ·
                      refine ⟨3900891992980702092762223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201189323974269457016297 3900891992980702092762223)
                      ·
                        rfl

theorem cell23_7596960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_7596960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596960 prefixEnd_7596960 := by exact prefixLift 7596960
  have htrace : WordTrace (prefixWord ++ tailWord_7596960) baseStart_7596960 baseEnd_7596960 := by
    simpa [prefixWord, tailWord_7596960, baseEnd_7596960] using wordTrace_append hprefix tailTrace_7596960
  have hstable : (prefixWord ++ tailWord_7596960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596960).length < 2 ^ (prefixWord ++ tailWord_7596960).sum := by decide
  have hdescent : baseEnd_7596960 < baseStart_7596960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7596963 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3]
def baseStart_7596963 : Nat := 118140960795 + 7596963 * 2 ^ 59
def prefixEnd_7596963 : Nat := 4983230072969 + 3 ^ 40 * 7596963 * 2
def baseEnd_7596963 : Nat := 3900893533422665581024709

theorem tailTrace_7596963 : CollatzResearch.WordTrace tailWord_7596963 prefixEnd_7596963 3900893533422665581024709 := by
  unfold tailWord_7596963
  simp only [CollatzResearch.WordTrace]
  refine ⟨277084003976507983829603543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184722669317671989219735695 277084003976507983829603543)
  ·
    refine ⟨415626005964761975744405315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277084003976507983829603543 415626005964761975744405315)
    ·
      refine ⟨623439008947142963616607973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415626005964761975744405315 623439008947142963616607973)
      ·
        refine ⟨116894814177589305678113995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623439008947142963616607973 116894814177589305678113995)
        ·
          refine ⟨175342221266383958517170993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116894814177589305678113995 175342221266383958517170993)
          ·
            refine ⟨131506665949787968887878245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175342221266383958517170993 131506665949787968887878245)
            ·
              refine ⟨24657499865585244166477171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131506665949787968887878245 24657499865585244166477171)
              ·
                refine ⟨36986249798377866249715757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24657499865585244166477171 36986249798377866249715757)
                ·
                  refine ⟨13869843674391699843643409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36986249798377866249715757 13869843674391699843643409)
                  ·
                    refine ⟨10402382755793774882732557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13869843674391699843643409 10402382755793774882732557)
                    ·
                      refine ⟨3900893533422665581024709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402382755793774882732557 3900893533422665581024709)
                      ·
                        rfl

theorem cell23_7596963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_7596963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7596963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7596963 prefixEnd_7596963 := by exact prefixLift 7596963
  have htrace : WordTrace (prefixWord ++ tailWord_7596963) baseStart_7596963 baseEnd_7596963 := by
    simpa [prefixWord, tailWord_7596963, baseEnd_7596963] using wordTrace_append hprefix tailTrace_7596963
  have hstable : (prefixWord ++ tailWord_7596963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7596963).length < 2 ^ (prefixWord ++ tailWord_7596963).sum := by decide
  have hdescent : baseEnd_7596963 < baseStart_7596963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7596963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597014 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7597014 : Nat := 118140960795 + 7597014 * 2 ^ 59
def prefixEnd_7597014 : Nat := 4983230072969 + 3 ^ 40 * 7597014 * 2
def baseEnd_7597014 : Nat := 3900919720936044881486975

theorem tailTrace_7597014 : CollatzResearch.WordTrace tailWord_7597014 prefixEnd_7597014 3900919720936044881486975 := by
  unfold tailWord_7597014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317866506207701221231881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184723909399548813026473397 17317866506207701221231881)
  ·
    refine ⟨12988399879655775915923911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17317866506207701221231881 12988399879655775915923911)
    ·
      refine ⟨19482599819483663873885867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12988399879655775915923911 19482599819483663873885867)
      ·
        refine ⟨29223899729225495810828801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19482599819483663873885867 29223899729225495810828801)
        ·
          refine ⟨21917924796919121858121601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29223899729225495810828801 21917924796919121858121601)
          ·
            refine ⟨16438443597689341393591201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21917924796919121858121601 16438443597689341393591201)
            ·
              refine ⟨12328832698267006045193401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16438443597689341393591201 12328832698267006045193401)
              ·
                refine ⟨9246624523700254533895051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12328832698267006045193401 9246624523700254533895051)
                ·
                  refine ⟨13869936785550381800842577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246624523700254533895051 13869936785550381800842577)
                  ·
                    refine ⟨10402452589162786350631933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13869936785550381800842577 10402452589162786350631933)
                    ·
                      refine ⟨3900919720936044881486975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402452589162786350631933 3900919720936044881486975)
                      ·
                        rfl

theorem cell23_7597014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7597014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597014 prefixEnd_7597014 := by exact prefixLift 7597014
  have htrace : WordTrace (prefixWord ++ tailWord_7597014) baseStart_7597014 baseEnd_7597014 := by
    simpa [prefixWord, tailWord_7597014, baseEnd_7597014] using wordTrace_append hprefix tailTrace_7597014
  have hstable : (prefixWord ++ tailWord_7597014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597014).length < 2 ^ (prefixWord ++ tailWord_7597014).sum := by decide
  have hdescent : baseEnd_7597014 < baseStart_7597014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597045 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7597045 : Nat := 118140960795 + 7597045 * 2 ^ 59
def prefixEnd_7597045 : Nat := 4983230072969 + 3 ^ 40 * 7597045 * 2
def baseEnd_7597045 : Nat := 3900935638836334260199333

theorem tailTrace_7597045 : CollatzResearch.WordTrace tailWord_7597045 prefixEnd_7597045 3900935638836334260199333 := by
  unfold tailWord_7597045
  simp only [CollatzResearch.WordTrace]
  refine ⟨277086994762210911834088589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184724663174807274556059059 277086994762210911834088589)
  ·
    refine ⟨103907623035829091937783221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277086994762210911834088589 103907623035829091937783221)
    ·
      refine ⟨9741339659608977369167177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103907623035829091937783221 9741339659608977369167177)
      ·
        refine ⟨7306004744706733026875383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9741339659608977369167177 7306004744706733026875383)
        ·
          refine ⟨10959007117060099540313075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306004744706733026875383 10959007117060099540313075)
          ·
            refine ⟨16438510675590149310469613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10959007117060099540313075 16438510675590149310469613)
            ·
              refine ⟨6164441503346305991426105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16438510675590149310469613 6164441503346305991426105)
              ·
                refine ⟨4623331127509729493569579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6164441503346305991426105 4623331127509729493569579)
                ·
                  refine ⟨6934996691264594240354369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623331127509729493569579 6934996691264594240354369)
                  ·
                    refine ⟨5201247518448445680265777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6934996691264594240354369 5201247518448445680265777)
                    ·
                      refine ⟨3900935638836334260199333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201247518448445680265777 3900935638836334260199333)
                      ·
                        rfl

theorem cell23_7597045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7597045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597045 prefixEnd_7597045 := by exact prefixLift 7597045
  have htrace : WordTrace (prefixWord ++ tailWord_7597045) baseStart_7597045 baseEnd_7597045 := by
    simpa [prefixWord, tailWord_7597045, baseEnd_7597045] using wordTrace_append hprefix tailTrace_7597045
  have hstable : (prefixWord ++ tailWord_7597045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597045).length < 2 ^ (prefixWord ++ tailWord_7597045).sum := by decide
  have hdescent : baseEnd_7597045 < baseStart_7597045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597053 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_7597053 : Nat := 118140960795 + 7597053 * 2 ^ 59
def prefixEnd_7597053 : Nat := 4983230072969 + 3 ^ 40 * 7597053 * 2
def baseEnd_7597053 : Nat := 3900939746681570228899295

theorem tailTrace_7597053 : CollatzResearch.WordTrace tailWord_7597053 prefixEnd_7597053 3900939746681570228899295 := by
  unfold tailWord_7597053
  simp only [CollatzResearch.WordTrace]
  refine ⟨277087286546181929200379813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184724857697454619466919875 277087286546181929200379813)
  ·
    refine ⟨51953866227409111725071215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277087286546181929200379813 51953866227409111725071215)
    ·
      refine ⟨77930799341113667587606823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51953866227409111725071215 77930799341113667587606823)
      ·
        refine ⟨116896199011670501381410235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77930799341113667587606823 116896199011670501381410235)
        ·
          refine ⟨175344298517505752072115353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116896199011670501381410235 175344298517505752072115353)
          ·
            refine ⟨131508223888129314054086515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175344298517505752072115353 131508223888129314054086515)
            ·
              refine ⟨197262335832193971081129773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131508223888129314054086515 197262335832193971081129773)
              ·
                refine ⟨73973375937072739155423665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197262335832193971081129773 73973375937072739155423665)
                ·
                  refine ⟨55480031952804554366567749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73973375937072739155423665 55480031952804554366567749)
                  ·
                    refine ⟨10402505991150853943731453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55480031952804554366567749 10402505991150853943731453)
                    ·
                      refine ⟨3900939746681570228899295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402505991150853943731453 3900939746681570228899295)
                      ·
                        rfl

theorem cell23_7597053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_7597053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597053 prefixEnd_7597053 := by exact prefixLift 7597053
  have htrace : WordTrace (prefixWord ++ tailWord_7597053) baseStart_7597053 baseEnd_7597053 := by
    simpa [prefixWord, tailWord_7597053, baseEnd_7597053] using wordTrace_append hprefix tailTrace_7597053
  have hstable : (prefixWord ++ tailWord_7597053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597053).length < 2 ^ (prefixWord ++ tailWord_7597053).sum := by decide
  have hdescent : baseEnd_7597053 < baseStart_7597053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597063 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7597063 : Nat := 118140960795 + 7597063 * 2 ^ 59
def prefixEnd_7597063 : Nat := 4983230072969 + 3 ^ 40 * 7597063 * 2
def baseEnd_7597063 : Nat := 3900944881488115189774249

theorem tailTrace_7597063 : CollatzResearch.WordTrace tailWord_7597063 prefixEnd_7597063 3900944881488115189774249 := by
  unfold tailWord_7597063
  simp only [CollatzResearch.WordTrace]
  refine ⟨277087651276145700908243843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184725100850763800605495895 277087651276145700908243843)
  ·
    refine ⟨415631476914218551362365765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277087651276145700908243843 415631476914218551362365765)
    ·
      refine ⟨77930901921415978380443581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415631476914218551362365765 77930901921415978380443581)
      ·
        refine ⟨29224088220530991892666343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77930901921415978380443581 29224088220530991892666343)
        ·
          refine ⟨43836132330796487838999515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29224088220530991892666343 43836132330796487838999515)
          ·
            refine ⟨65754198496194731758499273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43836132330796487838999515 65754198496194731758499273)
            ·
              refine ⟨49315648872146048818874455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65754198496194731758499273 49315648872146048818874455)
              ·
                refine ⟨73973473308219073228311683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49315648872146048818874455 73973473308219073228311683)
                ·
                  refine ⟨110960209962328609842467525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73973473308219073228311683 110960209962328609842467525)
                  ·
                    refine ⟨20805039367936614345462661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110960209962328609842467525 20805039367936614345462661)
                    ·
                      refine ⟨3900944881488115189774249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20805039367936614345462661 3900944881488115189774249)
                      ·
                        rfl

theorem cell23_7597063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7597063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597063 prefixEnd_7597063 := by exact prefixLift 7597063
  have htrace : WordTrace (prefixWord ++ tailWord_7597063) baseStart_7597063 baseEnd_7597063 := by
    simpa [prefixWord, tailWord_7597063, baseEnd_7597063] using wordTrace_append hprefix tailTrace_7597063
  have hstable : (prefixWord ++ tailWord_7597063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597063).length < 2 ^ (prefixWord ++ tailWord_7597063).sum := by decide
  have hdescent : baseEnd_7597063 < baseStart_7597063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597123 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_7597123 : Nat := 118140960795 + 7597123 * 2 ^ 59
def prefixEnd_7597123 : Nat := 4983230072969 + 3 ^ 40 * 7597123 * 2
def baseEnd_7597123 : Nat := 3900975690327384955023973

theorem tailTrace_7597123 : CollatzResearch.WordTrace tailWord_7597123 prefixEnd_7597123 3900975690327384955023973 := by
  unfold tailWord_7597123
  simp only [CollatzResearch.WordTrace]
  refine ⟨277089839655928331155428023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184726559770618887436952015 277089839655928331155428023)
  ·
    refine ⟨415634759483892496733142035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277089839655928331155428023 415634759483892496733142035)
    ·
      refine ⟨623452139225838745099713053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415634759483892496733142035 623452139225838745099713053)
      ·
        refine ⟨233794552209689529412392395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623452139225838745099713053 233794552209689529412392395)
        ·
          refine ⟨350691828314534294118588593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233794552209689529412392395 350691828314534294118588593)
          ·
            refine ⟨263018871235900720588941445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350691828314534294118588593 263018871235900720588941445)
            ·
              refine ⟨49316038356731385110426521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263018871235900720588941445 49316038356731385110426521)
              ·
                refine ⟨36987028767548538832819891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49316038356731385110426521 36987028767548538832819891)
                ·
                  refine ⟨55480543151322808249229837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36987028767548538832819891 55480543151322808249229837)
                  ·
                    refine ⟨20805203681746053093461189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55480543151322808249229837 20805203681746053093461189)
                    ·
                      refine ⟨3900975690327384955023973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20805203681746053093461189 3900975690327384955023973)
                      ·
                        rfl

theorem cell23_7597123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_7597123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597123 prefixEnd_7597123 := by exact prefixLift 7597123
  have htrace : WordTrace (prefixWord ++ tailWord_7597123) baseStart_7597123 baseEnd_7597123 := by
    simpa [prefixWord, tailWord_7597123, baseEnd_7597123] using wordTrace_append hprefix tailTrace_7597123
  have hstable : (prefixWord ++ tailWord_7597123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597123).length < 2 ^ (prefixWord ++ tailWord_7597123).sum := by decide
  have hdescent : baseEnd_7597123 < baseStart_7597123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597153 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7597153 : Nat := 118140960795 + 7597153 * 2 ^ 59
def prefixEnd_7597153 : Nat := 4983230072969 + 3 ^ 40 * 7597153 * 2
def baseEnd_7597153 : Nat := 3900991094747019837648835

theorem tailTrace_7597153 : CollatzResearch.WordTrace tailWord_7597153 prefixEnd_7597153 3900991094747019837648835 := by
  unfold tailWord_7597153
  simp only [CollatzResearch.WordTrace]
  refine ⟨277090933845819646279020113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184727289230546430852680075 277090933845819646279020113)
  ·
    refine ⟨207818200384364734709265085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277090933845819646279020113 207818200384364734709265085)
    ·
      refine ⟨77931825144136775515974407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207818200384364734709265085 77931825144136775515974407)
      ·
        refine ⟨116897737716205163273961611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77931825144136775515974407 116897737716205163273961611)
        ·
          refine ⟨175346606574307744910942417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116897737716205163273961611 175346606574307744910942417)
          ·
            refine ⟨131509954930730808683206813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175346606574307744910942417 131509954930730808683206813)
            ·
              refine ⟨49316233099024053256202555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131509954930730808683206813 49316233099024053256202555)
              ·
                refine ⟨73974349648536079884303833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49316233099024053256202555 73974349648536079884303833)
                ·
                  refine ⟨55480762236402059913227875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73974349648536079884303833 55480762236402059913227875)
                  ·
                    refine ⟨83221143354603089869841813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55480762236402059913227875 83221143354603089869841813)
                    ·
                      refine ⟨3900991094747019837648835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83221143354603089869841813 3900991094747019837648835)
                      ·
                        rfl

theorem cell23_7597153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7597153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597153 prefixEnd_7597153 := by exact prefixLift 7597153
  have htrace : WordTrace (prefixWord ++ tailWord_7597153) baseStart_7597153 baseEnd_7597153 := by
    simpa [prefixWord, tailWord_7597153, baseEnd_7597153] using wordTrace_append hprefix tailTrace_7597153
  have hstable : (prefixWord ++ tailWord_7597153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597153).length < 2 ^ (prefixWord ++ tailWord_7597153).sum := by decide
  have hdescent : baseEnd_7597153 < baseStart_7597153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597167 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 1, 4]
def baseStart_7597167 : Nat := 118140960795 + 7597167 * 2 ^ 59
def prefixEnd_7597167 : Nat := 4983230072969 + 3 ^ 40 * 7597167 * 2
def baseEnd_7597167 : Nat := 1300332761158727594291257

theorem tailTrace_7597167 : CollatzResearch.WordTrace tailWord_7597167 prefixEnd_7597167 1300332761158727594291257 := by
  unfold tailWord_7597167
  simp only [CollatzResearch.WordTrace]
  refine ⟨277091444467768926670029755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184727629645179284446686503 277091444467768926670029755)
  ·
    refine ⟨415637166701653390005044633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277091444467768926670029755 415637166701653390005044633)
    ·
      refine ⟨311727875026240042503783475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415637166701653390005044633 311727875026240042503783475)
      ·
        refine ⟨467591812539360063755675213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311727875026240042503783475 467591812539360063755675213)
        ·
          refine ⟨175346929702260023908378205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467591812539360063755675213 175346929702260023908378205)
          ·
            refine ⟨65755098638347508965641827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175346929702260023908378205 65755098638347508965641827)
            ·
              refine ⟨98632647957521263448462741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65755098638347508965641827 98632647957521263448462741)
              ·
                refine ⟨4623405373008809224146691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98632647957521263448462741 4623405373008809224146691)
                ·
                  refine ⟨6935108059513213836220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623405373008809224146691 6935108059513213836220037)
                  ·
                    refine ⟨1300332761158727594291257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935108059513213836220037 1300332761158727594291257)
                    ·
                      rfl

theorem cell23_7597167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 4].length) (baseStart_7597167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597167 prefixEnd_7597167 := by exact prefixLift 7597167
  have htrace : WordTrace (prefixWord ++ tailWord_7597167) baseStart_7597167 baseEnd_7597167 := by
    simpa [prefixWord, tailWord_7597167, baseEnd_7597167] using wordTrace_append hprefix tailTrace_7597167
  have hstable : (prefixWord ++ tailWord_7597167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597167).length < 2 ^ (prefixWord ++ tailWord_7597167).sum := by decide
  have hdescent : baseEnd_7597167 < baseStart_7597167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597218 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_7597218 : Nat := 118140960795 + 7597218 * 2 ^ 59
def prefixEnd_7597218 : Nat := 4983230072969 + 3 ^ 40 * 7597218 * 2
def baseEnd_7597218 : Nat := 1300341490329854027778679

theorem tailTrace_7597218 : CollatzResearch.WordTrace tailWord_7597218 prefixEnd_7597218 1300341490329854027778679 := by
  unfold tailWord_7597218
  simp only [CollatzResearch.WordTrace]
  refine ⟨69273326147646040595034077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184728869727056108253424205 69273326147646040595034077)
  ·
    refine ⟨25977497305367265223137779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69273326147646040595034077 25977497305367265223137779)
    ·
      refine ⟨38966245958050897834706669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25977497305367265223137779 38966245958050897834706669)
      ·
        refine ⟨14612342234269086688015001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38966245958050897834706669 14612342234269086688015001)
        ·
          refine ⟨10959256675701815016011251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14612342234269086688015001 10959256675701815016011251)
          ·
            refine ⟨16438885013552722524016877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10959256675701815016011251 16438885013552722524016877)
            ·
              refine ⟨6164581880082270946506329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16438885013552722524016877 6164581880082270946506329)
              ·
                refine ⟨4623436410061703209879747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6164581880082270946506329 4623436410061703209879747)
                ·
                  refine ⟨6935154615092554814819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623436410061703209879747 6935154615092554814819621)
                  ·
                    refine ⟨1300341490329854027778679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935154615092554814819621 1300341490329854027778679)
                    ·
                      rfl

theorem cell23_7597218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_7597218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597218 prefixEnd_7597218 := by exact prefixLift 7597218
  have htrace : WordTrace (prefixWord ++ tailWord_7597218) baseStart_7597218 baseEnd_7597218 := by
    simpa [prefixWord, tailWord_7597218, baseEnd_7597218] using wordTrace_append hprefix tailTrace_7597218
  have hstable : (prefixWord ++ tailWord_7597218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597218).length < 2 ^ (prefixWord ++ tailWord_7597218).sum := by decide
  have hdescent : baseEnd_7597218 < baseStart_7597218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597240 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_7597240 : Nat := 118140960795 + 7597240 * 2 ^ 59
def prefixEnd_7597240 : Nat := 4983230072969 + 3 ^ 40 * 7597240 * 2
def baseEnd_7597240 : Nat := 1300345255854653665753645

theorem tailTrace_7597240 : CollatzResearch.WordTrace tailWord_7597240 prefixEnd_7597240 1300345255854653665753645 := by
  unfold tailWord_7597240
  simp only [CollatzResearch.WordTrace]
  refine ⟨138547053498252230068718587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184729404664336306758291449 138547053498252230068718587)
  ·
    refine ⟨207820580247378345103077881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138547053498252230068718587 207820580247378345103077881)
    ·
      refine ⟨155865435185533758827308411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207820580247378345103077881 155865435185533758827308411)
      ·
        refine ⟨233798152778300638240962617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155865435185533758827308411 233798152778300638240962617)
        ·
          refine ⟨175348614583725478680721963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233798152778300638240962617 175348614583725478680721963)
          ·
            refine ⟨263022921875588218021082945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175348614583725478680721963 263022921875588218021082945)
            ·
              refine ⟨197267191406691163515812209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263022921875588218021082945 197267191406691163515812209)
              ·
                refine ⟨147950393555018372636859157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197267191406691163515812209 147950393555018372636859157)
                ·
                  refine ⟨6935174697891486217352773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147950393555018372636859157 6935174697891486217352773)
                  ·
                    refine ⟨1300345255854653665753645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935174697891486217352773 1300345255854653665753645)
                    ·
                      rfl

theorem cell23_7597240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_7597240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597240 prefixEnd_7597240 := by exact prefixLift 7597240
  have htrace : WordTrace (prefixWord ++ tailWord_7597240) baseStart_7597240 baseEnd_7597240 := by
    simpa [prefixWord, tailWord_7597240, baseEnd_7597240] using wordTrace_append hprefix tailTrace_7597240
  have hstable : (prefixWord ++ tailWord_7597240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597240).length < 2 ^ (prefixWord ++ tailWord_7597240).sum := by decide
  have hdescent : baseEnd_7597240 < baseStart_7597240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597244 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_7597244 : Nat := 118140960795 + 7597244 * 2 ^ 59
def prefixEnd_7597244 : Nat := 4983230072969 + 3 ^ 40 * 7597244 * 2
def baseEnd_7597244 : Nat := 1300345940495526327203639

theorem tailTrace_7597244 : CollatzResearch.WordTrace tailWord_7597244 prefixEnd_7597244 1300345940495526327203639 := by
  unfold tailWord_7597244
  simp only [CollatzResearch.WordTrace]
  refine ⟨138547126444244984410291393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184729501925659979213721857 138547126444244984410291393)
  ·
    refine ⟨103910344833183738307718545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138547126444244984410291393 103910344833183738307718545)
    ·
      refine ⟨77932758624887803730788909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103910344833183738307718545 77932758624887803730788909)
      ·
        refine ⟨29224784484332926399045841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77932758624887803730788909 29224784484332926399045841)
        ·
          refine ⟨21918588363249694799284381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29224784484332926399045841 21918588363249694799284381)
          ·
            refine ⟨8219470636218635549731643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21918588363249694799284381 8219470636218635549731643)
            ·
              refine ⟨12329205954327953324597465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219470636218635549731643 12329205954327953324597465)
              ·
                refine ⟨9246904465745964993448099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12329205954327953324597465 9246904465745964993448099)
                ·
                  refine ⟨13870356698618947490172149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246904465745964993448099 13870356698618947490172149)
                  ·
                    refine ⟨1300345940495526327203639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13870356698618947490172149 1300345940495526327203639)
                    ·
                      rfl

theorem cell23_7597244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_7597244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597244 prefixEnd_7597244 := by exact prefixLift 7597244
  have htrace : WordTrace (prefixWord ++ tailWord_7597244) baseStart_7597244 baseEnd_7597244 := by
    simpa [prefixWord, tailWord_7597244, baseEnd_7597244] using wordTrace_append hprefix tailTrace_7597244
  have hstable : (prefixWord ++ tailWord_7597244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597244).length < 2 ^ (prefixWord ++ tailWord_7597244).sum := by decide
  have hdescent : baseEnd_7597244 < baseStart_7597244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597247 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_7597247 : Nat := 118140960795 + 7597247 * 2 ^ 59
def prefixEnd_7597247 : Nat := 4983230072969 + 3 ^ 40 * 7597247 * 2
def baseEnd_7597247 : Nat := 3901039361928542469873403

theorem tailTrace_7597247 : CollatzResearch.WordTrace tailWord_7597247 prefixEnd_7597247 3901039361928542469873403 := by
  unfold tailWord_7597247
  simp only [CollatzResearch.WordTrace]
  refine ⟨277094362307479100332941995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184729574871652733555294663 277094362307479100332941995)
  ·
    refine ⟨415641543461218650499412993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277094362307479100332941995 415641543461218650499412993)
    ·
      refine ⟨311731157595913987874559745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415641543461218650499412993 311731157595913987874559745)
      ·
        refine ⟨233798368196935490905919809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311731157595913987874559745 233798368196935490905919809)
        ·
          refine ⟨175348776147701618179439857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233798368196935490905919809 175348776147701618179439857)
          ·
            refine ⟨131511582110776213634579893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175348776147701618179439857 131511582110776213634579893)
            ·
              refine ⟨12329210822885270028241865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131511582110776213634579893 12329210822885270028241865)
              ·
                refine ⟨9246908117163952521181399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12329210822885270028241865 9246908117163952521181399)
                ·
                  refine ⟨13870362175745928781772099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246908117163952521181399 13870362175745928781772099)
                  ·
                    refine ⟨20805543263618893172658149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13870362175745928781772099 20805543263618893172658149)
                    ·
                      refine ⟨3901039361928542469873403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20805543263618893172658149 3901039361928542469873403)
                      ·
                        rfl

theorem cell23_7597247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_7597247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597247 prefixEnd_7597247 := by exact prefixLift 7597247
  have htrace : WordTrace (prefixWord ++ tailWord_7597247) baseStart_7597247 baseEnd_7597247 := by
    simpa [prefixWord, tailWord_7597247, baseEnd_7597247] using wordTrace_append hprefix tailTrace_7597247
  have hstable : (prefixWord ++ tailWord_7597247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597247).length < 2 ^ (prefixWord ++ tailWord_7597247).sum := by decide
  have hdescent : baseEnd_7597247 < baseStart_7597247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597297 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_7597297 : Nat := 118140960795 + 7597297 * 2 ^ 59
def prefixEnd_7597297 : Nat := 4983230072969 + 3 ^ 40 * 7597297 * 2
def baseEnd_7597297 : Nat := 3901065035961267274248173

theorem tailTrace_7597297 : CollatzResearch.WordTrace tailWord_7597297 prefixEnd_7597297 3901065035961267274248173 := by
  unfold tailWord_7597297
  simp only [CollatzResearch.WordTrace]
  refine ⟨277096185957297958872262145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184730790638198639248174763 277096185957297958872262145)
  ·
    refine ⟨207822139467973469154196609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277096185957297958872262145 207822139467973469154196609)
    ·
      refine ⟨155866604600980101865647457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207822139467973469154196609 155866604600980101865647457)
      ·
        refine ⟨116899953450735076399235593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155866604600980101865647457 116899953450735076399235593)
        ·
          refine ⟨87674965088051307299426695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116899953450735076399235593 87674965088051307299426695)
          ·
            refine ⟨131512447632076960949140043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87674965088051307299426695 131512447632076960949140043)
            ·
              refine ⟨197268671448115441423710065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131512447632076960949140043 197268671448115441423710065)
              ·
                refine ⟨147951503586086581067782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197268671448115441423710065 147951503586086581067782549)
                ·
                  refine ⟨6935226730597808487552307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147951503586086581067782549 6935226730597808487552307)
                  ·
                    refine ⟨10402840095896712731328461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935226730597808487552307 10402840095896712731328461)
                    ·
                      refine ⟨3901065035961267274248173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10402840095896712731328461 3901065035961267274248173)
                      ·
                        rfl

theorem cell23_7597297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_7597297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597297 prefixEnd_7597297 := by exact prefixLift 7597297
  have htrace : WordTrace (prefixWord ++ tailWord_7597297) baseStart_7597297 baseEnd_7597297 := by
    simpa [prefixWord, tailWord_7597297, baseEnd_7597297] using wordTrace_append hprefix tailTrace_7597297
  have hstable : (prefixWord ++ tailWord_7597297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597297).length < 2 ^ (prefixWord ++ tailWord_7597297).sum := by decide
  have hdescent : baseEnd_7597297 < baseStart_7597297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597360 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 7]
def baseStart_7597360 : Nat := 118140960795 + 7597360 * 2 ^ 59
def prefixEnd_7597360 : Nat := 4983230072969 + 3 ^ 40 * 7597360 * 2
def baseEnd_7597360 : Nat := 433455265026944503084487

theorem tailTrace_7597360 : CollatzResearch.WordTrace tailWord_7597360 prefixEnd_7597360 433455265026944503084487 := by
  unfold tailWord_7597360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138549241878034860315902767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184732322504046480421203689 138549241878034860315902767)
  ·
    refine ⟨207823862817052290473854151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138549241878034860315902767 207823862817052290473854151)
    ·
      refine ⟨311735794225578435710781227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207823862817052290473854151 311735794225578435710781227)
      ·
        refine ⟨467603691338367653566171841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311735794225578435710781227 467603691338367653566171841)
        ·
          refine ⟨350702768503775740174628881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467603691338367653566171841 350702768503775740174628881)
          ·
            refine ⟨263027076377831805130971661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350702768503775740174628881 263027076377831805130971661)
            ·
              refine ⟨98635153641686926924114373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263027076377831805130971661 98635153641686926924114373)
              ·
                refine ⟨18494091307816298798271445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98635153641686926924114373 18494091307816298798271445)
                ·
                  refine ⟨433455265026944503084487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18494091307816298798271445 433455265026944503084487)
                  ·
                    rfl

theorem cell23_7597360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_7597360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597360 prefixEnd_7597360 := by exact prefixLift 7597360
  have htrace : WordTrace (prefixWord ++ tailWord_7597360) baseStart_7597360 baseEnd_7597360 := by
    simpa [prefixWord, tailWord_7597360, baseEnd_7597360] using wordTrace_append hprefix tailTrace_7597360
  have hstable : (prefixWord ++ tailWord_7597360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597360).length < 2 ^ (prefixWord ++ tailWord_7597360).sum := by decide
  have hdescent : baseEnd_7597360 < baseStart_7597360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597444 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7597444 : Nat := 118140960795 + 7597444 * 2 ^ 59
def prefixEnd_7597444 : Nat := 4983230072969 + 3 ^ 40 * 7597444 * 2
def baseEnd_7597444 : Nat := 3901140517617478199109997

theorem tailTrace_7597444 : CollatzResearch.WordTrace tailWord_7597444 prefixEnd_7597444 3901140517617478199109997 := by
  unfold tailWord_7597444
  simp only [CollatzResearch.WordTrace]
  refine ⟨138550773743882701488931693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184734364991843601985242257 138550773743882701488931693)
  ·
    refine ⟨51956540153956013058349385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138550773743882701488931693 51956540153956013058349385)
    ·
      refine ⟨38967405115467009793762039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51956540153956013058349385 38967405115467009793762039)
      ·
        refine ⟨58451107673200514690643059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38967405115467009793762039 58451107673200514690643059)
        ·
          refine ⟨87676661509800772035964589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58451107673200514690643059 87676661509800772035964589)
          ·
            refine ⟨32878748066175289513486721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87676661509800772035964589 32878748066175289513486721)
            ·
              refine ⟨24659061049631467135115041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32878748066175289513486721 24659061049631467135115041)
              ·
                refine ⟨18494295787223600351336281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24659061049631467135115041 18494295787223600351336281)
                ·
                  refine ⟨13870721840417700263502211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18494295787223600351336281 13870721840417700263502211)
                  ·
                    refine ⟨20806082760626550395253317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13870721840417700263502211 20806082760626550395253317)
                    ·
                      refine ⟨3901140517617478199109997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20806082760626550395253317 3901140517617478199109997)
                      ·
                        rfl

theorem cell23_7597444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7597444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597444 prefixEnd_7597444 := by exact prefixLift 7597444
  have htrace : WordTrace (prefixWord ++ tailWord_7597444) baseStart_7597444 baseEnd_7597444 := by
    simpa [prefixWord, tailWord_7597444, baseEnd_7597444] using wordTrace_append hprefix tailTrace_7597444
  have hstable : (prefixWord ++ tailWord_7597444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597444).length < 2 ^ (prefixWord ++ tailWord_7597444).sum := by decide
  have hdescent : baseEnd_7597444 < baseStart_7597444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597477 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_7597477 : Nat := 118140960795 + 7597477 * 2 ^ 59
def prefixEnd_7597477 : Nat := 4983230072969 + 3 ^ 40 * 7597477 * 2
def baseEnd_7597477 : Nat := 3901157462479076569997345

theorem tailTrace_7597477 : CollatzResearch.WordTrace tailWord_7597477 prefixEnd_7597477 3901157462479076569997345 := by
  unfold tailWord_7597477
  simp only [CollatzResearch.WordTrace]
  refine ⟨277102751096645849613814685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184735167397763899742543123 277102751096645849613814685)
  ·
    refine ⟨103913531661242193605180507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277102751096645849613814685 103913531661242193605180507)
    ·
      refine ⟨155870297491863290407770761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103913531661242193605180507 155870297491863290407770761)
      ·
        refine ⟨116902723118897467805828071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155870297491863290407770761 116902723118897467805828071)
        ·
          refine ⟨175354084678346201708742107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116902723118897467805828071 175354084678346201708742107)
          ·
            refine ⟨263031127017519302563113161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175354084678346201708742107 263031127017519302563113161)
            ·
              refine ⟨197273345263139476922334871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263031127017519302563113161 197273345263139476922334871)
              ·
                refine ⟨295910017894709215383502307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197273345263139476922334871 295910017894709215383502307)
                ·
                  refine ⟨443865026842063823075253461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295910017894709215383502307 443865026842063823075253461)
                  ·
                    refine ⟨10403086566610870853326253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 443865026842063823075253461 10403086566610870853326253)
                    ·
                      refine ⟨3901157462479076569997345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403086566610870853326253 3901157462479076569997345)
                      ·
                        rfl

theorem cell23_7597477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_7597477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597477 prefixEnd_7597477 := by exact prefixLift 7597477
  have htrace : WordTrace (prefixWord ++ tailWord_7597477) baseStart_7597477 baseEnd_7597477 := by
    simpa [prefixWord, tailWord_7597477, baseEnd_7597477] using wordTrace_append hprefix tailTrace_7597477
  have hstable : (prefixWord ++ tailWord_7597477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597477).length < 2 ^ (prefixWord ++ tailWord_7597477).sum := by decide
  have hdescent : baseEnd_7597477 < baseStart_7597477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597511 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_7597511 : Nat := 118140960795 + 7597511 * 2 ^ 59
def prefixEnd_7597511 : Nat := 4983230072969 + 3 ^ 40 * 7597511 * 2
def baseEnd_7597511 : Nat := 3901174920821329436972189

theorem tailTrace_7597511 : CollatzResearch.WordTrace tailWord_7597511 prefixEnd_7597511 3901174920821329436972189 := by
  unfold tailWord_7597511
  simp only [CollatzResearch.WordTrace]
  refine ⟨277103991178522673420552387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184735994119015115613701591 277103991178522673420552387)
  ·
    refine ⟨415655986767784010130828581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277103991178522673420552387 415655986767784010130828581)
    ·
      refine ⟨77935497518959501899530359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415655986767784010130828581 77935497518959501899530359)
      ·
        refine ⟨116903246278439252849295539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77935497518959501899530359 116903246278439252849295539)
        ·
          refine ⟨175354869417658879273943309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116903246278439252849295539 175354869417658879273943309)
          ·
            refine ⟨65758076031622079727728741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175354869417658879273943309 65758076031622079727728741)
            ·
              refine ⟨12329639255929139948949139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65758076031622079727728741 12329639255929139948949139)
              ·
                refine ⟨18494458883893709923423709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12329639255929139948949139 18494458883893709923423709)
                ·
                  refine ⟨6935422081460141221283891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18494458883893709923423709 6935422081460141221283891)
                  ·
                    refine ⟨10403133122190211831925837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935422081460141221283891 10403133122190211831925837)
                    ·
                      refine ⟨3901174920821329436972189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403133122190211831925837 3901174920821329436972189)
                      ·
                        rfl

theorem cell23_7597511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_7597511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597511 prefixEnd_7597511 := by exact prefixLift 7597511
  have htrace : WordTrace (prefixWord ++ tailWord_7597511) baseStart_7597511 baseEnd_7597511 := by
    simpa [prefixWord, tailWord_7597511, baseEnd_7597511] using wordTrace_append hprefix tailTrace_7597511
  have hstable : (prefixWord ++ tailWord_7597511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597511).length < 2 ^ (prefixWord ++ tailWord_7597511).sum := by decide
  have hdescent : baseEnd_7597511 < baseStart_7597511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597544 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7597544 : Nat := 118140960795 + 7597544 * 2 ^ 59
def prefixEnd_7597544 : Nat := 4983230072969 + 3 ^ 40 * 7597544 * 2
def baseEnd_7597544 : Nat := 1300397288560975935953179

theorem tailTrace_7597544 : CollatzResearch.WordTrace tailWord_7597544 prefixEnd_7597544 1300397288560975935953179 := by
  unfold tailWord_7597544
  simp only [CollatzResearch.WordTrace]
  refine ⟨138552597393701560028251843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184736796524935413371002457 138552597393701560028251843)
  ·
    refine ⟨207828896090552340042377765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138552597393701560028251843 207828896090552340042377765)
    ·
      refine ⟨38967918016978563757945831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207828896090552340042377765 38967918016978563757945831)
      ·
        refine ⟨58451877025467845636918747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38967918016978563757945831 58451877025467845636918747)
        ·
          refine ⟨87677815538201768455378121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58451877025467845636918747 87677815538201768455378121)
          ·
            refine ⟨65758361653651326341533591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87677815538201768455378121 65758361653651326341533591)
            ·
              refine ⟨98637542480476989512300387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65758361653651326341533591 98637542480476989512300387)
              ·
                refine ⟨147956313720715484268450581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98637542480476989512300387 147956313720715484268450581)
                ·
                  refine ⟨6935452205658538325083621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147956313720715484268450581 6935452205658538325083621)
                  ·
                    refine ⟨1300397288560975935953179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935452205658538325083621 1300397288560975935953179)
                    ·
                      rfl

theorem cell23_7597544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7597544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597544 prefixEnd_7597544 := by exact prefixLift 7597544
  have htrace : WordTrace (prefixWord ++ tailWord_7597544) baseStart_7597544 baseEnd_7597544 := by
    simpa [prefixWord, tailWord_7597544, baseEnd_7597544] using wordTrace_append hprefix tailTrace_7597544
  have hstable : (prefixWord ++ tailWord_7597544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597544).length < 2 ^ (prefixWord ++ tailWord_7597544).sum := by decide
  have hdescent : baseEnd_7597544 < baseStart_7597544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597551 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 5, 2, 2]
def baseStart_7597551 : Nat := 118140960795 + 7597551 * 2 ^ 59
def prefixEnd_7597551 : Nat := 4983230072969 + 3 ^ 40 * 7597551 * 2
def baseEnd_7597551 : Nat := 3901195460047509280472005

theorem tailTrace_7597551 : CollatzResearch.WordTrace tailWord_7597551 prefixEnd_7597551 3901195460047509280472005 := by
  unfold tailWord_7597551
  simp only [CollatzResearch.WordTrace]
  refine ⟨277105450098377760252008507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184736966732251840168005671 277105450098377760252008507)
  ·
    refine ⟨415658175147566640378012761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277105450098377760252008507 415658175147566640378012761)
    ·
      refine ⟨311743631360674980283509571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415658175147566640378012761 311743631360674980283509571)
      ·
        refine ⟨467615447041012470425264357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311743631360674980283509571 467615447041012470425264357)
        ·
          refine ⟨87677896320189838204737067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467615447041012470425264357 87677896320189838204737067)
          ·
            refine ⟨131516844480284757307105601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87677896320189838204737067 131516844480284757307105601)
            ·
              refine ⟨98637633360213567980329201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131516844480284757307105601 98637633360213567980329201)
              ·
                refine ⟨73978225020160175985246901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98637633360213567980329201 73978225020160175985246901)
                ·
                  refine ⟨6935458595640016498616897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73978225020160175985246901 6935458595640016498616897)
                  ·
                    refine ⟨5201593946730012373962673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6935458595640016498616897 5201593946730012373962673)
                    ·
                      refine ⟨3901195460047509280472005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201593946730012373962673 3901195460047509280472005)
                      ·
                        rfl

theorem cell23_7597551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2, 2].length) (baseStart_7597551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597551 prefixEnd_7597551 := by exact prefixLift 7597551
  have htrace : WordTrace (prefixWord ++ tailWord_7597551) baseStart_7597551 baseEnd_7597551 := by
    simpa [prefixWord, tailWord_7597551, baseEnd_7597551] using wordTrace_append hprefix tailTrace_7597551
  have hstable : (prefixWord ++ tailWord_7597551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597551).length < 2 ^ (prefixWord ++ tailWord_7597551).sum := by decide
  have hdescent : baseEnd_7597551 < baseStart_7597551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597577 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_7597577 : Nat := 118140960795 + 7597577 * 2 ^ 59
def prefixEnd_7597577 : Nat := 4983230072969 + 3 ^ 40 * 7597577 * 2
def baseEnd_7597577 : Nat := 3901208810544526178746885

theorem tailTrace_7597577 : CollatzResearch.WordTrace tailWord_7597577 prefixEnd_7597577 3901208810544526178746885 := by
  unfold tailWord_7597577
  simp only [CollatzResearch.WordTrace]
  refine ⟨277106398396283566692454985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184737598930855711128303323 277106398396283566692454985)
  ·
    refine ⟨207829798797212675019341239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277106398396283566692454985 207829798797212675019341239)
    ·
      refine ⟨311744698195819012529011859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207829798797212675019341239 311744698195819012529011859)
      ·
        refine ⟨467617047293728518793517789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311744698195819012529011859 467617047293728518793517789)
        ·
          refine ⟨175356392735148194547569171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467617047293728518793517789 175356392735148194547569171)
          ·
            refine ⟨263034589102722291821353757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175356392735148194547569171 263034589102722291821353757)
            ·
              refine ⟨98637970913520859433007659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263034589102722291821353757 98637970913520859433007659)
              ·
                refine ⟨147956956370281289149511489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98637970913520859433007659 147956956370281289149511489)
                ·
                  refine ⟨110967717277710966862133617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147956956370281289149511489 110967717277710966862133617)
                  ·
                    refine ⟨83225787958283225146600213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110967717277710966862133617 83225787958283225146600213)
                    ·
                      refine ⟨3901208810544526178746885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83225787958283225146600213 3901208810544526178746885)
                      ·
                        rfl

theorem cell23_7597577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_7597577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597577 prefixEnd_7597577 := by exact prefixLift 7597577
  have htrace : WordTrace (prefixWord ++ tailWord_7597577) baseStart_7597577 baseEnd_7597577 := by
    simpa [prefixWord, tailWord_7597577, baseEnd_7597577] using wordTrace_append hprefix tailTrace_7597577
  have hstable : (prefixWord ++ tailWord_7597577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597577).length < 2 ^ (prefixWord ++ tailWord_7597577).sum := by decide
  have hdescent : baseEnd_7597577 < baseStart_7597577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597578 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_7597578 : Nat := 118140960795 + 7597578 * 2 ^ 59
def prefixEnd_7597578 : Nat := 4983230072969 + 3 ^ 40 * 7597578 * 2
def baseEnd_7597578 : Nat := 1300403108008393558278127

theorem tailTrace_7597578 : CollatzResearch.WordTrace tailWord_7597578 prefixEnd_7597578 1300403108008393558278127 := by
  unfold tailWord_7597578
  simp only [CollatzResearch.WordTrace]
  refine ⟨69276608717319985965810347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184737623246186629242160925 69276608717319985965810347)
  ·
    refine ⟨103914913075979978948715521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69276608717319985965810347 103914913075979978948715521)
    ·
      refine ⟨77936184806984984211536641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103914913075979978948715521 77936184806984984211536641)
      ·
        refine ⟨58452138605238738158652481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77936184806984984211536641 58452138605238738158652481)
        ·
          refine ⟨43839103953929053618989361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58452138605238738158652481 43839103953929053618989361)
          ·
            refine ⟨32879327965446790214242021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43839103953929053618989361 32879327965446790214242021)
            ·
              refine ⟨6164873993521273165170379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32879327965446790214242021 6164873993521273165170379)
              ·
                refine ⟨9247310990281909747755569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164873993521273165170379 9247310990281909747755569)
                ·
                  refine ⟨6935483242711432310816677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9247310990281909747755569 6935483242711432310816677)
                  ·
                    refine ⟨1300403108008393558278127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935483242711432310816677 1300403108008393558278127)
                    ·
                      rfl

theorem cell23_7597578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_7597578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597578 prefixEnd_7597578 := by exact prefixLift 7597578
  have htrace : WordTrace (prefixWord ++ tailWord_7597578) baseStart_7597578 baseEnd_7597578 := by
    simpa [prefixWord, tailWord_7597578, baseEnd_7597578] using wordTrace_append hprefix tailTrace_7597578
  have hstable : (prefixWord ++ tailWord_7597578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597578).length < 2 ^ (prefixWord ++ tailWord_7597578).sum := by decide
  have hdescent : baseEnd_7597578 < baseStart_7597578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597601 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7597601 : Nat := 118140960795 + 7597601 * 2 ^ 59
def prefixEnd_7597601 : Nat := 4983230072969 + 3 ^ 40 * 7597601 * 2
def baseEnd_7597601 : Nat := 3901221134080234084846775

theorem tailTrace_7597601 : CollatzResearch.WordTrace tailWord_7597601 prefixEnd_7597601 3901221134080234084846775 := by
  unfold tailWord_7597601
  simp only [CollatzResearch.WordTrace]
  refine ⟨277107273748196618791328657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184738182498797745860885771 277107273748196618791328657)
  ·
    refine ⟨207830455311147464093496493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277107273748196618791328657 207830455311147464093496493)
    ·
      refine ⟨77936420741680299035061185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207830455311147464093496493 77936420741680299035061185)
      ·
        refine ⟨58452315556260224276295889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77936420741680299035061185 58452315556260224276295889)
        ·
          refine ⟨43839236667195168207221917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58452315556260224276295889 43839236667195168207221917)
          ·
            refine ⟨16439713750198188077708219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43839236667195168207221917 16439713750198188077708219)
            ·
              refine ⟨24659570625297282116562329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16439713750198188077708219 24659570625297282116562329)
              ·
                refine ⟨18494677968972961587421747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24659570625297282116562329 18494677968972961587421747)
                ·
                  refine ⟨27742016953459442381132621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18494677968972961587421747 27742016953459442381132621)
                  ·
                    refine ⟨10403256357547290892924733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27742016953459442381132621 10403256357547290892924733)
                    ·
                      refine ⟨3901221134080234084846775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403256357547290892924733 3901221134080234084846775)
                      ·
                        rfl

theorem cell23_7597601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7597601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597601 prefixEnd_7597601 := by exact prefixLift 7597601
  have htrace : WordTrace (prefixWord ++ tailWord_7597601) baseStart_7597601 baseEnd_7597601 := by
    simpa [prefixWord, tailWord_7597601, baseEnd_7597601] using wordTrace_append hprefix tailTrace_7597601
  have hstable : (prefixWord ++ tailWord_7597601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597601).length < 2 ^ (prefixWord ++ tailWord_7597601).sum := by decide
  have hdescent : baseEnd_7597601 < baseStart_7597601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597624 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_7597624 : Nat := 118140960795 + 7597624 * 2 ^ 59
def prefixEnd_7597624 : Nat := 4983230072969 + 3 ^ 40 * 7597624 * 2
def baseEnd_7597624 : Nat := 3901232944135287494859169

theorem tailTrace_7597624 : CollatzResearch.WordTrace tailWord_7597624 prefixEnd_7597624 3901232944135287494859169 := by
  unfold tailWord_7597624
  simp only [CollatzResearch.WordTrace]
  refine ⟨138554056313556646859707963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184738741751408862479610617 138554056313556646859707963)
  ·
    refine ⟨207831084470334970289561945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138554056313556646859707963 207831084470334970289561945)
    ·
      refine ⟨155873313352751227717171459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207831084470334970289561945 155873313352751227717171459)
      ·
        refine ⟨233809970029126841575757189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155873313352751227717171459 233809970029126841575757189)
        ·
          refine ⟨43839369380461282795454473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233809970029126841575757189 43839369380461282795454473)
          ·
            refine ⟨32879527035345962096590855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43839369380461282795454473 32879527035345962096590855)
            ·
              refine ⟨49319290553018943144886283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32879527035345962096590855 49319290553018943144886283)
              ·
                refine ⟨73978935829528414717329425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49319290553018943144886283 73978935829528414717329425)
                ·
                  refine ⟨55484201872146311037997069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73978935829528414717329425 55484201872146311037997069)
                  ·
                    refine ⟨20806575702054866639248901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55484201872146311037997069 20806575702054866639248901)
                    ·
                      refine ⟨3901232944135287494859169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20806575702054866639248901 3901232944135287494859169)
                      ·
                        rfl

theorem cell23_7597624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_7597624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597624 prefixEnd_7597624 := by exact prefixLift 7597624
  have htrace : WordTrace (prefixWord ++ tailWord_7597624) baseStart_7597624 baseEnd_7597624 := by
    simpa [prefixWord, tailWord_7597624, baseEnd_7597624] using wordTrace_append hprefix tailTrace_7597624
  have hstable : (prefixWord ++ tailWord_7597624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597624).length < 2 ^ (prefixWord ++ tailWord_7597624).sum := by decide
  have hdescent : baseEnd_7597624 < baseStart_7597624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597731 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4]
def baseStart_7597731 : Nat := 118140960795 + 7597731 * 2 ^ 59
def prefixEnd_7597731 : Nat := 4983230072969 + 3 ^ 40 * 7597731 * 2
def baseEnd_7597731 : Nat := 3901287886565318576221177

theorem tailTrace_7597731 : CollatzResearch.WordTrace tailWord_7597731 prefixEnd_7597731 3901287886565318576221177 := by
  unfold tailWord_7597731
  simp only [CollatzResearch.WordTrace]
  refine ⟨277112015237725650993561047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184741343491817100662374031 277112015237725650993561047)
  ·
    refine ⟨415668022856588476490341571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277112015237725650993561047 415668022856588476490341571)
    ·
      refine ⟨623502034284882714735512357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415668022856588476490341571 623502034284882714735512357)
      ·
        refine ⟨116906631428415509012908567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623502034284882714735512357 116906631428415509012908567)
        ·
          refine ⟨175359947142623263519362851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116906631428415509012908567 175359947142623263519362851)
          ·
            refine ⟨263039920713934895279044277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175359947142623263519362851 263039920713934895279044277)
            ·
              refine ⟨24659992566931396432410401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263039920713934895279044277 24659992566931396432410401)
              ·
                refine ⟨18494994425198547324307801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24659992566931396432410401 18494994425198547324307801)
                ·
                  refine ⟨13871245818898910493230851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18494994425198547324307801 13871245818898910493230851)
                  ·
                    refine ⟨20806868728348365739846277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13871245818898910493230851 20806868728348365739846277)
                    ·
                      refine ⟨3901287886565318576221177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20806868728348365739846277 3901287886565318576221177)
                      ·
                        rfl

theorem cell23_7597731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_7597731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597731 prefixEnd_7597731 := by exact prefixLift 7597731
  have htrace : WordTrace (prefixWord ++ tailWord_7597731) baseStart_7597731 baseEnd_7597731 := by
    simpa [prefixWord, tailWord_7597731, baseEnd_7597731] using wordTrace_append hprefix tailTrace_7597731
  have hstable : (prefixWord ++ tailWord_7597731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597731).length < 2 ^ (prefixWord ++ tailWord_7597731).sum := by decide
  have hdescent : baseEnd_7597731 < baseStart_7597731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597744 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_7597744 : Nat := 118140960795 + 7597744 * 2 ^ 59
def prefixEnd_7597744 : Nat := 4983230072969 + 3 ^ 40 * 7597744 * 2
def baseEnd_7597744 : Nat := 3901294561813827025358617

theorem tailTrace_7597744 : CollatzResearch.WordTrace tailWord_7597744 prefixEnd_7597744 3901294561813827025358617 := by
  unfold tailWord_7597744
  simp only [CollatzResearch.WordTrace]
  refine ⟨138556244693339277106892143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184741659591119036142522857 138556244693339277106892143)
  ·
    refine ⟨207834367040008915660338215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138556244693339277106892143 207834367040008915660338215)
    ·
      refine ⟨311751550560013373490507323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207834367040008915660338215 311751550560013373490507323)
      ·
        refine ⟨467627325840020060235760985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311751550560013373490507323 467627325840020060235760985)
        ·
          refine ⟨350720494380015045176820739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467627325840020060235760985 350720494380015045176820739)
          ·
            refine ⟨526080741570022567765231109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350720494380015045176820739 526080741570022567765231109)
            ·
              refine ⟨98640139044379231455980833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526080741570022567765231109 98640139044379231455980833)
              ·
                refine ⟨73980104283284423591985625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98640139044379231455980833 73980104283284423591985625)
                ·
                  refine ⟨55485078212463317693989219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73980104283284423591985625 55485078212463317693989219)
                  ·
                    refine ⟨83227617318694976540983829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55485078212463317693989219 83227617318694976540983829)
                    ·
                      refine ⟨3901294561813827025358617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83227617318694976540983829 3901294561813827025358617)
                      ·
                        rfl

theorem cell23_7597744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_7597744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597744 prefixEnd_7597744 := by exact prefixLift 7597744
  have htrace : WordTrace (prefixWord ++ tailWord_7597744) baseStart_7597744 baseEnd_7597744 := by
    simpa [prefixWord, tailWord_7597744, baseEnd_7597744] using wordTrace_append hprefix tailTrace_7597744
  have hstable : (prefixWord ++ tailWord_7597744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597744).length < 2 ^ (prefixWord ++ tailWord_7597744).sum := by decide
  have hdescent : baseEnd_7597744 < baseStart_7597744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597768 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_7597768 : Nat := 118140960795 + 7597768 * 2 ^ 59
def prefixEnd_7597768 : Nat := 4983230072969 + 3 ^ 40 * 7597768 * 2
def baseEnd_7597768 : Nat := 3901306885349534931458507

theorem tailTrace_7597768 : CollatzResearch.WordTrace tailWord_7597768 prefixEnd_7597768 3901306885349534931458507 := by
  unfold tailWord_7597768
  simp only [CollatzResearch.WordTrace]
  refine ⟨138556682369295803156328979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184742243159061070875105305 138556682369295803156328979)
  ·
    refine ⟨207835023553943704734493469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138556682369295803156328979 207835023553943704734493469)
    ·
      refine ⟨77938133832728889275435051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207835023553943704734493469 77938133832728889275435051)
      ·
        refine ⟨116907200749093333913152577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77938133832728889275435051 116907200749093333913152577)
        ·
          refine ⟨87680400561820000434864433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116907200749093333913152577 87680400561820000434864433)
          ·
            refine ⟨65760300421365000326148325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87680400561820000434864433 65760300421365000326148325)
            ·
              refine ⟨12330056329005937561152811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65760300421365000326148325 12330056329005937561152811)
              ·
                refine ⟨18495084493508906341729217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330056329005937561152811 18495084493508906341729217)
                ·
                  refine ⟨13871313370131679756296913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18495084493508906341729217 13871313370131679756296913)
                  ·
                    refine ⟨10403485027598759817222685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13871313370131679756296913 10403485027598759817222685)
                    ·
                      refine ⟨3901306885349534931458507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403485027598759817222685 3901306885349534931458507)
                      ·
                        rfl

theorem cell23_7597768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_7597768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597768 prefixEnd_7597768 := by exact prefixLift 7597768
  have htrace : WordTrace (prefixWord ++ tailWord_7597768) baseStart_7597768 baseEnd_7597768 := by
    simpa [prefixWord, tailWord_7597768, baseEnd_7597768] using wordTrace_append hprefix tailTrace_7597768
  have hstable : (prefixWord ++ tailWord_7597768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597768).length < 2 ^ (prefixWord ++ tailWord_7597768).sum := by decide
  have hdescent : baseEnd_7597768 < baseStart_7597768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597825 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_7597825 : Nat := 118140960795 + 7597825 * 2 ^ 59
def prefixEnd_7597825 : Nat := 4983230072969 + 3 ^ 40 * 7597825 * 2
def baseEnd_7597825 : Nat := 3901336153746841208445745

theorem tailTrace_7597825 : CollatzResearch.WordTrace tailWord_7597825 prefixEnd_7597825 3901336153746841208445745 := by
  unfold tailWord_7597825
  simp only [CollatzResearch.WordTrace]
  refine ⟨277115443699385105047482929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184743629132923403364988619 277115443699385105047482929)
  ·
    refine ⟨207836582774538828785612197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277115443699385105047482929 207836582774538828785612197)
    ·
      refine ⟨38969359270226030397302287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207836582774538828785612197 38969359270226030397302287)
      ·
        refine ⟨58454038905339045595953431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38969359270226030397302287 58454038905339045595953431)
        ·
          refine ⟨87681058358008568393930147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58454038905339045595953431 87681058358008568393930147)
          ·
            refine ⟨131521587537012852590895221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87681058358008568393930147 131521587537012852590895221)
            ·
              refine ⟨12330148831594954930396427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131521587537012852590895221 12330148831594954930396427)
              ·
                refine ⟨18495223247392432395594641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330148831594954930396427 18495223247392432395594641)
                ·
                  refine ⟨13871417435544324296695981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18495223247392432395594641 13871417435544324296695981)
                  ·
                    refine ⟨5201781538329121611260993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13871417435544324296695981 5201781538329121611260993)
                    ·
                      refine ⟨3901336153746841208445745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201781538329121611260993 3901336153746841208445745)
                      ·
                        rfl

theorem cell23_7597825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_7597825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597825 prefixEnd_7597825 := by exact prefixLift 7597825
  have htrace : WordTrace (prefixWord ++ tailWord_7597825) baseStart_7597825 baseEnd_7597825 := by
    simpa [prefixWord, tailWord_7597825, baseEnd_7597825] using wordTrace_append hprefix tailTrace_7597825
  have hstable : (prefixWord ++ tailWord_7597825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597825).length < 2 ^ (prefixWord ++ tailWord_7597825).sum := by decide
  have hdescent : baseEnd_7597825 < baseStart_7597825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597832 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_7597832 : Nat := 118140960795 + 7597832 * 2 ^ 59
def prefixEnd_7597832 : Nat := 4983230072969 + 3 ^ 40 * 7597832 * 2
def baseEnd_7597832 : Nat := 3901339748111422681058213

theorem tailTrace_7597832 : CollatzResearch.WordTrace tailWord_7597832 prefixEnd_7597832 3901339748111422681058213 := by
  unfold tailWord_7597832
  simp only [CollatzResearch.WordTrace]
  refine ⟨138557849505179872621493875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184743799340239830161991833 138557849505179872621493875)
  ·
    refine ⟨207836774257769808932240813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138557849505179872621493875 207836774257769808932240813)
    ·
      refine ⟨77938790346663678349590305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207836774257769808932240813 77938790346663678349590305)
      ·
        refine ⟨58454092759997758762192729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77938790346663678349590305 58454092759997758762192729)
        ·
          refine ⟨43840569569998319071644547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58454092759997758762192729 43840569569998319071644547)
          ·
            refine ⟨65760854354997478607466821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43840569569998319071644547 65760854354997478607466821)
            ·
              refine ⟨12330160191562027238900029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65760854354997478607466821 12330160191562027238900029)
              ·
                refine ⟨4623810071835760214587511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12330160191562027238900029 4623810071835760214587511)
                ·
                  refine ⟨6935715107753640321881267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623810071835760214587511 6935715107753640321881267)
                  ·
                    refine ⟨10403572661630460482821901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935715107753640321881267 10403572661630460482821901)
                    ·
                      refine ⟨3901339748111422681058213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403572661630460482821901 3901339748111422681058213)
                      ·
                        rfl

theorem cell23_7597832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_7597832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597832 prefixEnd_7597832 := by exact prefixLift 7597832
  have htrace : WordTrace (prefixWord ++ tailWord_7597832) baseStart_7597832 baseEnd_7597832 := by
    simpa [prefixWord, tailWord_7597832, baseEnd_7597832] using wordTrace_append hprefix tailTrace_7597832
  have hstable : (prefixWord ++ tailWord_7597832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597832).length < 2 ^ (prefixWord ++ tailWord_7597832).sum := by decide
  have hdescent : baseEnd_7597832 < baseStart_7597832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597841 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_7597841 : Nat := 118140960795 + 7597841 * 2 ^ 59
def prefixEnd_7597841 : Nat := 4983230072969 + 3 ^ 40 * 7597841 * 2
def baseEnd_7597841 : Nat := 3901344369437313145845671

theorem tailTrace_7597841 : CollatzResearch.WordTrace tailWord_7597841 prefixEnd_7597841 3901344369437313145845671 := by
  unfold tailWord_7597841
  simp only [CollatzResearch.WordTrace]
  refine ⟨277116027267327139780065377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184744018178218093186710251 277116027267327139780065377)
  ·
    refine ⟨207837020450495354835049033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277116027267327139780065377 207837020450495354835049033)
    ·
      refine ⟨155877765337871516126286775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207837020450495354835049033 155877765337871516126286775)
      ·
        refine ⟨233816648006807274189430163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155877765337871516126286775 233816648006807274189430163)
        ·
          refine ⟨350724972010210911284145245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233816648006807274189430163 350724972010210911284145245)
          ·
            refine ⟨131521864503829091731554467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350724972010210911284145245 131521864503829091731554467)
            ·
              refine ⟨197282796755743637597331701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131521864503829091731554467 197282796755743637597331701)
              ·
                refine ⟨18495262195850966024749847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197282796755743637597331701 18495262195850966024749847)
                ·
                  refine ⟨27742893293776449037124771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18495262195850966024749847 27742893293776449037124771)
                  ·
                    refine ⟨41614339940664673555687157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27742893293776449037124771 41614339940664673555687157)
                    ·
                      refine ⟨3901344369437313145845671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41614339940664673555687157 3901344369437313145845671)
                      ·
                        rfl

theorem cell23_7597841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_7597841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597841 prefixEnd_7597841 := by exact prefixLift 7597841
  have htrace : WordTrace (prefixWord ++ tailWord_7597841) baseStart_7597841 baseEnd_7597841 := by
    simpa [prefixWord, tailWord_7597841, baseEnd_7597841] using wordTrace_append hprefix tailTrace_7597841
  have hstable : (prefixWord ++ tailWord_7597841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597841).length < 2 ^ (prefixWord ++ tailWord_7597841).sum := by decide
  have hdescent : baseEnd_7597841 < baseStart_7597841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597858 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7597858 : Nat := 118140960795 + 7597858 * 2 ^ 59
def prefixEnd_7597858 : Nat := 4983230072969 + 3 ^ 40 * 7597858 * 2
def baseEnd_7597858 : Nat := 3901353098608439579333093

theorem tailTrace_7597858 : CollatzResearch.WordTrace tailWord_7597858 prefixEnd_7597858 3901353098608439579333093 := by
  unfold tailWord_7597858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69279161827066387920858557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184744431538843701122289485 69279161827066387920858557)
  ·
    refine ⟨25979685685149895470321959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69279161827066387920858557 25979685685149895470321959)
    ·
      refine ⟨38969528527724843205482939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25979685685149895470321959 38969528527724843205482939)
      ·
        refine ⟨58454292791587264808224409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38969528527724843205482939 58454292791587264808224409)
        ·
          refine ⟨43840719593690448606168307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58454292791587264808224409 43840719593690448606168307)
          ·
            refine ⟨65761079390535672909252461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43840719593690448606168307 65761079390535672909252461)
            ·
              refine ⟨24660404771450877340969673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65761079390535672909252461 24660404771450877340969673)
              ·
                refine ⟨18495303578588158005727255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24660404771450877340969673 18495303578588158005727255)
                ·
                  refine ⟨27742955367882237008590883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18495303578588158005727255 27742955367882237008590883)
                  ·
                    refine ⟨41614433051823355512886325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27742955367882237008590883 41614433051823355512886325)
                    ·
                      refine ⟨3901353098608439579333093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41614433051823355512886325 3901353098608439579333093)
                      ·
                        rfl

theorem cell23_7597858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7597858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597858 prefixEnd_7597858 := by exact prefixLift 7597858
  have htrace : WordTrace (prefixWord ++ tailWord_7597858) baseStart_7597858 baseEnd_7597858 := by
    simpa [prefixWord, tailWord_7597858, baseEnd_7597858] using wordTrace_append hprefix tailTrace_7597858
  have hstable : (prefixWord ++ tailWord_7597858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597858).length < 2 ^ (prefixWord ++ tailWord_7597858).sum := by decide
  have hdescent : baseEnd_7597858 < baseStart_7597858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597868 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_7597868 : Nat := 118140960795 + 7597868 * 2 ^ 59
def prefixEnd_7597868 : Nat := 4983230072969 + 3 ^ 40 * 7597868 * 2
def baseEnd_7597868 : Nat := 3901358233414984540208047

theorem tailTrace_7597868 : CollatzResearch.WordTrace tailWord_7597868 prefixEnd_7597868 3901358233414984540208047 := by
  unfold tailWord_7597868
  simp only [CollatzResearch.WordTrace]
  refine ⟨138558506019114661695649129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184744674692152882260865505 138558506019114661695649129)
  ·
    refine ⟨103918879514335996271736847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138558506019114661695649129 103918879514335996271736847)
    ·
      refine ⟨155878319271503994407605271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103918879514335996271736847 155878319271503994407605271)
      ·
        refine ⟨233817478907255991611407907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155878319271503994407605271 233817478907255991611407907)
        ·
          refine ⟨350726218360883987417111861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233817478907255991611407907 350726218360883987417111861)
          ·
            refine ⟨32880582971332873820354237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350726218360883987417111861 32880582971332873820354237)
            ·
              refine ⟨12330218614249827682632839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32880582971332873820354237 12330218614249827682632839)
              ·
                refine ⟨18495327921374741523949259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330218614249827682632839 18495327921374741523949259)
                ·
                  refine ⟨27742991882062112285923889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18495327921374741523949259 27742991882062112285923889)
                  ·
                    refine ⟨20807243911546584214442917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27742991882062112285923889 20807243911546584214442917)
                    ·
                      refine ⟨3901358233414984540208047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20807243911546584214442917 3901358233414984540208047)
                      ·
                        rfl

theorem cell23_7597868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_7597868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597868 prefixEnd_7597868 := by exact prefixLift 7597868
  have htrace : WordTrace (prefixWord ++ tailWord_7597868) baseStart_7597868 baseEnd_7597868 := by
    simpa [prefixWord, tailWord_7597868, baseEnd_7597868] using wordTrace_append hprefix tailTrace_7597868
  have hstable : (prefixWord ++ tailWord_7597868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597868).length < 2 ^ (prefixWord ++ tailWord_7597868).sum := by decide
  have hdescent : baseEnd_7597868 < baseStart_7597868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597905 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_7597905 : Nat := 118140960795 + 7597905 * 2 ^ 59
def prefixEnd_7597905 : Nat := 4983230072969 + 3 ^ 40 * 7597905 * 2
def baseEnd_7597905 : Nat := 3901377232199200895445377

theorem tailTrace_7597905 : CollatzResearch.WordTrace tailWord_7597905 prefixEnd_7597905 3901377232199200895445377 := by
  unfold tailWord_7597905
  simp only [CollatzResearch.WordTrace]
  refine ⟨277118361539095278710395169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184745574359396852473596779 277118361539095278710395169)
  ·
    refine ⟨207838771154321459032796377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277118361539095278710395169 207838771154321459032796377)
    ·
      refine ⟨155879078365741094274597283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207838771154321459032796377 155879078365741094274597283)
      ·
        refine ⟨233818617548611641411895925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155879078365741094274597283 233818617548611641411895925)
        ·
          refine ⟨21920495395182341382365243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233818617548611641411895925 21920495395182341382365243)
          ·
            refine ⟨32880743092773512073547865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21920495395182341382365243 32880743092773512073547865)
            ·
              refine ⟨24660557319580134055160899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32880743092773512073547865 24660557319580134055160899)
              ·
                refine ⟨36990835979370201082741349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24660557319580134055160899 36990835979370201082741349)
                ·
                  refine ⟨6935781746131912703014003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36990835979370201082741349 6935781746131912703014003)
                  ·
                    refine ⟨10403672619197869054521005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935781746131912703014003 10403672619197869054521005)
                    ·
                      refine ⟨3901377232199200895445377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403672619197869054521005 3901377232199200895445377)
                      ·
                        rfl

theorem cell23_7597905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_7597905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597905 prefixEnd_7597905 := by exact prefixLift 7597905
  have htrace : WordTrace (prefixWord ++ tailWord_7597905) baseStart_7597905 baseEnd_7597905 := by
    simpa [prefixWord, tailWord_7597905, baseEnd_7597905] using wordTrace_append hprefix tailTrace_7597905
  have hstable : (prefixWord ++ tailWord_7597905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597905).length < 2 ^ (prefixWord ++ tailWord_7597905).sum := by decide
  have hdescent : baseEnd_7597905 < baseStart_7597905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597906 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_7597906 : Nat := 118140960795 + 7597906 * 2 ^ 59
def prefixEnd_7597906 : Nat := 4983230072969 + 3 ^ 40 * 7597906 * 2
def baseEnd_7597906 : Nat := 3901377745679855391532873

theorem tailTrace_7597906 : CollatzResearch.WordTrace tailWord_7597906 prefixEnd_7597906 3901377745679855391532873 := by
  unfold tailWord_7597906
  simp only [CollatzResearch.WordTrace]
  refine ⟨69279599503022913970295393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184745598674727770587454381 69279599503022913970295393)
  ·
    refine ⟨51959699627267185477721545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69279599503022913970295393 51959699627267185477721545)
    ·
      refine ⟨38969774720450389108291159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51959699627267185477721545 38969774720450389108291159)
      ·
        refine ⟨58454662080675583662436739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38969774720450389108291159 58454662080675583662436739)
        ·
          refine ⟨87681993121013375493655109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58454662080675583662436739 87681993121013375493655109)
          ·
            refine ⟨16440373710190007905060333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87681993121013375493655109 16440373710190007905060333)
            ·
              refine ⟨6165140141321252964397625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16440373710190007905060333 6165140141321252964397625)
              ·
                refine ⟨4623855105990939723298219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165140141321252964397625 4623855105990939723298219)
                ·
                  refine ⟨6935782658986409584947329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623855105990939723298219 6935782658986409584947329)
                  ·
                    refine ⟨5201836994239807188710497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6935782658986409584947329 5201836994239807188710497)
                    ·
                      refine ⟨3901377745679855391532873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201836994239807188710497 3901377745679855391532873)
                      ·
                        rfl

theorem cell23_7597906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_7597906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597906 prefixEnd_7597906 := by exact prefixLift 7597906
  have htrace : WordTrace (prefixWord ++ tailWord_7597906) baseStart_7597906 baseEnd_7597906 := by
    simpa [prefixWord, tailWord_7597906, baseEnd_7597906] using wordTrace_append hprefix tailTrace_7597906
  have hstable : (prefixWord ++ tailWord_7597906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597906).length < 2 ^ (prefixWord ++ tailWord_7597906).sum := by decide
  have hdescent : baseEnd_7597906 < baseStart_7597906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597916 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_7597916 : Nat := 118140960795 + 7597916 * 2 ^ 59
def prefixEnd_7597916 : Nat := 4983230072969 + 3 ^ 40 * 7597916 * 2
def baseEnd_7597916 : Nat := 1300460960162133450802609

theorem tailTrace_7597916 : CollatzResearch.WordTrace tailWord_7597916 prefixEnd_7597916 1300460960162133450802609 := by
  unfold tailWord_7597916
  simp only [CollatzResearch.WordTrace]
  refine ⟨138559381371027713794522801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184745841828036951726030401 138559381371027713794522801)
  ·
    refine ⟨103919536028270785345892101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138559381371027713794522801 103919536028270785345892101)
    ·
      refine ⟨19484913005300772252354769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103919536028270785345892101 19484913005300772252354769)
      ·
        refine ⟨14613684753975579189266077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19484913005300772252354769 14613684753975579189266077)
        ·
          refine ⟨5480131782740842195974779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14613684753975579189266077 5480131782740842195974779)
          ·
            refine ⟨8220197674111263293962169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480131782740842195974779 8220197674111263293962169)
            ·
              refine ⟨6165148255583447470471627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220197674111263293962169 6165148255583447470471627)
              ·
                refine ⟨9247722383375171205707441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165148255583447470471627 9247722383375171205707441)
                ·
                  refine ⟨6935791787531378404280581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9247722383375171205707441 6935791787531378404280581)
                  ·
                    refine ⟨1300460960162133450802609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935791787531378404280581 1300460960162133450802609)
                    ·
                      rfl

theorem cell23_7597916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_7597916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597916 prefixEnd_7597916 := by exact prefixLift 7597916
  have htrace : WordTrace (prefixWord ++ tailWord_7597916) baseStart_7597916 baseEnd_7597916 := by
    simpa [prefixWord, tailWord_7597916, baseEnd_7597916] using wordTrace_append hprefix tailTrace_7597916
  have hstable : (prefixWord ++ tailWord_7597916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597916).length < 2 ^ (prefixWord ++ tailWord_7597916).sum := by decide
  have hdescent : baseEnd_7597916 < baseStart_7597916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597921 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_7597921 : Nat := 118140960795 + 7597921 * 2 ^ 59
def prefixEnd_7597921 : Nat := 4983230072969 + 3 ^ 40 * 7597921 * 2
def baseEnd_7597921 : Nat := 1300461815963224277615101

theorem tailTrace_7597921 : CollatzResearch.WordTrace tailWord_7597921 prefixEnd_7597921 1300461815963224277615101 := by
  unfold tailWord_7597921
  simp only [CollatzResearch.WordTrace]
  refine ⟨277118945107037313442977617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184745963404691542295318411 277118945107037313442977617)
  ·
    refine ⟨207839208830277985082233213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277118945107037313442977617 207839208830277985082233213)
    ·
      refine ⟨77939703311354244405837455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207839208830277985082233213 77939703311354244405837455)
      ·
        refine ⟨116909554967031366608756183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77939703311354244405837455 116909554967031366608756183)
        ·
          refine ⟨175364332450547049913134275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116909554967031366608756183 175364332450547049913134275)
          ·
            refine ⟨263046498675820574869701413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175364332450547049913134275 263046498675820574869701413)
            ·
              refine ⟨49321218501716357788069015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263046498675820574869701413 49321218501716357788069015)
              ·
                refine ⟨73981827752574536682103523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49321218501716357788069015 73981827752574536682103523)
                ·
                  refine ⟨110972741628861805023155285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73981827752574536682103523 110972741628861805023155285)
                  ·
                    refine ⟨1300461815963224277615101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110972741628861805023155285 1300461815963224277615101)
                    ·
                      rfl

theorem cell23_7597921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_7597921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597921 prefixEnd_7597921 := by exact prefixLift 7597921
  have htrace : WordTrace (prefixWord ++ tailWord_7597921) baseStart_7597921 baseEnd_7597921 := by
    simpa [prefixWord, tailWord_7597921, baseEnd_7597921] using wordTrace_append hprefix tailTrace_7597921
  have hstable : (prefixWord ++ tailWord_7597921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597921).length < 2 ^ (prefixWord ++ tailWord_7597921).sum := by decide
  have hdescent : baseEnd_7597921 < baseStart_7597921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597932 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_7597932 : Nat := 118140960795 + 7597932 * 2 ^ 59
def prefixEnd_7597932 : Nat := 4983230072969 + 3 ^ 40 * 7597932 * 2
def baseEnd_7597932 : Nat := 3901391096176872289807753

theorem tailTrace_7597932 : CollatzResearch.WordTrace tailWord_7597932 prefixEnd_7597932 3901391096176872289807753 := by
  unfold tailWord_7597932
  simp only [CollatzResearch.WordTrace]
  refine ⟨138559673154998731160814025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184746230873331641547752033 138559673154998731160814025)
  ·
    refine ⟨103919754866249048370610519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138559673154998731160814025 103919754866249048370610519)
    ·
      refine ⟨155879632299373572555915779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103919754866249048370610519 155879632299373572555915779)
      ·
        refine ⟨233819448449060358833873669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155879632299373572555915779 233819448449060358833873669)
        ·
          refine ⟨43841146584198817281351313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233819448449060358833873669 43841146584198817281351313)
          ·
            refine ⟨32880859938149112961013485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43841146584198817281351313 32880859938149112961013485)
            ·
              refine ⟨12330322476805917360380057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32880859938149112961013485 12330322476805917360380057)
              ·
                refine ⟨9247741857604438020285043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12330322476805917360380057 9247741857604438020285043)
                ·
                  refine ⟨13871612786406657030427565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9247741857604438020285043 13871612786406657030427565)
                  ·
                    refine ⟨5201854794902496386410337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13871612786406657030427565 5201854794902496386410337)
                    ·
                      refine ⟨3901391096176872289807753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201854794902496386410337 3901391096176872289807753)
                      ·
                        rfl

theorem cell23_7597932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_7597932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597932 prefixEnd_7597932 := by exact prefixLift 7597932
  have htrace : WordTrace (prefixWord ++ tailWord_7597932) baseStart_7597932 baseEnd_7597932 := by
    simpa [prefixWord, tailWord_7597932, baseEnd_7597932] using wordTrace_append hprefix tailTrace_7597932
  have hstable : (prefixWord ++ tailWord_7597932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597932).length < 2 ^ (prefixWord ++ tailWord_7597932).sum := by decide
  have hdescent : baseEnd_7597932 < baseStart_7597932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597945 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 1, 4, 2]
def baseStart_7597945 : Nat := 118140960795 + 7597945 * 2 ^ 59
def prefixEnd_7597945 : Nat := 4983230072969 + 3 ^ 40 * 7597945 * 2
def baseEnd_7597945 : Nat := 3901397771425380738945193

theorem tailTrace_7597945 : CollatzResearch.WordTrace tailWord_7597945 prefixEnd_7597945 3901397771425380738945193 := by
  unfold tailWord_7597945
  simp only [CollatzResearch.WordTrace]
  refine ⟨277119820458950365541851289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184746546972633577027900859 277119820458950365541851289)
  ·
    refine ⟨207839865344212774156388467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277119820458950365541851289 207839865344212774156388467)
    ·
      refine ⟨311759798016319161234582701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207839865344212774156388467 311759798016319161234582701)
      ·
        refine ⟨116909924256119685462968513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311759798016319161234582701 116909924256119685462968513)
        ·
          refine ⟨87682443192089764097226385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116909924256119685462968513 87682443192089764097226385)
          ·
            refine ⟨65761832394067323072919789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87682443192089764097226385 65761832394067323072919789)
            ·
              refine ⟨24660687147775246152344921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65761832394067323072919789 24660687147775246152344921)
              ·
                refine ⟨18495515360831434614258691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24660687147775246152344921 18495515360831434614258691)
                ·
                  refine ⟨27743273041247151921388037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18495515360831434614258691 27743273041247151921388037)
                  ·
                    refine ⟨5201863695233840985260257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27743273041247151921388037 5201863695233840985260257)
                    ·
                      refine ⟨3901397771425380738945193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5201863695233840985260257 3901397771425380738945193)
                      ·
                        rfl

theorem cell23_7597945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_7597945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597945 prefixEnd_7597945 := by exact prefixLift 7597945
  have htrace : WordTrace (prefixWord ++ tailWord_7597945) baseStart_7597945 baseEnd_7597945 := by
    simpa [prefixWord, tailWord_7597945, baseEnd_7597945] using wordTrace_append hprefix tailTrace_7597945
  have hstable : (prefixWord ++ tailWord_7597945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597945).length < 2 ^ (prefixWord ++ tailWord_7597945).sum := by decide
  have hdescent : baseEnd_7597945 < baseStart_7597945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7597985 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 7]
def baseStart_7597985 : Nat := 118140960795 + 7597985 * 2 ^ 59
def prefixEnd_7597985 : Nat := 4983230072969 + 3 ^ 40 * 7597985 * 2
def baseEnd_7597985 : Nat := 433490923405728953605001

theorem tailTrace_7597985 : CollatzResearch.WordTrace tailWord_7597985 prefixEnd_7597985 433490923405728953605001 := by
  unfold tailWord_7597985
  simp only [CollatzResearch.WordTrace]
  refine ⟨277121279378805452373307409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184747519585870301582204939 277121279378805452373307409)
  ·
    refine ⟨207840959534104089279980557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277121279378805452373307409 207840959534104089279980557)
    ·
      refine ⟨77940359825289033479992709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207840959534104089279980557 77940359825289033479992709)
      ·
        refine ⟨14613817467241693777498633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77940359825289033479992709 14613817467241693777498633)
        ·
          refine ⟨10960363100431270333123975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14613817467241693777498633 10960363100431270333123975)
          ·
            refine ⟨16440544650646905499685963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960363100431270333123975 16440544650646905499685963)
            ·
              refine ⟨24660816975970358249528945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16440544650646905499685963 24660816975970358249528945)
              ·
                refine ⟨18495612731977768687146709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24660816975970358249528945 18495612731977768687146709)
                ·
                  refine ⟨433490923405728953605001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18495612731977768687146709 433490923405728953605001)
                  ·
                    rfl

theorem cell23_7597985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_7597985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7597985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7597985 prefixEnd_7597985 := by exact prefixLift 7597985
  have htrace : WordTrace (prefixWord ++ tailWord_7597985) baseStart_7597985 baseEnd_7597985 := by
    simpa [prefixWord, tailWord_7597985, baseEnd_7597985] using wordTrace_append hprefix tailTrace_7597985
  have hstable : (prefixWord ++ tailWord_7597985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7597985).length < 2 ^ (prefixWord ++ tailWord_7597985).sum := by decide
  have hdescent : baseEnd_7597985 < baseStart_7597985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7597985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598058 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_7598058 : Nat := 118140960795 + 7598058 * 2 ^ 59
def prefixEnd_7598058 : Nat := 4983230072969 + 3 ^ 40 * 7598058 * 2
def baseEnd_7598058 : Nat := 433495088304370977425797

theorem tailTrace_7598058 : CollatzResearch.WordTrace tailWord_7598058 prefixEnd_7598058 433495088304370977425797 := by
  unfold tailWord_7598058
  simp only [CollatzResearch.WordTrace]
  refine ⟨69280985476885246460178707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184749294605027323893809885 69280985476885246460178707)
  ·
    refine ⟨103921478215327869690268061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69280985476885246460178707 103921478215327869690268061)
    ·
      refine ⟨38970554330747951133850523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103921478215327869690268061 38970554330747951133850523)
      ·
        refine ⟨58455831496121926700775785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38970554330747951133850523 58455831496121926700775785)
        ·
          refine ⟨43841873622091445025581839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58455831496121926700775785 43841873622091445025581839)
          ·
            refine ⟨65762810433137167538372759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43841873622091445025581839 65762810433137167538372759)
            ·
              refine ⟨98644215649705751307559139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65762810433137167538372759 98644215649705751307559139)
              ·
                refine ⟨147966323474558626961338709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98644215649705751307559139 147966323474558626961338709)
                ·
                  refine ⟨433495088304370977425797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147966323474558626961338709 433495088304370977425797)
                  ·
                    rfl

theorem cell23_7598058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_7598058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598058 prefixEnd_7598058 := by exact prefixLift 7598058
  have htrace : WordTrace (prefixWord ++ tailWord_7598058) baseStart_7598058 baseEnd_7598058 := by
    simpa [prefixWord, tailWord_7598058, baseEnd_7598058] using wordTrace_append hprefix tailTrace_7598058
  have hstable : (prefixWord ++ tailWord_7598058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598058).length < 2 ^ (prefixWord ++ tailWord_7598058).sum := by decide
  have hdescent : baseEnd_7598058 < baseStart_7598058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598135 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 4, 4]
def baseStart_7598135 : Nat := 118140960795 + 7598135 * 2 ^ 59
def prefixEnd_7598135 : Nat := 4983230072969 + 3 ^ 40 * 7598135 * 2
def baseEnd_7598135 : Nat := 1300498444249911665189773

theorem tailTrace_7598135 : CollatzResearch.WordTrace tailWord_7598135 prefixEnd_7598135 1300498444249911665189773 := by
  unfold tailWord_7598135
  simp only [CollatzResearch.WordTrace]
  refine ⟨277126750328262027991267859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184751166885508018660845239 277126750328262027991267859)
  ·
    refine ⟨415690125492393041986901789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277126750328262027991267859 415690125492393041986901789)
    ·
      refine ⟨155883797059647390745088171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415690125492393041986901789 155883797059647390745088171)
      ·
        refine ⟨233825695589471086117632257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155883797059647390745088171 233825695589471086117632257)
        ·
          refine ⟨175369271692103314588224193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233825695589471086117632257 175369271692103314588224193)
          ·
            refine ⟨131526953769077485941168145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175369271692103314588224193 131526953769077485941168145)
            ·
              refine ⟨98645215326808114455876109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131526953769077485941168145 98645215326808114455876109)
              ·
                refine ⟨36991955747553042920953541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98645215326808114455876109 36991955747553042920953541)
                ·
                  refine ⟨6935991702666195547678789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36991955747553042920953541 6935991702666195547678789)
                  ·
                    refine ⟨1300498444249911665189773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935991702666195547678789 1300498444249911665189773)
                    ·
                      rfl

theorem cell23_7598135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_7598135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598135 prefixEnd_7598135 := by exact prefixLift 7598135
  have htrace : WordTrace (prefixWord ++ tailWord_7598135) baseStart_7598135 baseEnd_7598135 := by
    simpa [prefixWord, tailWord_7598135, baseEnd_7598135] using wordTrace_append hprefix tailTrace_7598135
  have hstable : (prefixWord ++ tailWord_7598135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598135).length < 2 ^ (prefixWord ++ tailWord_7598135).sum := by decide
  have hdescent : baseEnd_7598135 < baseStart_7598135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598136 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 1, 1, 3]
def baseStart_7598136 : Nat := 118140960795 + 7598136 * 2 ^ 59
def prefixEnd_7598136 : Nat := 4983230072969 + 3 ^ 40 * 7598136 * 2
def baseEnd_7598136 : Nat := 3901495846230389491656815

theorem tailTrace_7598136 : CollatzResearch.WordTrace tailWord_7598136 prefixEnd_7598136 3901495846230389491656815 := by
  unfold tailWord_7598136
  simp only [CollatzResearch.WordTrace]
  refine ⟨138563393400629202581027131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184751191200838936774702841 138563393400629202581027131)
  ·
    refine ⟨207845090100943803871540697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138563393400629202581027131 207845090100943803871540697)
    ·
      refine ⟨155883817575707852903655523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207845090100943803871540697 155883817575707852903655523)
      ·
        refine ⟨233825726363561779355483285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155883817575707852903655523 233825726363561779355483285)
        ·
          refine ⟨10960580923291958407288279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233825726363561779355483285 10960580923291958407288279)
          ·
            refine ⟨16440871384937937610932419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960580923291958407288279 16440871384937937610932419)
            ·
              refine ⟨24661307077406906416398629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16440871384937937610932419 24661307077406906416398629)
              ·
                refine ⟨4623995077013794953074743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24661307077406906416398629 4623995077013794953074743)
                ·
                  refine ⟨6935992615520692429612115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623995077013794953074743 6935992615520692429612115)
                  ·
                    refine ⟨10403988923281038644418173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935992615520692429612115 10403988923281038644418173)
                    ·
                      refine ⟨3901495846230389491656815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10403988923281038644418173 3901495846230389491656815)
                      ·
                        rfl

theorem cell23_7598136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_7598136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598136 prefixEnd_7598136 := by exact prefixLift 7598136
  have htrace : WordTrace (prefixWord ++ tailWord_7598136) baseStart_7598136 baseEnd_7598136 := by
    simpa [prefixWord, tailWord_7598136, baseEnd_7598136] using wordTrace_append hprefix tailTrace_7598136
  have hstable : (prefixWord ++ tailWord_7598136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598136).length < 2 ^ (prefixWord ++ tailWord_7598136).sum := by decide
  have hdescent : baseEnd_7598136 < baseStart_7598136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598172 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7598172 : Nat := 118140960795 + 7598172 * 2 ^ 59
def prefixEnd_7598172 : Nat := 4983230072969 + 3 ^ 40 * 7598172 * 2
def baseEnd_7598172 : Nat := 3901514331533951350806649

theorem tailTrace_7598172 : CollatzResearch.WordTrace tailWord_7598172 prefixEnd_7598172 3901514331533951350806649 := by
  unfold tailWord_7598172
  simp only [CollatzResearch.WordTrace]
  refine ⟨138564049914563991655182385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184752066552751988873576513 138564049914563991655182385)
  ·
    refine ⟨103923037435922993741386789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138564049914563991655182385 103923037435922993741386789)
    ·
      refine ⟨19485569519235561326510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103923037435922993741386789 19485569519235561326510023)
      ·
        refine ⟨29228354278853341989765035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19485569519235561326510023 29228354278853341989765035)
        ·
          refine ⟨43842531418280012984647553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29228354278853341989765035 43842531418280012984647553)
          ·
            refine ⟨32881898563710009738485665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43842531418280012984647553 32881898563710009738485665)
            ·
              refine ⟨24661423922782507303864249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32881898563710009738485665 24661423922782507303864249)
              ·
                refine ⟨18496067942086880477898187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24661423922782507303864249 18496067942086880477898187)
                ·
                  refine ⟨27744101913130320716847281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18496067942086880477898187 27744101913130320716847281)
                  ·
                    refine ⟨20808076434847740537635461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27744101913130320716847281 20808076434847740537635461)
                    ·
                      refine ⟨3901514331533951350806649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20808076434847740537635461 3901514331533951350806649)
                      ·
                        rfl

theorem cell23_7598172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7598172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598172 prefixEnd_7598172 := by exact prefixLift 7598172
  have htrace : WordTrace (prefixWord ++ tailWord_7598172) baseStart_7598172 baseEnd_7598172 := by
    simpa [prefixWord, tailWord_7598172, baseEnd_7598172] using wordTrace_append hprefix tailTrace_7598172
  have hstable : (prefixWord ++ tailWord_7598172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598172).length < 2 ^ (prefixWord ++ tailWord_7598172).sum := by decide
  have hdescent : baseEnd_7598172 < baseStart_7598172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598175 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_7598175 : Nat := 118140960795 + 7598175 * 2 ^ 59
def prefixEnd_7598175 : Nat := 4983230072969 + 3 ^ 40 * 7598175 * 2
def baseEnd_7598175 : Nat := 3901515871975914839069135

theorem tailTrace_7598175 : CollatzResearch.WordTrace tailWord_7598175 prefixEnd_7598175 3901515871975914839069135 := by
  unfold tailWord_7598175
  simp only [CollatzResearch.WordTrace]
  refine ⟨277128209248117114822723979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184752139498744743215149319 277128209248117114822723979)
  ·
    refine ⟨415692313872175672234085969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277128209248117114822723979 415692313872175672234085969)
    ·
      refine ⟨311769235404131754175564477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415692313872175672234085969 311769235404131754175564477)
      ·
        refine ⟨116913463276549407815836679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311769235404131754175564477 116913463276549407815836679)
        ·
          refine ⟨175370194914824111723755019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116913463276549407815836679 175370194914824111723755019)
          ·
            refine ⟨263055292372236167585632529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175370194914824111723755019 263055292372236167585632529)
            ·
              refine ⟨197291469279177125689224397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263055292372236167585632529 197291469279177125689224397)
              ·
                refine ⟨73984300979691422133459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197291469279177125689224397 73984300979691422133459149)
                ·
                  refine ⟨27744112867384283300047181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73984300979691422133459149 27744112867384283300047181)
                  ·
                    refine ⟨10404042325269106237517693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27744112867384283300047181 10404042325269106237517693)
                    ·
                      refine ⟨3901515871975914839069135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404042325269106237517693 3901515871975914839069135)
                      ·
                        rfl

theorem cell23_7598175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_7598175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598175 prefixEnd_7598175 := by exact prefixLift 7598175
  have htrace : WordTrace (prefixWord ++ tailWord_7598175) baseStart_7598175 baseEnd_7598175 := by
    simpa [prefixWord, tailWord_7598175, baseEnd_7598175] using wordTrace_append hprefix tailTrace_7598175
  have hstable : (prefixWord ++ tailWord_7598175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598175).length < 2 ^ (prefixWord ++ tailWord_7598175).sum := by decide
  have hdescent : baseEnd_7598175 < baseStart_7598175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598176 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 1, 2, 2]
def baseStart_7598176 : Nat := 118140960795 + 7598176 * 2 ^ 59
def prefixEnd_7598176 : Nat := 4983230072969 + 3 ^ 40 * 7598176 * 2
def baseEnd_7598176 : Nat := 3901516385456569335156631

theorem tailTrace_7598176 : CollatzResearch.WordTrace tailWord_7598176 prefixEnd_7598176 3901516385456569335156631 := by
  unfold tailWord_7598176
  simp only [CollatzResearch.WordTrace]
  refine ⟨138564122860556745996755191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184752163814075661329006921 138564122860556745996755191)
  ·
    refine ⟨207846184290835118995132787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138564122860556745996755191 207846184290835118995132787)
    ·
      refine ⟨311769276436252678492699181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207846184290835118995132787 311769276436252678492699181)
      ·
        refine ⟨116913478663594754434762193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311769276436252678492699181 116913478663594754434762193)
        ·
          refine ⟨87685108997696065826071645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116913478663594754434762193 87685108997696065826071645)
          ·
            refine ⟨32881915874136024684776867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87685108997696065826071645 32881915874136024684776867)
            ·
              refine ⟨49322873811204037027165301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32881915874136024684776867 49322873811204037027165301)
              ·
                refine ⟨4624019419800378471296747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49322873811204037027165301 4624019419800378471296747)
                ·
                  refine ⟨6936029129700567706945121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624019419800378471296747 6936029129700567706945121)
                  ·
                    refine ⟨5202021847275425780208841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6936029129700567706945121 5202021847275425780208841)
                    ·
                      refine ⟨3901516385456569335156631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202021847275425780208841 3901516385456569335156631)
                      ·
                        rfl

theorem cell23_7598176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_7598176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598176 prefixEnd_7598176 := by exact prefixLift 7598176
  have htrace : WordTrace (prefixWord ++ tailWord_7598176) baseStart_7598176 baseEnd_7598176 := by
    simpa [prefixWord, tailWord_7598176, baseEnd_7598176] using wordTrace_append hprefix tailTrace_7598176
  have hstable : (prefixWord ++ tailWord_7598176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598176).length < 2 ^ (prefixWord ++ tailWord_7598176).sum := by decide
  have hdescent : baseEnd_7598176 < baseStart_7598176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598179 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 1, 2, 3]
def baseStart_7598179 : Nat := 118140960795 + 7598179 * 2 ^ 59
def prefixEnd_7598179 : Nat := 4983230072969 + 3 ^ 40 * 7598179 * 2
def baseEnd_7598179 : Nat := 3901517925898532823419117

theorem tailTrace_7598179 : CollatzResearch.WordTrace tailWord_7598179 prefixEnd_7598179 3901517925898532823419117 := by
  unfold tailWord_7598179
  simp only [CollatzResearch.WordTrace]
  refine ⟨277128355140102623505869591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184752236760068415670579727 277128355140102623505869591)
  ·
    refine ⟨415692532710153935258804387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277128355140102623505869591 415692532710153935258804387)
    ·
      refine ⟨623538799065230902888206581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415692532710153935258804387 623538799065230902888206581)
      ·
        refine ⟨58456762412365397145769367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 623538799065230902888206581 58456762412365397145769367)
        ·
          refine ⟨87685143618548095718654051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58456762412365397145769367 87685143618548095718654051)
          ·
            refine ⟨131527715427822143577981077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87685143618548095718654051 131527715427822143577981077)
            ·
              refine ⟨6165361660679162980217863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131527715427822143577981077 6165361660679162980217863)
              ·
                refine ⟨9248042491018744470326795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165361660679162980217863 9248042491018744470326795)
                ·
                  refine ⟨13872063736528116705490193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248042491018744470326795 13872063736528116705490193)
                  ·
                    refine ⟨10404047802396087529117645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13872063736528116705490193 10404047802396087529117645)
                    ·
                      refine ⟨3901517925898532823419117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404047802396087529117645 3901517925898532823419117)
                      ·
                        rfl

theorem cell23_7598179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_7598179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598179 prefixEnd_7598179 := by exact prefixLift 7598179
  have htrace : WordTrace (prefixWord ++ tailWord_7598179) baseStart_7598179 baseEnd_7598179 := by
    simpa [prefixWord, tailWord_7598179, baseEnd_7598179] using wordTrace_append hprefix tailTrace_7598179
  have hstable : (prefixWord ++ tailWord_7598179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598179).length < 2 ^ (prefixWord ++ tailWord_7598179).sum := by decide
  have hdescent : baseEnd_7598179 < baseStart_7598179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598186 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_7598186 : Nat := 118140960795 + 7598186 * 2 ^ 59
def prefixEnd_7598186 : Nat := 4983230072969 + 3 ^ 40 * 7598186 * 2
def baseEnd_7598186 : Nat := 1300507173421038098677195

theorem tailTrace_7598186 : CollatzResearch.WordTrace tailWord_7598186 prefixEnd_7598186 1300507173421038098677195 := by
  unfold tailWord_7598186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69282152612769315925343603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184752406967384842467582941 69282152612769315925343603)
  ·
    refine ⟨103923228919153973888015405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69282152612769315925343603 103923228919153973888015405)
    ·
      refine ⟨38971210844682740208005777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103923228919153973888015405 38971210844682740208005777)
      ·
        refine ⟨29228408133512055156004333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38971210844682740208005777 29228408133512055156004333)
        ·
          refine ⟨10960653050067020683501625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29228408133512055156004333 10960653050067020683501625)
          ·
            refine ⟨8220489787550265512626219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10960653050067020683501625 8220489787550265512626219)
            ·
              refine ⟨12330734681325398268939329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8220489787550265512626219 12330734681325398268939329)
              ·
                refine ⟨9248051010994048701704497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12330734681325398268939329 9248051010994048701704497)
                ·
                  refine ⟨6936038258245536526278373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9248051010994048701704497 6936038258245536526278373)
                  ·
                    refine ⟨1300507173421038098677195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6936038258245536526278373 1300507173421038098677195)
                    ·
                      rfl

theorem cell23_7598186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_7598186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598186 prefixEnd_7598186 := by exact prefixLift 7598186
  have htrace : WordTrace (prefixWord ++ tailWord_7598186) baseStart_7598186 baseEnd_7598186 := by
    simpa [prefixWord, tailWord_7598186, baseEnd_7598186] using wordTrace_append hprefix tailTrace_7598186
  have hstable : (prefixWord ++ tailWord_7598186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598186).length < 2 ^ (prefixWord ++ tailWord_7598186).sum := by decide
  have hdescent : baseEnd_7598186 < baseStart_7598186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598215 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_7598215 : Nat := 118140960795 + 7598215 * 2 ^ 59
def prefixEnd_7598215 : Nat := 4983230072969 + 3 ^ 40 * 7598215 * 2
def baseEnd_7598215 : Nat := 3901536411202094682568951

theorem tailTrace_7598215 : CollatzResearch.WordTrace tailWord_7598215 prefixEnd_7598215 3901536411202094682568951 := by
  unfold tailWord_7598215
  simp only [CollatzResearch.WordTrace]
  refine ⟨277129668167972201654180099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184753112111981467769453399 277129668167972201654180099)
  ·
    refine ⟨415694502251958302481270149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277129668167972201654180099 415694502251958302481270149)
    ·
      refine ⟨77942719172242181715238153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415694502251958302481270149 77942719172242181715238153)
      ·
        refine ⟨58457039379181636286428615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77942719172242181715238153 58457039379181636286428615)
        ·
          refine ⟨87685559068772454429642923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58457039379181636286428615 87685559068772454429642923)
          ·
            refine ⟨131528338603158681644464385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87685559068772454429642923 131528338603158681644464385)
            ·
              refine ⟨98646253952369011233348289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131528338603158681644464385 98646253952369011233348289)
              ·
                refine ⟨73984690464276758425011217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98646253952369011233348289 73984690464276758425011217)
                ·
                  refine ⟨55488517848207568818758413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73984690464276758425011217 55488517848207568818758413)
                  ·
                    refine ⟨20808194193077838307034405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55488517848207568818758413 20808194193077838307034405)
                    ·
                      refine ⟨3901536411202094682568951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20808194193077838307034405 3901536411202094682568951)
                      ·
                        rfl

theorem cell23_7598215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_7598215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598215 prefixEnd_7598215 := by exact prefixLift 7598215
  have htrace : WordTrace (prefixWord ++ tailWord_7598215) baseStart_7598215 baseEnd_7598215 := by
    simpa [prefixWord, tailWord_7598215, baseEnd_7598215] using wordTrace_append hprefix tailTrace_7598215
  have hstable : (prefixWord ++ tailWord_7598215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598215).length < 2 ^ (prefixWord ++ tailWord_7598215).sum := by decide
  have hdescent : baseEnd_7598215 < baseStart_7598215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598230 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7598230 : Nat := 118140960795 + 7598230 * 2 ^ 59
def prefixEnd_7598230 : Nat := 4983230072969 + 3 ^ 40 * 7598230 * 2
def baseEnd_7598230 : Nat := 3901544113411912123881383

theorem tailTrace_7598230 : CollatzResearch.WordTrace tailWord_7598230 prefixEnd_7598230 3901544113411912123881383 := by
  unfold tailWord_7598230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17320638453932366200998509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184753476841945239477317429 17320638453932366200998509)
  ·
    refine ⟨6495239420224637325374441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17320638453932366200998509 6495239420224637325374441)
    ·
      refine ⟨4871429565168477994030831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6495239420224637325374441 4871429565168477994030831)
      ·
        refine ⟨7307144347752716991046247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871429565168477994030831 7307144347752716991046247)
        ·
          refine ⟨10960716521629075486569371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307144347752716991046247 10960716521629075486569371)
          ·
            refine ⟨16441074782443613229854057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960716521629075486569371 16441074782443613229854057)
            ·
              refine ⟨12330806086832709922390543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16441074782443613229854057 12330806086832709922390543)
              ·
                refine ⟨18496209130249064883585815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330806086832709922390543 18496209130249064883585815)
                ·
                  refine ⟨27744313695373597325378723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18496209130249064883585815 27744313695373597325378723)
                  ·
                    refine ⟨41616470543060395988068085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27744313695373597325378723 41616470543060395988068085)
                    ·
                      refine ⟨3901544113411912123881383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41616470543060395988068085 3901544113411912123881383)
                      ·
                        rfl

theorem cell23_7598230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7598230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598230 prefixEnd_7598230 := by exact prefixLift 7598230
  have htrace : WordTrace (prefixWord ++ tailWord_7598230) baseStart_7598230 baseEnd_7598230 := by
    simpa [prefixWord, tailWord_7598230, baseEnd_7598230] using wordTrace_append hprefix tailTrace_7598230
  have hstable : (prefixWord ++ tailWord_7598230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598230).length < 2 ^ (prefixWord ++ tailWord_7598230).sum := by decide
  have hdescent : baseEnd_7598230 < baseStart_7598230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598235 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3]
def baseStart_7598235 : Nat := 118140960795 + 7598235 * 2 ^ 59
def prefixEnd_7598235 : Nat := 4983230072969 + 3 ^ 40 * 7598235 * 2
def baseEnd_7598235 : Nat := 3901546680815184604318859

theorem tailTrace_7598235 : CollatzResearch.WordTrace tailWord_7598235 prefixEnd_7598235 3901546680815184604318859 := by
  unfold tailWord_7598235
  simp only [CollatzResearch.WordTrace]
  refine ⟨277130397627899745069908159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184753598418599830046605439 277130397627899745069908159)
  ·
    refine ⟨415695596441849617604862239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277130397627899745069908159 415695596441849617604862239)
    ·
      refine ⟨623543394662774426407293359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415695596441849617604862239 623543394662774426407293359)
      ·
        refine ⟨935315091994161639610940039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623543394662774426407293359 935315091994161639610940039)
        ·
          refine ⟨1402972637991242459416410059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935315091994161639610940039 1402972637991242459416410059)
          ·
            refine ⟨2104458956986863689124615089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402972637991242459416410059 2104458956986863689124615089)
            ·
              refine ⟨1578344217740147766843461317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2104458956986863689124615089 1578344217740147766843461317)
              ·
                refine ⟨295939540826277706283148997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1578344217740147766843461317 295939540826277706283148997)
                ·
                  refine ⟨55488663904927069928090437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295939540826277706283148997 55488663904927069928090437)
                  ·
                    refine ⟨10404124482173825611516957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55488663904927069928090437 10404124482173825611516957)
                    ·
                      refine ⟨3901546680815184604318859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404124482173825611516957 3901546680815184604318859)
                      ·
                        rfl

theorem cell23_7598235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3].length) (baseStart_7598235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598235 prefixEnd_7598235 := by exact prefixLift 7598235
  have htrace : WordTrace (prefixWord ++ tailWord_7598235) baseStart_7598235 baseEnd_7598235 := by
    simpa [prefixWord, tailWord_7598235, baseEnd_7598235] using wordTrace_append hprefix tailTrace_7598235
  have hstable : (prefixWord ++ tailWord_7598235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598235).length < 2 ^ (prefixWord ++ tailWord_7598235).sum := by decide
  have hdescent : baseEnd_7598235 < baseStart_7598235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598270 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_7598270 : Nat := 118140960795 + 7598270 * 2 ^ 59
def prefixEnd_7598270 : Nat := 4983230072969 + 3 ^ 40 * 7598270 * 2
def baseEnd_7598270 : Nat := 3901564652638091967381199

theorem tailTrace_7598270 : CollatzResearch.WordTrace tailWord_7598270 prefixEnd_7598270 3901564652638091967381199 := by
  unfold tailWord_7598270
  simp only [CollatzResearch.WordTrace]
  refine ⟨34641459272846618255929033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184754449455181964031621509 34641459272846618255929033)
  ·
    refine ⟨25981094454634963691946775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34641459272846618255929033 25981094454634963691946775)
    ·
      refine ⟨38971641681952445537920163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25981094454634963691946775 38971641681952445537920163)
      ·
        refine ⟨58457462522928668306880245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38971641681952445537920163 58457462522928668306880245)
        ·
          refine ⟨5480387111524562653770023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58457462522928668306880245 5480387111524562653770023)
          ·
            refine ⟨8220580667286843980655035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480387111524562653770023 8220580667286843980655035)
            ·
              refine ⟨12330871000930265970982553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8220580667286843980655035 12330871000930265970982553)
              ·
                refine ⟨9248153250697699478236915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12330871000930265970982553 9248153250697699478236915)
                ·
                  refine ⟨13872229876046549217355373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248153250697699478236915 13872229876046549217355373)
                  ·
                    refine ⟨5202086203517455956508265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13872229876046549217355373 5202086203517455956508265)
                    ·
                      refine ⟨3901564652638091967381199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202086203517455956508265 3901564652638091967381199)
                      ·
                        rfl

theorem cell23_7598270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_7598270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598270 prefixEnd_7598270 := by exact prefixLift 7598270
  have htrace : WordTrace (prefixWord ++ tailWord_7598270) baseStart_7598270 baseEnd_7598270 := by
    simpa [prefixWord, tailWord_7598270, baseEnd_7598270] using wordTrace_append hprefix tailTrace_7598270
  have hstable : (prefixWord ++ tailWord_7598270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598270).length < 2 ^ (prefixWord ++ tailWord_7598270).sum := by decide
  have hdescent : baseEnd_7598270 < baseStart_7598270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598309 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7598309 : Nat := 118140960795 + 7598309 * 2 ^ 59
def prefixEnd_7598309 : Nat := 4983230072969 + 3 ^ 40 * 7598309 * 2
def baseEnd_7598309 : Nat := 3901584678383617314793519

theorem tailTrace_7598309 : CollatzResearch.WordTrace tailWord_7598309 prefixEnd_7598309 3901584678383617314793519 := by
  unfold tailWord_7598309
  simp only [CollatzResearch.WordTrace]
  refine ⟨277133096629631655708101981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184755397753087770472067987 277133096629631655708101981)
  ·
    refine ⟨103924911236111870890538243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277133096629631655708101981 103924911236111870890538243)
    ·
      refine ⟨155887366854167806335807365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103924911236111870890538243 155887366854167806335807365)
      ·
        refine ⟨29228881285156463687963881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155887366854167806335807365 29228881285156463687963881)
        ·
          refine ⟨21921660963867347765972911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29228881285156463687963881 21921660963867347765972911)
          ·
            refine ⟨32882491445801021648959367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21921660963867347765972911 32882491445801021648959367)
            ·
              refine ⟨49323737168701532473439051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32882491445801021648959367 49323737168701532473439051)
              ·
                refine ⟨73985605753052298710158577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49323737168701532473439051 73985605753052298710158577)
                ·
                  refine ⟨55489204314789224032618933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73985605753052298710158577 55489204314789224032618933)
                  ·
                    refine ⟨5202112904511489753058025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55489204314789224032618933 5202112904511489753058025)
                    ·
                      refine ⟨3901584678383617314793519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202112904511489753058025 3901584678383617314793519)
                      ·
                        rfl

theorem cell23_7598309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7598309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598309 prefixEnd_7598309 := by exact prefixLift 7598309
  have htrace : WordTrace (prefixWord ++ tailWord_7598309) baseStart_7598309 baseEnd_7598309 := by
    simpa [prefixWord, tailWord_7598309, baseEnd_7598309] using wordTrace_append hprefix tailTrace_7598309
  have hstable : (prefixWord ++ tailWord_7598309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598309).length < 2 ^ (prefixWord ++ tailWord_7598309).sum := by decide
  have hdescent : baseEnd_7598309 < baseStart_7598309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598312 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7598312 : Nat := 118140960795 + 7598312 * 2 ^ 59
def prefixEnd_7598312 : Nat := 4983230072969 + 3 ^ 40 * 7598312 * 2
def baseEnd_7598312 : Nat := 3901586218825580803056005

theorem tailTrace_7598312 : CollatzResearch.WordTrace tailWord_7598312 prefixEnd_7598312 3901586218825580803056005 := by
  unfold tailWord_7598312
  simp only [CollatzResearch.WordTrace]
  refine ⟨138566603024310393610230595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184755470699080524813640793 138566603024310393610230595)
  ·
    refine ⟨207849904536465590415345893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138566603024310393610230595 207849904536465590415345893)
    ·
      refine ⟨38971857100587298202877355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207849904536465590415345893 38971857100587298202877355)
      ·
        refine ⟨58457785650880947304316033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38971857100587298202877355 58457785650880947304316033)
        ·
          refine ⟨43843339238160710478237025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58457785650880947304316033 43843339238160710478237025)
          ·
            refine ⟨32882504428620532858677769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43843339238160710478237025 32882504428620532858677769)
            ·
              refine ⟨24661878321465399644008327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32882504428620532858677769 24661878321465399644008327)
              ·
                refine ⟨36992817482198099466012491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24661878321465399644008327 36992817482198099466012491)
                ·
                  refine ⟨55489226223297149199018737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36992817482198099466012491 55489226223297149199018737)
                  ·
                    refine ⟨41616919667472861899264053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55489226223297149199018737 41616919667472861899264053)
                    ·
                      refine ⟨3901586218825580803056005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41616919667472861899264053 3901586218825580803056005)
                      ·
                        rfl

theorem cell23_7598312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7598312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598312 prefixEnd_7598312 := by exact prefixLift 7598312
  have htrace : WordTrace (prefixWord ++ tailWord_7598312) baseStart_7598312 baseEnd_7598312 := by
    simpa [prefixWord, tailWord_7598312, baseEnd_7598312] using wordTrace_append hprefix tailTrace_7598312
  have hstable : (prefixWord ++ tailWord_7598312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598312).length < 2 ^ (prefixWord ++ tailWord_7598312).sum := by decide
  have hdescent : baseEnd_7598312 < baseStart_7598312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598392 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_7598392 : Nat := 118140960795 + 7598392 * 2 ^ 59
def prefixEnd_7598392 : Nat := 4983230072969 + 3 ^ 40 * 7598392 * 2
def baseEnd_7598392 : Nat := 1300542432425980163351879

theorem tailTrace_7598392 : CollatzResearch.WordTrace tailWord_7598392 prefixEnd_7598392 1300542432425980163351879 := by
  unfold tailWord_7598392
  simp only [CollatzResearch.WordTrace]
  refine ⟨138568061944165480441686715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184757415925553973922248953 138568061944165480441686715)
  ·
    refine ⟨207852092916248220662530073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138568061944165480441686715 207852092916248220662530073)
    ·
      refine ⟨155889069687186165496897555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207852092916248220662530073 155889069687186165496897555)
      ·
        refine ⟨233833604530779248245346333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155889069687186165496897555 233833604530779248245346333)
        ·
          refine ⟨87687601699042218092004875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233833604530779248245346333 87687601699042218092004875)
          ·
            refine ⟨131531402548563327138007313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87687601699042218092004875 131531402548563327138007313)
            ·
              refine ⟨98648551911422495353505485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131531402548563327138007313 98648551911422495353505485)
              ·
                refine ⟨36993206966783435757564557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98648551911422495353505485 36993206966783435757564557)
                ·
                  refine ⟨13872452612543788409086709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36993206966783435757564557 13872452612543788409086709)
                  ·
                    refine ⟨1300542432425980163351879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13872452612543788409086709 1300542432425980163351879)
                    ·
                      rfl

theorem cell23_7598392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_7598392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598392 prefixEnd_7598392 := by exact prefixLift 7598392
  have htrace : WordTrace (prefixWord ++ tailWord_7598392) baseStart_7598392 baseEnd_7598392 := by
    simpa [prefixWord, tailWord_7598392, baseEnd_7598392] using wordTrace_append hprefix tailTrace_7598392
  have hstable : (prefixWord ++ tailWord_7598392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598392).length < 2 ^ (prefixWord ++ tailWord_7598392).sum := by decide
  have hdescent : baseEnd_7598392 < baseStart_7598392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598399 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 5, 2]
def baseStart_7598399 : Nat := 118140960795 + 7598399 * 2 ^ 59
def prefixEnd_7598399 : Nat := 4983230072969 + 3 ^ 40 * 7598399 * 2
def baseEnd_7598399 : Nat := 3901630891642521962668105

theorem tailTrace_7598399 : CollatzResearch.WordTrace tailWord_7598399 prefixEnd_7598399 3901630891642521962668105 := by
  unfold tailWord_7598399
  simp only [CollatzResearch.WordTrace]
  refine ⟨277136379199305601078878251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184757586132870400719252167 277136379199305601078878251)
  ·
    refine ⟨415704568798958401618317377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277136379199305601078878251 415704568798958401618317377)
    ·
      refine ⟨311778426599218801213738033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415704568798958401618317377 311778426599218801213738033)
      ·
        refine ⟨233833819949414100910303525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311778426599218801213738033 233833819949414100910303525)
        ·
          refine ⟨43843841240515143920681911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233833819949414100910303525 43843841240515143920681911)
          ·
            refine ⟨65765761860772715881022867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43843841240515143920681911 65765761860772715881022867)
            ·
              refine ⟨98648642791159073821534301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65765761860772715881022867 98648642791159073821534301)
              ·
                refine ⟨36993241046684652683075363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98648642791159073821534301 36993241046684652683075363)
                ·
                  refine ⟨55489861570026979024613045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36993241046684652683075363 55489861570026979024613045)
                  ·
                    refine ⟨5202174522190029283557473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55489861570026979024613045 5202174522190029283557473)
                    ·
                      refine ⟨3901630891642521962668105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202174522190029283557473 3901630891642521962668105)
                      ·
                        rfl

theorem cell23_7598399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_7598399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598399 prefixEnd_7598399 := by exact prefixLift 7598399
  have htrace : WordTrace (prefixWord ++ tailWord_7598399) baseStart_7598399 baseEnd_7598399 := by
    simpa [prefixWord, tailWord_7598399, baseEnd_7598399] using wordTrace_append hprefix tailTrace_7598399
  have hstable : (prefixWord ++ tailWord_7598399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598399).length < 2 ^ (prefixWord ++ tailWord_7598399).sum := by decide
  have hdescent : baseEnd_7598399 < baseStart_7598399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598416 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2]
def baseStart_7598416 : Nat := 118140960795 + 7598416 * 2 ^ 59
def prefixEnd_7598416 : Nat := 4983230072969 + 3 ^ 40 * 7598416 * 2
def baseEnd_7598416 : Nat := 3901639620813648396155527

theorem tailTrace_7598416 : CollatzResearch.WordTrace tailWord_7598416 prefixEnd_7598416 3901639620813648396155527 := by
  unfold tailWord_7598416
  simp only [CollatzResearch.WordTrace]
  refine ⟨138568499620122006491123551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184757999493496008654831401 138568499620122006491123551)
  ·
    refine ⟨207852749430183009736685327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138568499620122006491123551 207852749430183009736685327)
    ·
      refine ⟨311779124145274514605027991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207852749430183009736685327 311779124145274514605027991)
      ·
        refine ⟨467668686217911771907541987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311779124145274514605027991 467668686217911771907541987)
        ·
          refine ⟨701503029326867657861312981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467668686217911771907541987 701503029326867657861312981)
          ·
            refine ⟨16441477249848460731124523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 701503029326867657861312981 16441477249848460731124523)
            ·
              refine ⟨24662215874772691096686785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441477249848460731124523 24662215874772691096686785)
              ·
                refine ⟨18496661906079518322515089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24662215874772691096686785 18496661906079518322515089)
                ·
                  refine ⟨13872496429559638741886317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18496661906079518322515089 13872496429559638741886317)
                  ·
                    refine ⟨5202186161084864528207369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13872496429559638741886317 5202186161084864528207369)
                    ·
                      refine ⟨3901639620813648396155527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202186161084864528207369 3901639620813648396155527)
                      ·
                        rfl

theorem cell23_7598416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2].length) (baseStart_7598416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598416 prefixEnd_7598416 := by exact prefixLift 7598416
  have htrace : WordTrace (prefixWord ++ tailWord_7598416) baseStart_7598416 baseEnd_7598416 := by
    simpa [prefixWord, tailWord_7598416, baseEnd_7598416] using wordTrace_append hprefix tailTrace_7598416
  have hstable : (prefixWord ++ tailWord_7598416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598416).length < 2 ^ (prefixWord ++ tailWord_7598416).sum := by decide
  have hdescent : baseEnd_7598416 < baseStart_7598416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598459 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4]
def baseStart_7598459 : Nat := 118140960795 + 7598459 * 2 ^ 59
def prefixEnd_7598459 : Nat := 4983230072969 + 3 ^ 40 * 7598459 * 2
def baseEnd_7598459 : Nat := 3901661700481791727917829

theorem tailTrace_7598459 : CollatzResearch.WordTrace tailWord_7598459 prefixEnd_7598459 3901661700481791727917829 := by
  unfold tailWord_7598459
  simp only [CollatzResearch.WordTrace]
  refine ⟨277138567579088231326062431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184759045052725487550708287 277138567579088231326062431)
  ·
    refine ⟨415707851368632346989093647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277138567579088231326062431 415707851368632346989093647)
    ·
      refine ⟨623561777052948520483640471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415707851368632346989093647 623561777052948520483640471)
      ·
        refine ⟨935342665579422780725460707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623561777052948520483640471 935342665579422780725460707)
        ·
          refine ⟨1403013998369134171088191061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935342665579422780725460707 1403013998369134171088191061)
          ·
            refine ⟨16441570293388291067439739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1403013998369134171088191061 16441570293388291067439739)
            ·
              refine ⟨24662355440082436601159609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441570293388291067439739 24662355440082436601159609)
              ·
                refine ⟨18496766580061827450869707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24662355440082436601159609 18496766580061827450869707)
                ·
                  refine ⟨27745149870092741176304561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18496766580061827450869707 27745149870092741176304561)
                  ·
                    refine ⟨20808862402569555882228421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27745149870092741176304561 20808862402569555882228421)
                    ·
                      refine ⟨3901661700481791727917829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20808862402569555882228421 3901661700481791727917829)
                      ·
                        rfl

theorem cell23_7598459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_7598459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598459 prefixEnd_7598459 := by exact prefixLift 7598459
  have htrace : WordTrace (prefixWord ++ tailWord_7598459) baseStart_7598459 baseEnd_7598459 := by
    simpa [prefixWord, tailWord_7598459, baseEnd_7598459] using wordTrace_append hprefix tailTrace_7598459
  have hstable : (prefixWord ++ tailWord_7598459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598459).length < 2 ^ (prefixWord ++ tailWord_7598459).sum := by decide
  have hdescent : baseEnd_7598459 < baseStart_7598459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598474 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7598474 : Nat := 118140960795 + 7598474 * 2 ^ 59
def prefixEnd_7598474 : Nat := 4983230072969 + 3 ^ 40 * 7598474 * 2
def baseEnd_7598474 : Nat := 3901669402691609169230261

theorem tailTrace_7598474 : CollatzResearch.WordTrace tailWord_7598474 prefixEnd_7598474 3901669402691609169230261 := by
  unfold tailWord_7598474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69284778668508472221964619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184759409782689259258572317 69284778668508472221964619)
  ·
    refine ⟨103927168002762708332946929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69284778668508472221964619 103927168002762708332946929)
    ·
      refine ⟨77945376002072031249710197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103927168002762708332946929 77945376002072031249710197)
      ·
        refine ⟨7307379000194252929660331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77945376002072031249710197 7307379000194252929660331)
        ·
          refine ⟨10961068500291379394490497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307379000194252929660331 10961068500291379394490497)
          ·
            refine ⟨8220801375218534545867873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10961068500291379394490497 8220801375218534545867873)
            ·
              refine ⟨6165601031413900909400905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220801375218534545867873 6165601031413900909400905)
              ·
                refine ⟨4624200773560425682050679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165601031413900909400905 4624200773560425682050679)
                ·
                  refine ⟨6936301160340638523076019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624200773560425682050679 6936301160340638523076019)
                  ·
                    refine ⟨10404451740510957784614029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6936301160340638523076019 10404451740510957784614029)
                    ·
                      refine ⟨3901669402691609169230261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404451740510957784614029 3901669402691609169230261)
                      ·
                        rfl

theorem cell23_7598474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7598474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598474 prefixEnd_7598474 := by exact prefixLift 7598474
  have htrace : WordTrace (prefixWord ++ tailWord_7598474) baseStart_7598474 baseEnd_7598474 := by
    simpa [prefixWord, tailWord_7598474, baseEnd_7598474] using wordTrace_append hprefix tailTrace_7598474
  have hstable : (prefixWord ++ tailWord_7598474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598474).length < 2 ^ (prefixWord ++ tailWord_7598474).sum := by decide
  have hdescent : baseEnd_7598474 < baseStart_7598474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598496 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_7598496 : Nat := 118140960795 + 7598496 * 2 ^ 59
def prefixEnd_7598496 : Nat := 4983230072969 + 3 ^ 40 * 7598496 * 2
def baseEnd_7598496 : Nat := 3901680699266008083155159

theorem tailTrace_7598496 : CollatzResearch.WordTrace tailWord_7598496 prefixEnd_7598496 3901680699266008083155159 := by
  unfold tailWord_7598496
  simp only [CollatzResearch.WordTrace]
  refine ⟨138569958539977093322579671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184759944719969457763439561 138569958539977093322579671)
  ·
    refine ⟨207854937809965639983869507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138569958539977093322579671 207854937809965639983869507)
    ·
      refine ⟨311782406714948459975804261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207854937809965639983869507 311782406714948459975804261)
      ·
        refine ⟨58459201259052836245463299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311782406714948459975804261 58459201259052836245463299)
        ·
          refine ⟨87688801888579254368194949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58459201259052836245463299 87688801888579254368194949)
          ·
            refine ⟨16441650354108610194036553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87688801888579254368194949 16441650354108610194036553)
            ·
              refine ⟨12331237765581457645527415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16441650354108610194036553 12331237765581457645527415)
              ·
                refine ⟨18496856648372186468291123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12331237765581457645527415 18496856648372186468291123)
                ·
                  refine ⟨27745284972558279702436685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18496856648372186468291123 27745284972558279702436685)
                  ·
                    refine ⟨10404481864709354888413757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27745284972558279702436685 10404481864709354888413757)
                    ·
                      refine ⟨3901680699266008083155159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404481864709354888413757 3901680699266008083155159)
                      ·
                        rfl

theorem cell23_7598496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_7598496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598496 prefixEnd_7598496 := by exact prefixLift 7598496
  have htrace : WordTrace (prefixWord ++ tailWord_7598496) baseStart_7598496 baseEnd_7598496 := by
    simpa [prefixWord, tailWord_7598496, baseEnd_7598496] using wordTrace_append hprefix tailTrace_7598496
  have hstable : (prefixWord ++ tailWord_7598496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598496).length < 2 ^ (prefixWord ++ tailWord_7598496).sum := by decide
  have hdescent : baseEnd_7598496 < baseStart_7598496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598517 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_7598517 : Nat := 118140960795 + 7598517 * 2 ^ 59
def prefixEnd_7598517 : Nat := 4983230072969 + 3 ^ 40 * 7598517 * 2
def baseEnd_7598517 : Nat := 3901691482359752500992563

theorem tailTrace_7598517 : CollatzResearch.WordTrace tailWord_7598517 prefixEnd_7598517 3901691482359752500992563 := by
  unfold tailWord_7598517
  simp only [CollatzResearch.WordTrace]
  refine ⟨277140683012878107231673805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184760455341918738154449203 277140683012878107231673805)
  ·
    refine ⟨103927756129829290211877677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277140683012878107231673805 103927756129829290211877677)
    ·
      refine ⟨38972908548685983829454129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103927756129829290211877677 38972908548685983829454129)
      ·
        refine ⟨29229681411514487872090597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38972908548685983829454129 29229681411514487872090597)
        ·
          refine ⟨5480565264658966476016987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29229681411514487872090597 5480565264658966476016987)
          ·
            refine ⟨8220847896988449714025481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480565264658966476016987 8220847896988449714025481)
            ·
              refine ⟨6165635922741337285519111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220847896988449714025481 6165635922741337285519111)
              ·
                refine ⟨9248453884112005928278667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165635922741337285519111 9248453884112005928278667)
                ·
                  refine ⟨13872680826168008892418001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248453884112005928278667 13872680826168008892418001)
                  ·
                    refine ⟨10404510619626006669313501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13872680826168008892418001 10404510619626006669313501)
                    ·
                      refine ⟨3901691482359752500992563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404510619626006669313501 3901691482359752500992563)
                      ·
                        rfl

theorem cell23_7598517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_7598517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598517 prefixEnd_7598517 := by exact prefixLift 7598517
  have htrace : WordTrace (prefixWord ++ tailWord_7598517) baseStart_7598517 baseEnd_7598517 := by
    simpa [prefixWord, tailWord_7598517, baseEnd_7598517] using wordTrace_append hprefix tailTrace_7598517
  have hstable : (prefixWord ++ tailWord_7598517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598517).length < 2 ^ (prefixWord ++ tailWord_7598517).sum := by decide
  have hdescent : baseEnd_7598517 < baseStart_7598517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598559 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 7]
def baseStart_7598559 : Nat := 118140960795 + 7598559 * 2 ^ 59
def prefixEnd_7598559 : Nat := 4983230072969 + 3 ^ 40 * 7598559 * 2
def baseEnd_7598559 : Nat := 433523672060804592963041

theorem tailTrace_7598559 : CollatzResearch.WordTrace tailWord_7598559 prefixEnd_7598559 433523672060804592963041 := by
  unfold tailWord_7598559
  simp only [CollatzResearch.WordTrace]
  refine ⟨277142214878725948404702731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184761476585817298936468487 277142214878725948404702731)
  ·
    refine ⟨415713322318088922607054097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277142214878725948404702731 415713322318088922607054097)
    ·
      refine ⟨311784991738566691955290573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415713322318088922607054097 311784991738566691955290573)
      ·
        refine ⟨116919371901962509483233965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311784991738566691955290573 116919371901962509483233965)
        ·
          refine ⟨43844764463235941056212737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116919371901962509483233965 43844764463235941056212737)
          ·
            refine ⟨32883573347426955792159553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43844764463235941056212737 32883573347426955792159553)
            ·
              refine ⟨24662680010570216844119665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32883573347426955792159553 24662680010570216844119665)
              ·
                refine ⟨18497010007927662633089749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24662680010570216844119665 18497010007927662633089749)
                ·
                  refine ⟨433523672060804592963041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18497010007927662633089749 433523672060804592963041)
                  ·
                    rfl

theorem cell23_7598559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 7].length) (baseStart_7598559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598559 prefixEnd_7598559 := by exact prefixLift 7598559
  have htrace : WordTrace (prefixWord ++ tailWord_7598559) baseStart_7598559 baseEnd_7598559 := by
    simpa [prefixWord, tailWord_7598559, baseEnd_7598559] using wordTrace_append hprefix tailTrace_7598559
  have hstable : (prefixWord ++ tailWord_7598559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598559).length < 2 ^ (prefixWord ++ tailWord_7598559).sum := by decide
  have hdescent : baseEnd_7598559 < baseStart_7598559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598569 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_7598569 : Nat := 118140960795 + 7598569 * 2 ^ 59
def prefixEnd_7598569 : Nat := 4983230072969 + 3 ^ 40 * 7598569 * 2
def baseEnd_7598569 : Nat := 3901718183353786297542323

theorem tailTrace_7598569 : CollatzResearch.WordTrace tailWord_7598569 prefixEnd_7598569 3901718183353786297542323 := by
  unfold tailWord_7598569
  simp only [CollatzResearch.WordTrace]
  refine ⟨277142579608689720112566761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184761719739126480075044507 277142579608689720112566761)
  ·
    refine ⟨207856934706517290084425071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277142579608689720112566761 207856934706517290084425071)
    ·
      refine ⟨311785402059775935126637607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207856934706517290084425071 311785402059775935126637607)
      ·
        refine ⟨467678103089663902689956411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311785402059775935126637607 467678103089663902689956411)
        ·
          refine ⟨701517154634495854034934617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467678103089663902689956411 701517154634495854034934617)
          ·
            refine ⟨526137865975871890526200963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701517154634495854034934617 526137865975871890526200963)
            ·
              refine ⟨789206798963807835789301445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526137865975871890526200963 789206798963807835789301445)
              ·
                refine ⟨147976274805713969210494021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789206798963807835789301445 147976274805713969210494021)
                ·
                  refine ⟨27745551526071369226967629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147976274805713969210494021 27745551526071369226967629)
                  ·
                    refine ⟨10404581822276763460112861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27745551526071369226967629 10404581822276763460112861)
                    ·
                      refine ⟨3901718183353786297542323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404581822276763460112861 3901718183353786297542323)
                      ·
                        rfl

theorem cell23_7598569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_7598569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598569 prefixEnd_7598569 := by exact prefixLift 7598569
  have htrace : WordTrace (prefixWord ++ tailWord_7598569) baseStart_7598569 baseEnd_7598569 := by
    simpa [prefixWord, tailWord_7598569, baseEnd_7598569] using wordTrace_append hprefix tailTrace_7598569
  have hstable : (prefixWord ++ tailWord_7598569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598569).length < 2 ^ (prefixWord ++ tailWord_7598569).sum := by decide
  have hdescent : baseEnd_7598569 < baseStart_7598569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598609 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_7598609 : Nat := 118140960795 + 7598609 * 2 ^ 59
def prefixEnd_7598609 : Nat := 4983230072969 + 3 ^ 40 * 7598609 * 2
def baseEnd_7598609 : Nat := 3901738722579966141042139

theorem tailTrace_7598609 : CollatzResearch.WordTrace tailWord_7598609 prefixEnd_7598609 3901738722579966141042139 := by
  unfold tailWord_7598609
  simp only [CollatzResearch.WordTrace]
  refine ⟨277144038528544806944022881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184762692352363204629348587 277144038528544806944022881)
  ·
    refine ⟨207858028896408605208017161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277144038528544806944022881 207858028896408605208017161)
    ·
      refine ⟨155893521672306453906012871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207858028896408605208017161 155893521672306453906012871)
      ·
        refine ⟨233840282508459680859019307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155893521672306453906012871 233840282508459680859019307)
        ·
          refine ⟨350760423762689521288528961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233840282508459680859019307 350760423762689521288528961)
          ·
            refine ⟨263070317822017140966396721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350760423762689521288528961 263070317822017140966396721)
            ·
              refine ⟨197302738366512855724797541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263070317822017140966396721 197302738366512855724797541)
              ·
                refine ⟨36994263443721160448399539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197302738366512855724797541 36994263443721160448399539)
                ·
                  refine ⟨55491395165581740672599309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36994263443721160448399539 55491395165581740672599309)
                  ·
                    refine ⟨20809273187093152752224741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55491395165581740672599309 20809273187093152752224741)
                    ·
                      refine ⟨3901738722579966141042139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20809273187093152752224741 3901738722579966141042139)
                      ·
                        rfl

theorem cell23_7598609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_7598609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598609 prefixEnd_7598609 := by exact prefixLift 7598609
  have htrace : WordTrace (prefixWord ++ tailWord_7598609) baseStart_7598609 baseEnd_7598609 := by
    simpa [prefixWord, tailWord_7598609, baseEnd_7598609] using wordTrace_append hprefix tailTrace_7598609
  have hstable : (prefixWord ++ tailWord_7598609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598609).length < 2 ^ (prefixWord ++ tailWord_7598609).sum := by decide
  have hdescent : baseEnd_7598609 < baseStart_7598609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598644 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 5]
def baseStart_7598644 : Nat := 118140960795 + 7598644 * 2 ^ 59
def prefixEnd_7598644 : Nat := 4983230072969 + 3 ^ 40 * 7598644 * 2
def baseEnd_7598644 : Nat := 433528521600319278233831

theorem tailTrace_7598644 : CollatzResearch.WordTrace tailWord_7598644 prefixEnd_7598644 433528521600319278233831 := by
  unfold tailWord_7598644
  simp only [CollatzResearch.WordTrace]
  refine ⟨138572657541709003960773493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184763543388945338614364657 138572657541709003960773493)
  ·
    refine ⟨12991186644535219121322515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138572657541709003960773493 12991186644535219121322515)
    ·
      refine ⟨19486779966802828681983773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12991186644535219121322515 19486779966802828681983773)
      ·
        refine ⟨7307542487551060755743915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19486779966802828681983773 7307542487551060755743915)
        ·
          refine ⟨10961313731326591133615873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307542487551060755743915 10961313731326591133615873)
          ·
            refine ⟨8220985298494943350211905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10961313731326591133615873 8220985298494943350211905)
            ·
              refine ⟨6165738973871207512658929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220985298494943350211905 6165738973871207512658929)
              ·
                refine ⟨4624304230403405634494197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165738973871207512658929 4624304230403405634494197)
                ·
                  refine ⟨433528521600319278233831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624304230403405634494197 433528521600319278233831)
                  ·
                    rfl

theorem cell23_7598644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_7598644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598644 prefixEnd_7598644 := by exact prefixLift 7598644
  have htrace : WordTrace (prefixWord ++ tailWord_7598644) baseStart_7598644 baseEnd_7598644 := by
    simpa [prefixWord, tailWord_7598644, baseEnd_7598644] using wordTrace_append hprefix tailTrace_7598644
  have hstable : (prefixWord ++ tailWord_7598644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598644).length < 2 ^ (prefixWord ++ tailWord_7598644).sum := by decide
  have hdescent : baseEnd_7598644 < baseStart_7598644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598666 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_7598666 : Nat := 118140960795 + 7598666 * 2 ^ 59
def prefixEnd_7598666 : Nat := 4983230072969 + 3 ^ 40 * 7598666 * 2
def baseEnd_7598666 : Nat := 433529776775252490892153

theorem tailTrace_7598666 : CollatzResearch.WordTrace tailWord_7598666 prefixEnd_7598666 433529776775252490892153 := by
  unfold tailWord_7598666
  simp only [CollatzResearch.WordTrace]
  refine ⟨69286529372334576419711963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184764078326225537119231901 69286529372334576419711963)
  ·
    refine ⟨103929794058501864629567945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69286529372334576419711963 103929794058501864629567945)
    ·
      refine ⟨77947345543876398472175959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103929794058501864629567945 77947345543876398472175959)
      ·
        refine ⟨116921018315814597708263939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77947345543876398472175959 116921018315814597708263939)
        ·
          refine ⟨175381527473721896562395909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116921018315814597708263939 175381527473721896562395909)
          ·
            refine ⟨32884036401322855605449233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175381527473721896562395909 32884036401322855605449233)
            ·
              refine ⟨24663027300992141704086925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32884036401322855605449233 24663027300992141704086925)
              ·
                refine ⟨9248635237872053139032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24663027300992141704086925 9248635237872053139032597)
                ·
                  refine ⟨433529776775252490892153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9248635237872053139032597 433529776775252490892153)
                  ·
                    rfl

theorem cell23_7598666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_7598666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598666 prefixEnd_7598666 := by exact prefixLift 7598666
  have htrace : WordTrace (prefixWord ++ tailWord_7598666) baseStart_7598666 baseEnd_7598666 := by
    simpa [prefixWord, tailWord_7598666, baseEnd_7598666] using wordTrace_append hprefix tailTrace_7598666
  have hstable : (prefixWord ++ tailWord_7598666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598666).length < 2 ^ (prefixWord ++ tailWord_7598666).sum := by decide
  have hdescent : baseEnd_7598666 < baseStart_7598666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598703 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 2, 3, 2]
def baseStart_7598703 : Nat := 118140960795 + 7598703 * 2 ^ 59
def prefixEnd_7598703 : Nat := 4983230072969 + 3 ^ 40 * 7598703 * 2
def baseEnd_7598703 : Nat := 3901786989761488773266707

theorem tailTrace_7598703 : CollatzResearch.WordTrace tailWord_7598703 prefixEnd_7598703 3901786989761488773266707 := by
  unfold tailWord_7598703
  simp only [CollatzResearch.WordTrace]
  refine ⟨277147466990204260997944763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184764977993469507331963175 277147466990204260997944763)
  ·
    refine ⟨415721200485306391496917145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277147466990204260997944763 415721200485306391496917145)
    ·
      refine ⟨311790900363979793622687859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415721200485306391496917145 311790900363979793622687859)
      ·
        refine ⟨467686350545969690434031789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311790900363979793622687859 467686350545969690434031789)
        ·
          refine ⟨175382381454738633912761921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467686350545969690434031789 175382381454738633912761921)
          ·
            refine ⟨131536786091053975434571441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175382381454738633912761921 131536786091053975434571441)
            ·
              refine ⟨98652589568290481575928581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131536786091053975434571441 98652589568290481575928581)
              ·
                refine ⟨18497360544054465295486609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98652589568290481575928581 18497360544054465295486609)
                ·
                  refine ⟨13873020408040848971614957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18497360544054465295486609 13873020408040848971614957)
                  ·
                    refine ⟨5202382653015318364355609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13873020408040848971614957 5202382653015318364355609)
                    ·
                      refine ⟨3901786989761488773266707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202382653015318364355609 3901786989761488773266707)
                      ·
                        rfl

theorem cell23_7598703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3, 2].length) (baseStart_7598703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598703 prefixEnd_7598703 := by exact prefixLift 7598703
  have htrace : WordTrace (prefixWord ++ tailWord_7598703) baseStart_7598703 baseEnd_7598703 := by
    simpa [prefixWord, tailWord_7598703, baseEnd_7598703] using wordTrace_append hprefix tailTrace_7598703
  have hstable : (prefixWord ++ tailWord_7598703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598703).length < 2 ^ (prefixWord ++ tailWord_7598703).sum := by decide
  have hdescent : baseEnd_7598703 < baseStart_7598703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598716 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_7598716 : Nat := 118140960795 + 7598716 * 2 ^ 59
def prefixEnd_7598716 : Nat := 4983230072969 + 3 ^ 40 * 7598716 * 2
def baseEnd_7598716 : Nat := 3901793665009997222404147

theorem tailTrace_7598716 : CollatzResearch.WordTrace tailWord_7598716 prefixEnd_7598716 3901793665009997222404147 := by
  unfold tailWord_7598716
  simp only [CollatzResearch.WordTrace]
  refine ⟨138573970569578582109084001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184765294092771442812112001 138573970569578582109084001)
  ·
    refine ⟨103930477927183936581813001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138573970569578582109084001 103930477927183936581813001)
    ·
      refine ⟨77947858445387952436359751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103930477927183936581813001 77947858445387952436359751)
      ·
        refine ⟨116921787668081928654539627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77947858445387952436359751 116921787668081928654539627)
        ·
          refine ⟨175382681502122892981809441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116921787668081928654539627 175382681502122892981809441)
          ·
            refine ⟨131537011126592169736357081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175382681502122892981809441 131537011126592169736357081)
            ·
              refine ⟨98652758344944127302267811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131537011126592169736357081 98652758344944127302267811)
              ·
                refine ⟨147979137517416190953401717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98652758344944127302267811 147979137517416190953401717)
                ·
                  refine ⟨13873044142257767901881411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147979137517416190953401717 13873044142257767901881411)
                  ·
                    refine ⟨20809566213386651852822117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13873044142257767901881411 20809566213386651852822117)
                    ·
                      refine ⟨3901793665009997222404147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20809566213386651852822117 3901793665009997222404147)
                      ·
                        rfl

theorem cell23_7598716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_7598716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598716 prefixEnd_7598716 := by exact prefixLift 7598716
  have htrace : WordTrace (prefixWord ++ tailWord_7598716) baseStart_7598716 baseEnd_7598716 := by
    simpa [prefixWord, tailWord_7598716, baseEnd_7598716] using wordTrace_append hprefix tailTrace_7598716
  have hstable : (prefixWord ++ tailWord_7598716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598716).length < 2 ^ (prefixWord ++ tailWord_7598716).sum := by decide
  have hdescent : baseEnd_7598716 < baseStart_7598716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598730 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_7598730 : Nat := 118140960795 + 7598730 * 2 ^ 59
def prefixEnd_7598730 : Nat := 4983230072969 + 3 ^ 40 * 7598730 * 2
def baseEnd_7598730 : Nat := 1300600284579720055876361

theorem tailTrace_7598730 : CollatzResearch.WordTrace tailWord_7598730 prefixEnd_7598730 1300600284579720055876361 := by
  unfold tailWord_7598730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69287112940276611152294411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184765634507404296406118429 69287112940276611152294411)
  ·
    refine ⟨103930669410414916728441617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69287112940276611152294411 103930669410414916728441617)
    ·
      refine ⟨77948002057811187546331213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103930669410414916728441617 77948002057811187546331213)
      ·
        refine ⟨29230500771679195329874205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77948002057811187546331213 29230500771679195329874205)
        ·
          refine ⟨10961437789379698248702827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29230500771679195329874205 10961437789379698248702827)
          ·
            refine ⟨16442156684069547373054241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961437789379698248702827 16442156684069547373054241)
            ·
              refine ⟨12331617513052160529790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16442156684069547373054241 12331617513052160529790681)
              ·
                refine ⟨9248713134789120397343011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12331617513052160529790681 9248713134789120397343011)
                ·
                  refine ⟨13873069702183680596014517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248713134789120397343011 13873069702183680596014517)
                  ·
                    refine ⟨1300600284579720055876361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13873069702183680596014517 1300600284579720055876361)
                    ·
                      rfl

theorem cell23_7598730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_7598730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598730 prefixEnd_7598730 := by exact prefixLift 7598730
  have htrace : WordTrace (prefixWord ++ tailWord_7598730) baseStart_7598730 baseEnd_7598730 := by
    simpa [prefixWord, tailWord_7598730, baseEnd_7598730] using wordTrace_append hprefix tailTrace_7598730
  have hstable : (prefixWord ++ tailWord_7598730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598730).length < 2 ^ (prefixWord ++ tailWord_7598730).sum := by decide
  have hdescent : baseEnd_7598730 < baseStart_7598730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598739 : List Nat := [1, 1, 1, 2, 1, 2, 2, 13]
def baseStart_7598739 : Nat := 118140960795 + 7598739 * 2 ^ 59
def prefixEnd_7598739 : Nat := 4983230072969 + 3 ^ 40 * 7598739 * 2
def baseEnd_7598739 : Nat := 144511313891298171570983

theorem tailTrace_7598739 : CollatzResearch.WordTrace tailWord_7598739 prefixEnd_7598739 144511313891298171570983 := by
  unfold tailWord_7598739
  simp only [CollatzResearch.WordTrace]
  refine ⟨277148780018073839146255271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184765853345382559430836847 277148780018073839146255271)
  ·
    refine ⟨415723170027110758719382907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277148780018073839146255271 415723170027110758719382907)
    ·
      refine ⟨623584755040666138079074361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415723170027110758719382907 623584755040666138079074361)
      ·
        refine ⟨467688566280499603559305771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623584755040666138079074361 467688566280499603559305771)
        ·
          refine ⟨701532849420749405338958657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467688566280499603559305771 701532849420749405338958657)
          ·
            refine ⟨526149637065562054004218993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701532849420749405338958657 526149637065562054004218993)
            ·
              refine ⟨394612227799171540503164245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526149637065562054004218993 394612227799171540503164245)
              ·
                refine ⟨144511313891298171570983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 394612227799171540503164245 144511313891298171570983)
                ·
                  rfl

theorem cell23_7598739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 13].length) (baseStart_7598739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598739 prefixEnd_7598739 := by exact prefixLift 7598739
  have htrace : WordTrace (prefixWord ++ tailWord_7598739) baseStart_7598739 baseEnd_7598739 := by
    simpa [prefixWord, tailWord_7598739, baseEnd_7598739] using wordTrace_append hprefix tailTrace_7598739
  have hstable : (prefixWord ++ tailWord_7598739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598739).length < 2 ^ (prefixWord ++ tailWord_7598739).sum := by decide
  have hdescent : baseEnd_7598739 < baseStart_7598739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598750 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7598750 : Nat := 118140960795 + 7598750 * 2 ^ 59
def prefixEnd_7598750 : Nat := 4983230072969 + 3 ^ 40 * 7598750 * 2
def baseEnd_7598750 : Nat := 3901811123352250089378991

theorem tailTrace_7598750 : CollatzResearch.WordTrace tailWord_7598750 prefixEnd_7598750 3901811123352250089378991 := by
  unfold tailWord_7598750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643647652629248503113213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184766120814022658683270469 34643647652629248503113213)
  ·
    refine ⟨12991367869735968188667455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34643647652629248503113213 12991367869735968188667455)
    ·
      refine ⟨19487051804603952283001183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12991367869735968188667455 19487051804603952283001183)
      ·
        refine ⟨29230577706905928424501775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19487051804603952283001183 29230577706905928424501775)
        ·
          refine ⟨43845866560358892636752663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29230577706905928424501775 43845866560358892636752663)
          ·
            refine ⟨65768799840538338955128995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43845866560358892636752663 65768799840538338955128995)
            ·
              refine ⟨98653199760807508432693493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65768799840538338955128995 98653199760807508432693493)
              ·
                refine ⟨9248737477575703915565015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98653199760807508432693493 9248737477575703915565015)
                ·
                  refine ⟨13873106216363555873347523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248737477575703915565015 13873106216363555873347523)
                  ·
                    refine ⟨20809659324545333810021285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13873106216363555873347523 20809659324545333810021285)
                    ·
                      refine ⟨3901811123352250089378991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20809659324545333810021285 3901811123352250089378991)
                      ·
                        rfl

theorem cell23_7598750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7598750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598750 prefixEnd_7598750 := by exact prefixLift 7598750
  have htrace : WordTrace (prefixWord ++ tailWord_7598750) baseStart_7598750 baseEnd_7598750 := by
    simpa [prefixWord, tailWord_7598750, baseEnd_7598750] using wordTrace_append hprefix tailTrace_7598750
  have hstable : (prefixWord ++ tailWord_7598750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598750).length < 2 ^ (prefixWord ++ tailWord_7598750).sum := by decide
  have hdescent : baseEnd_7598750 < baseStart_7598750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598767 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 3, 2, 2]
def baseStart_7598767 : Nat := 118140960795 + 7598767 * 2 ^ 59
def prefixEnd_7598767 : Nat := 4983230072969 + 3 ^ 40 * 7598767 * 2
def baseEnd_7598767 : Nat := 3901819852523376522866413

theorem tailTrace_7598767 : CollatzResearch.WordTrace tailWord_7598767 prefixEnd_7598767 3901819852523376522866413 := by
  unfold tailWord_7598767
  simp only [CollatzResearch.WordTrace]
  refine ⟨277149801261972399928274555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184766534174648266618849703 277149801261972399928274555)
  ·
    refine ⟨415724701892958599892411833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277149801261972399928274555 415724701892958599892411833)
    ·
      refine ⟨311793526419718949919308875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415724701892958599892411833 311793526419718949919308875)
      ·
        refine ⟨467690289629578424878963313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311793526419718949919308875 467690289629578424878963313)
        ·
          refine ⟨350767717222183818659222485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467690289629578424878963313 350767717222183818659222485)
          ·
            refine ⟨8221118372394933249825527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 350767717222183818659222485 8221118372394933249825527)
            ·
              refine ⟨12331677558592399874738291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221118372394933249825527 12331677558592399874738291)
              ·
                refine ⟨18497516337888599812107437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12331677558592399874738291 18497516337888599812107437)
                ·
                  refine ⟨6936568626708224929540289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18497516337888599812107437 6936568626708224929540289)
                  ·
                    refine ⟨5202426470031168697155217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6936568626708224929540289 5202426470031168697155217)
                    ·
                      refine ⟨3901819852523376522866413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202426470031168697155217 3901819852523376522866413)
                      ·
                        rfl

theorem cell23_7598767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2, 2].length) (baseStart_7598767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598767 prefixEnd_7598767 := by exact prefixLift 7598767
  have htrace : WordTrace (prefixWord ++ tailWord_7598767) baseStart_7598767 baseEnd_7598767 := by
    simpa [prefixWord, tailWord_7598767, baseEnd_7598767] using wordTrace_append hprefix tailTrace_7598767
  have hstable : (prefixWord ++ tailWord_7598767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598767).length < 2 ^ (prefixWord ++ tailWord_7598767).sum := by decide
  have hdescent : baseEnd_7598767 < baseStart_7598767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598773 : List Nat := [1, 3, 3, 3, 1, 2, 2, 8]
def baseStart_7598773 : Nat := 118140960795 + 7598773 * 2 ^ 59
def prefixEnd_7598773 : Nat := 4983230072969 + 3 ^ 40 * 7598773 * 2
def baseEnd_7598773 : Nat := 144511960496566796273755

theorem tailTrace_7598773 : CollatzResearch.WordTrace tailWord_7598773 prefixEnd_7598773 144511960496566796273755 := by
  unfold tailWord_7598773
  simp only [CollatzResearch.WordTrace]
  refine ⟨277150020099950662952992973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184766680066633775301995315 277150020099950662952992973)
  ·
    refine ⟨103931257537481498607372365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277150020099950662952992973 103931257537481498607372365)
    ·
      refine ⟨38974221576555561977764637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103931257537481498607372365 38974221576555561977764637)
      ·
        refine ⟨14615333091208335741661739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38974221576555561977764637 14615333091208335741661739)
        ·
          refine ⟨21922999636812503612492609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14615333091208335741661739 21922999636812503612492609)
          ·
            refine ⟨16442249727609377709369457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21922999636812503612492609 16442249727609377709369457)
            ·
              refine ⟨12331687295707033282027093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16442249727609377709369457 12331687295707033282027093)
              ·
                refine ⟨144511960496566796273755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12331687295707033282027093 144511960496566796273755)
                ·
                  rfl

theorem cell23_7598773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 8].length) (baseStart_7598773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598773 prefixEnd_7598773 := by exact prefixLift 7598773
  have htrace : WordTrace (prefixWord ++ tailWord_7598773) baseStart_7598773 baseEnd_7598773 := by
    simpa [prefixWord, tailWord_7598773, baseEnd_7598773] using wordTrace_append hprefix tailTrace_7598773
  have hstable : (prefixWord ++ tailWord_7598773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598773).length < 2 ^ (prefixWord ++ tailWord_7598773).sum := by decide
  have hdescent : baseEnd_7598773 < baseStart_7598773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598797 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7598797 : Nat := 118140960795 + 7598797 * 2 ^ 59
def prefixEnd_7598797 : Nat := 4983230072969 + 3 ^ 40 * 7598797 * 2
def baseEnd_7598797 : Nat := 3901835256943011405491275

theorem tailTrace_7598797 : CollatzResearch.WordTrace tailWord_7598797 prefixEnd_7598797 3901835256943011405491275 := by
  unfold tailWord_7598797
  simp only [CollatzResearch.WordTrace]
  refine ⟨277150895451863715051866645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184767263634575810034577763 277150895451863715051866645)
  ·
    refine ⟨12991448224306111643056249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277150895451863715051866645 12991448224306111643056249)
    ·
      refine ⟨9743586168229583732292187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12991448224306111643056249 9743586168229583732292187)
      ·
        refine ⟨14615379252344375598438281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9743586168229583732292187 14615379252344375598438281)
        ·
          refine ⟨10961534439258281698828711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14615379252344375598438281 10961534439258281698828711)
          ·
            refine ⟨16442301658887422548243067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961534439258281698828711 16442301658887422548243067)
            ·
              refine ⟨24663452488331133822364601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442301658887422548243067 24663452488331133822364601)
              ·
                refine ⟨18497589366248350366773451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24663452488331133822364601 18497589366248350366773451)
                ·
                  refine ⟨27746384049372525550160177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18497589366248350366773451 27746384049372525550160177)
                  ·
                    refine ⟨20809788037029394162620133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27746384049372525550160177 20809788037029394162620133)
                    ·
                      refine ⟨3901835256943011405491275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20809788037029394162620133 3901835256943011405491275)
                      ·
                        rfl

theorem cell23_7598797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7598797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598797 prefixEnd_7598797 := by exact prefixLift 7598797
  have htrace : WordTrace (prefixWord ++ tailWord_7598797) baseStart_7598797 baseEnd_7598797 := by
    simpa [prefixWord, tailWord_7598797, baseEnd_7598797] using wordTrace_append hprefix tailTrace_7598797
  have hstable : (prefixWord ++ tailWord_7598797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598797).length < 2 ^ (prefixWord ++ tailWord_7598797).sum := by decide
  have hdescent : baseEnd_7598797 < baseStart_7598797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598804 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7598804 : Nat := 118140960795 + 7598804 * 2 ^ 59
def prefixEnd_7598804 : Nat := 4983230072969 + 3 ^ 40 * 7598804 * 2
def baseEnd_7598804 : Nat := 3901838851307592878103743

theorem tailTrace_7598804 : CollatzResearch.WordTrace tailWord_7598804 prefixEnd_7598804 3901838851307592878103743 := by
  unfold tailWord_7598804
  simp only [CollatzResearch.WordTrace]
  refine ⟨138575575381419177623685733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184767433841892236831580977 138575575381419177623685733)
  ·
    refine ⟨25982920384016095804441075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138575575381419177623685733 25982920384016095804441075)
    ·
      refine ⟨38974380576024143706661613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25982920384016095804441075 38974380576024143706661613)
      ·
        refine ⟨14615392716009053889998105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38974380576024143706661613 14615392716009053889998105)
        ·
          refine ⟨10961544537006790417498579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14615392716009053889998105 10961544537006790417498579)
          ·
            refine ⟨16442316805510185626247869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961544537006790417498579 16442316805510185626247869)
            ·
              refine ⟨6165868802066319609842951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16442316805510185626247869 6165868802066319609842951)
              ·
                refine ⟨9248803203099479414764427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165868802066319609842951 9248803203099479414764427)
                ·
                  refine ⟨13873204804649219122146641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248803203099479414764427 13873204804649219122146641)
                  ·
                    refine ⟨10404903603486914341609981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13873204804649219122146641 10404903603486914341609981)
                    ·
                      refine ⟨3901838851307592878103743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404903603486914341609981 3901838851307592878103743)
                      ·
                        rfl

theorem cell23_7598804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7598804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598804 prefixEnd_7598804 := by exact prefixLift 7598804
  have htrace : WordTrace (prefixWord ++ tailWord_7598804) baseStart_7598804 baseEnd_7598804 := by
    simpa [prefixWord, tailWord_7598804, baseEnd_7598804] using wordTrace_append hprefix tailTrace_7598804
  have hstable : (prefixWord ++ tailWord_7598804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598804).length < 2 ^ (prefixWord ++ tailWord_7598804).sum := by decide
  have hdescent : baseEnd_7598804 < baseStart_7598804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598816 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_7598816 : Nat := 118140960795 + 7598816 * 2 ^ 59
def prefixEnd_7598816 : Nat := 4983230072969 + 3 ^ 40 * 7598816 * 2
def baseEnd_7598816 : Nat := 1300615004358482277051229

theorem tailTrace_7598816 : CollatzResearch.WordTrace tailWord_7598816 prefixEnd_7598816 1300615004358482277051229 := by
  unfold tailWord_7598816
  simp only [CollatzResearch.WordTrace]
  refine ⟨138575794219397440648404151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184767725625863254197872201 138575794219397440648404151)
  ·
    refine ⟨207863691329096160972606227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138575794219397440648404151 207863691329096160972606227)
    ·
      refine ⟨311795536993644241458909341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207863691329096160972606227 311795536993644241458909341)
      ·
        refine ⟨116923326372616590547091003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311795536993644241458909341 116923326372616590547091003)
        ·
          refine ⟨175384989558924885820636505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116923326372616590547091003 175384989558924885820636505)
          ·
            refine ⟨131538742169193664365477379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175384989558924885820636505 131538742169193664365477379)
            ·
              refine ⟨197308113253790496548216069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131538742169193664365477379 197308113253790496548216069)
              ·
                refine ⟨36995271235085718102790513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197308113253790496548216069 36995271235085718102790513)
                ·
                  refine ⟨27746453426314288577092885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36995271235085718102790513 27746453426314288577092885)
                  ·
                    refine ⟨1300615004358482277051229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27746453426314288577092885 1300615004358482277051229)
                    ·
                      rfl

theorem cell23_7598816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_7598816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598816 prefixEnd_7598816 := by exact prefixLift 7598816
  have htrace : WordTrace (prefixWord ++ tailWord_7598816) baseStart_7598816 baseEnd_7598816 := by
    simpa [prefixWord, tailWord_7598816, baseEnd_7598816] using wordTrace_append hprefix tailTrace_7598816
  have hstable : (prefixWord ++ tailWord_7598816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598816).length < 2 ^ (prefixWord ++ tailWord_7598816).sum := by decide
  have hdescent : baseEnd_7598816 < baseStart_7598816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598817 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_7598817 : Nat := 118140960795 + 7598817 * 2 ^ 59
def prefixEnd_7598817 : Nat := 4983230072969 + 3 ^ 40 * 7598817 * 2
def baseEnd_7598817 : Nat := 3901845526556101327241183

theorem tailTrace_7598817 : CollatzResearch.WordTrace tailWord_7598817 prefixEnd_7598817 3901845526556101327241183 := by
  unfold tailWord_7598817
  simp only [CollatzResearch.WordTrace]
  refine ⟨277151624911791258467594705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184767749941194172311729803 277151624911791258467594705)
  ·
    refine ⟨207863718683843443850696029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277151624911791258467594705 207863718683843443850696029)
    ·
      refine ⟨77948894506441291444011011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207863718683843443850696029 77948894506441291444011011)
      ·
        refine ⟨116923341759661937166016517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77948894506441291444011011 116923341759661937166016517)
        ·
          refine ⟨21923126579936613218628097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116923341759661937166016517 21923126579936613218628097)
          ·
            refine ⟨16442344934952459913971073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21923126579936613218628097 16442344934952459913971073)
            ·
              refine ⟨12331758701214344935478305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16442344934952459913971073 12331758701214344935478305)
              ·
                refine ⟨9248819025910758701608729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12331758701214344935478305 9248819025910758701608729)
                ·
                  refine ⟨6936614269433069026206547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9248819025910758701608729 6936614269433069026206547)
                  ·
                    refine ⟨10404921404149603539309821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6936614269433069026206547 10404921404149603539309821)
                    ·
                      refine ⟨3901845526556101327241183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10404921404149603539309821 3901845526556101327241183)
                      ·
                        rfl

theorem cell23_7598817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_7598817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598817 prefixEnd_7598817 := by exact prefixLift 7598817
  have htrace : WordTrace (prefixWord ++ tailWord_7598817) baseStart_7598817 baseEnd_7598817 := by
    simpa [prefixWord, tailWord_7598817, baseEnd_7598817] using wordTrace_append hprefix tailTrace_7598817
  have hstable : (prefixWord ++ tailWord_7598817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598817).length < 2 ^ (prefixWord ++ tailWord_7598817).sum := by decide
  have hdescent : baseEnd_7598817 < baseStart_7598817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598840 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_7598840 : Nat := 118140960795 + 7598840 * 2 ^ 59
def prefixEnd_7598840 : Nat := 4983230072969 + 3 ^ 40 * 7598840 * 2
def baseEnd_7598840 : Nat := 3901857336611154737253577

theorem tailTrace_7598840 : CollatzResearch.WordTrace tailWord_7598840 prefixEnd_7598840 3901857336611154737253577 := by
  unfold tailWord_7598840
  simp only [CollatzResearch.WordTrace]
  refine ⟨138576231895353966697840987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184768309193805288930454649 138576231895353966697840987)
  ·
    refine ⟨207864347843030950046761481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138576231895353966697840987 207864347843030950046761481)
    ·
      refine ⟨155898260882273212535071111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207864347843030950046761481 155898260882273212535071111)
      ·
        refine ⟨233847391323409818802606667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155898260882273212535071111 233847391323409818802606667)
        ·
          refine ⟨350771086985114728203910001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233847391323409818802606667 350771086985114728203910001)
          ·
            refine ⟨263078315238836046152932501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350771086985114728203910001 263078315238836046152932501)
            ·
              refine ⟨12331796026820439663418711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263078315238836046152932501 12331796026820439663418711)
              ·
                refine ⟨18497694040230659495128067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12331796026820439663418711 18497694040230659495128067)
                ·
                  refine ⟨27746541060345989242692101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18497694040230659495128067 27746541060345989242692101)
                  ·
                    refine ⟨5202476448814872983004769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27746541060345989242692101 5202476448814872983004769)
                    ·
                      refine ⟨3901857336611154737253577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202476448814872983004769 3901857336611154737253577)
                      ·
                        rfl

theorem cell23_7598840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_7598840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598840 prefixEnd_7598840 := by exact prefixLift 7598840
  have htrace : WordTrace (prefixWord ++ tailWord_7598840) baseStart_7598840 baseEnd_7598840 := by
    simpa [prefixWord, tailWord_7598840, baseEnd_7598840] using wordTrace_append hprefix tailTrace_7598840
  have hstable : (prefixWord ++ tailWord_7598840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598840).length < 2 ^ (prefixWord ++ tailWord_7598840).sum := by decide
  have hdescent : baseEnd_7598840 < baseStart_7598840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598880 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 5]
def baseStart_7598880 : Nat := 118140960795 + 7598880 * 2 ^ 59
def prefixEnd_7598880 : Nat := 4983230072969 + 3 ^ 40 * 7598880 * 2
def baseEnd_7598880 : Nat := 433541986204148286750377

theorem tailTrace_7598880 : CollatzResearch.WordTrace tailWord_7598880 prefixEnd_7598880 433541986204148286750377 := by
  unfold tailWord_7598880
  simp only [CollatzResearch.WordTrace]
  refine ⟨138576961355281510113569047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184769281807042013484758729 138576961355281510113569047)
  ·
    refine ⟨207865442032922265170353571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138576961355281510113569047 207865442032922265170353571)
    ·
      refine ⟨311798163049383397755530357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207865442032922265170353571 311798163049383397755530357)
      ·
        refine ⟨29231077785879693539580971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311798163049383397755530357 29231077785879693539580971)
        ·
          refine ⟨43846616678819540309371457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29231077785879693539580971 43846616678819540309371457)
          ·
            refine ⟨32884962509114655232028593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43846616678819540309371457 32884962509114655232028593)
            ·
              refine ⟨24663721881835991424021445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32884962509114655232028593 24663721881835991424021445)
              ·
                refine ⟨4624447852844248392004021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24663721881835991424021445 4624447852844248392004021)
                ·
                  refine ⟨433541986204148286750377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624447852844248392004021 433541986204148286750377)
                  ·
                    rfl

theorem cell23_7598880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 5].length) (baseStart_7598880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598880 prefixEnd_7598880 := by exact prefixLift 7598880
  have htrace : WordTrace (prefixWord ++ tailWord_7598880) baseStart_7598880 baseEnd_7598880 := by
    simpa [prefixWord, tailWord_7598880, baseEnd_7598880] using wordTrace_append hprefix tailTrace_7598880
  have hstable : (prefixWord ++ tailWord_7598880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598880).length < 2 ^ (prefixWord ++ tailWord_7598880).sum := by decide
  have hdescent : baseEnd_7598880 < baseStart_7598880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598930 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_7598930 : Nat := 118140960795 + 7598930 * 2 ^ 59
def prefixEnd_7598930 : Nat := 4983230072969 + 3 ^ 40 * 7598930 * 2
def baseEnd_7598930 : Nat := 3901903549870059385128163

theorem tailTrace_7598930 : CollatzResearch.WordTrace tailWord_7598930 prefixEnd_7598930 3901903549870059385128163 := by
  unfold tailWord_7598930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69288936590095469691614561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184770497573587919177638829 69288936590095469691614561)
  ·
    refine ⟨51966702442571602268710921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69288936590095469691614561 51966702442571602268710921)
    ·
      refine ⟨38975026831928701701533191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51966702442571602268710921 38975026831928701701533191)
      ·
        refine ⟨58462540247893052552299787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38975026831928701701533191 58462540247893052552299787)
        ·
          refine ⟨87693810371839578828449681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58462540247893052552299787 87693810371839578828449681)
          ·
            refine ⟨65770357778879684121337261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87693810371839578828449681 65770357778879684121337261)
            ·
              refine ⟨24663884167079881545501473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65770357778879684121337261 24663884167079881545501473)
              ·
                refine ⟨18497913125309911159126105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24663884167079881545501473 18497913125309911159126105)
                ·
                  refine ⟨13873434843982433369344579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18497913125309911159126105 13873434843982433369344579)
                  ·
                    refine ⟨20810152265973650054016869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13873434843982433369344579 20810152265973650054016869)
                    ·
                      refine ⟨3901903549870059385128163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20810152265973650054016869 3901903549870059385128163)
                      ·
                        rfl

theorem cell23_7598930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_7598930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598930 prefixEnd_7598930 := by exact prefixLift 7598930
  have htrace : WordTrace (prefixWord ++ tailWord_7598930) baseStart_7598930 baseEnd_7598930 := by
    simpa [prefixWord, tailWord_7598930, baseEnd_7598930] using wordTrace_append hprefix tailTrace_7598930
  have hstable : (prefixWord ++ tailWord_7598930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598930).length < 2 ^ (prefixWord ++ tailWord_7598930).sum := by decide
  have hdescent : baseEnd_7598930 < baseStart_7598930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7598963 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3]
def baseStart_7598963 : Nat := 118140960795 + 7598963 * 2 ^ 59
def prefixEnd_7598963 : Nat := 4983230072969 + 3 ^ 40 * 7598963 * 2
def baseEnd_7598963 : Nat := 3901920494731657756015511

theorem tailTrace_7598963 : CollatzResearch.WordTrace tailWord_7598963 prefixEnd_7598963 3901920494731657756015511 := by
  unfold tailWord_7598963
  simp only [CollatzResearch.WordTrace]
  refine ⟨277156949969262325402409543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184771299979508216934939695 277156949969262325402409543)
  ·
    refine ⟨415735424953893488103614315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277156949969262325402409543 415735424953893488103614315)
    ·
      refine ⟨623603137430840232155421473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415735424953893488103614315 623603137430840232155421473)
      ·
        refine ⟨467702353073130174116566105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623603137430840232155421473 467702353073130174116566105)
        ·
          refine ⟨350776764804847630587424579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467702353073130174116566105 350776764804847630587424579)
          ·
            refine ⟨526165147207271445881136869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350776764804847630587424579 526165147207271445881136869)
            ·
              refine ⟨98655965101363396102713163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526165147207271445881136869 98655965101363396102713163)
              ·
                refine ⟨147983947652045094154069745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98655965101363396102713163 147983947652045094154069745)
                ·
                  refine ⟨110987960739033820615552309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147983947652045094154069745 110987960739033820615552309)
                  ·
                    refine ⟨10405121319284420682708029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110987960739033820615552309 10405121319284420682708029)
                    ·
                      refine ⟨3901920494731657756015511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10405121319284420682708029 3901920494731657756015511)
                      ·
                        rfl

theorem cell23_7598963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_7598963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7598963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7598963 prefixEnd_7598963 := by exact prefixLift 7598963
  have htrace : WordTrace (prefixWord ++ tailWord_7598963) baseStart_7598963 baseEnd_7598963 := by
    simpa [prefixWord, tailWord_7598963, baseEnd_7598963] using wordTrace_append hprefix tailTrace_7598963
  have hstable : (prefixWord ++ tailWord_7598963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7598963).length < 2 ^ (prefixWord ++ tailWord_7598963).sum := by decide
  have hdescent : baseEnd_7598963 < baseStart_7598963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7598963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599020 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_7599020 : Nat := 118140960795 + 7599020 * 2 ^ 59
def prefixEnd_7599020 : Nat := 4983230072969 + 3 ^ 40 * 7599020 * 2
def baseEnd_7599020 : Nat := 3901949763128964033002749

theorem tailTrace_7599020 : CollatzResearch.WordTrace tailWord_7599020 prefixEnd_7599020 3901949763128964033002749 := by
  unfold tailWord_7599020
  simp only [CollatzResearch.WordTrace]
  refine ⟨138579514465027912068617257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184772685953370549424823009 138579514465027912068617257)
  ·
    refine ⟨103934635848770934051462943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138579514465027912068617257 103934635848770934051462943)
    ·
      refine ⟨155901953773156401077194415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103934635848770934051462943 155901953773156401077194415)
      ·
        refine ⟨233852930659734601615791623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155901953773156401077194415 233852930659734601615791623)
        ·
          refine ⟨350779395989601902423687435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233852930659734601615791623 350779395989601902423687435)
          ·
            refine ⟨526169093984402853635531153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350779395989601902423687435 526169093984402853635531153)
            ·
              refine ⟨394626820488302140226648365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526169093984402853635531153 394626820488302140226648365)
              ·
                refine ⟨147985057683113302584993137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394626820488302140226648365 147985057683113302584993137)
                ·
                  refine ⟨110988793262334976938744853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147985057683113302584993137 110988793262334976938744853)
                  ·
                    refine ⟨5202599684171952044003665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110988793262334976938744853 5202599684171952044003665)
                    ·
                      refine ⟨3901949763128964033002749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202599684171952044003665 3901949763128964033002749)
                      ·
                        rfl

theorem cell23_7599020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_7599020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599020 prefixEnd_7599020 := by exact prefixLift 7599020
  have htrace : WordTrace (prefixWord ++ tailWord_7599020) baseStart_7599020 baseEnd_7599020 := by
    simpa [prefixWord, tailWord_7599020, baseEnd_7599020] using wordTrace_append hprefix tailTrace_7599020
  have hstable : (prefixWord ++ tailWord_7599020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599020).length < 2 ^ (prefixWord ++ tailWord_7599020).sum := by decide
  have hdescent : baseEnd_7599020 < baseStart_7599020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599023 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_7599023 : Nat := 118140960795 + 7599023 * 2 ^ 59
def prefixEnd_7599023 : Nat := 4983230072969 + 3 ^ 40 * 7599023 * 2
def baseEnd_7599023 : Nat := 3901951303570927521265235

theorem tailTrace_7599023 : CollatzResearch.WordTrace tailWord_7599023 prefixEnd_7599023 3901951303570927521265235 := by
  unfold tailWord_7599023
  simp only [CollatzResearch.WordTrace]
  refine ⟨277159138349044955649593723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184772758899363303766395815 277159138349044955649593723)
  ·
    refine ⟨415738707523567433474390585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277159138349044955649593723 415738707523567433474390585)
    ·
      refine ⟨311804030642675575105792939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415738707523567433474390585 311804030642675575105792939)
      ·
        refine ⟨467706045964013362658689409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311804030642675575105792939 467706045964013362658689409)
        ·
          refine ⟨350779534473010021994017057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467706045964013362658689409 350779534473010021994017057)
          ·
            refine ⟨263084650854757516495512793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350779534473010021994017057 263084650854757516495512793)
            ·
              refine ⟨197313488141068137371634595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263084650854757516495512793 197313488141068137371634595)
              ·
                refine ⟨295970232211602206057451893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197313488141068137371634595 295970232211602206057451893)
                ·
                  refine ⟨27747209269837706817886115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295970232211602206057451893 27747209269837706817886115)
                  ·
                    refine ⟨41620813904756560226829173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27747209269837706817886115 41620813904756560226829173)
                    ·
                      refine ⟨3901951303570927521265235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41620813904756560226829173 3901951303570927521265235)
                      ·
                        rfl

theorem cell23_7599023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_7599023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599023 prefixEnd_7599023 := by exact prefixLift 7599023
  have htrace : WordTrace (prefixWord ++ tailWord_7599023) baseStart_7599023 baseEnd_7599023 := by
    simpa [prefixWord, tailWord_7599023, baseEnd_7599023] using wordTrace_append hprefix tailTrace_7599023
  have hstable : (prefixWord ++ tailWord_7599023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599023).length < 2 ^ (prefixWord ++ tailWord_7599023).sum := by decide
  have hdescent : baseEnd_7599023 < baseStart_7599023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599047 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 2, 4]
def baseStart_7599047 : Nat := 118140960795 + 7599047 * 2 ^ 59
def prefixEnd_7599047 : Nat := 4983230072969 + 3 ^ 40 * 7599047 * 2
def baseEnd_7599047 : Nat := 1300654542368878475788375

theorem tailTrace_7599047 : CollatzResearch.WordTrace tailWord_7599047 prefixEnd_7599047 1300654542368878475788375 := by
  unfold tailWord_7599047
  simp only [CollatzResearch.WordTrace]
  refine ⟨277160013700958007748467395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184773342467305338498978263 277160013700958007748467395)
  ·
    refine ⟨415740020551437011622701093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277160013700958007748467395 415740020551437011622701093)
    ·
      refine ⟨77951253853394439679256455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415740020551437011622701093 77951253853394439679256455)
      ·
        refine ⟨116926880780091659518884683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77951253853394439679256455 116926880780091659518884683)
        ·
          refine ⟨175390321170137489278327025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116926880780091659518884683 175390321170137489278327025)
          ·
            refine ⟨131542740877603116958745269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175390321170137489278327025 131542740877603116958745269)
            ·
              refine ⟨12332131957275292214882369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131542740877603116958745269 12332131957275292214882369)
              ·
                refine ⟨9249098967956469161161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12332131957275292214882369 9249098967956469161161777)
                ·
                  refine ⟨6936824225967351870871333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249098967956469161161777 6936824225967351870871333)
                  ·
                    refine ⟨1300654542368878475788375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6936824225967351870871333 1300654542368878475788375)
                    ·
                      rfl

theorem cell23_7599047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_7599047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599047 prefixEnd_7599047 := by exact prefixLift 7599047
  have htrace : WordTrace (prefixWord ++ tailWord_7599047) baseStart_7599047 baseEnd_7599047 := by
    simpa [prefixWord, tailWord_7599047, baseEnd_7599047] using wordTrace_append hprefix tailTrace_7599047
  have hstable : (prefixWord ++ tailWord_7599047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599047).length < 2 ^ (prefixWord ++ tailWord_7599047).sum := by decide
  have hdescent : baseEnd_7599047 < baseStart_7599047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599054 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_7599054 : Nat := 118140960795 + 7599054 * 2 ^ 59
def prefixEnd_7599054 : Nat := 4983230072969 + 3 ^ 40 * 7599054 * 2
def baseEnd_7599054 : Nat := 3901967221471216899977593

theorem tailTrace_7599054 : CollatzResearch.WordTrace tailWord_7599054 prefixEnd_7599054 3901967221471216899977593 := by
  unfold tailWord_7599054
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645033626491580992996527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184773512674621765295981477 34645033626491580992996527)
  ·
    refine ⟨51967550439737371489494791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34645033626491580992996527 51967550439737371489494791)
    ·
      refine ⟨77951325659606057234242187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51967550439737371489494791 77951325659606057234242187)
      ·
        refine ⟨116926988489409085851363281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77951325659606057234242187 116926988489409085851363281)
        ·
          refine ⟨87695241367056814388522461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116926988489409085851363281 87695241367056814388522461)
          ·
            refine ⟨32885715512646305395695923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87695241367056814388522461 32885715512646305395695923)
            ·
              refine ⟨49328573268969458093543885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32885715512646305395695923 49328573268969458093543885)
              ·
                refine ⟨18498214975863546785078957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49328573268969458093543885 18498214975863546785078957)
                ·
                  refine ⟨6936830615948830044404609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18498214975863546785078957 6936830615948830044404609)
                  ·
                    refine ⟨5202622961961622533303457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6936830615948830044404609 5202622961961622533303457)
                    ·
                      refine ⟨3901967221471216899977593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202622961961622533303457 3901967221471216899977593)
                      ·
                        rfl

theorem cell23_7599054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_7599054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599054 prefixEnd_7599054 := by exact prefixLift 7599054
  have htrace : WordTrace (prefixWord ++ tailWord_7599054) baseStart_7599054 baseEnd_7599054 := by
    simpa [prefixWord, tailWord_7599054, baseEnd_7599054] using wordTrace_append hprefix tailTrace_7599054
  have hstable : (prefixWord ++ tailWord_7599054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599054).length < 2 ^ (prefixWord ++ tailWord_7599054).sum := by decide
  have hdescent : baseEnd_7599054 < baseStart_7599054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599063 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_7599063 : Nat := 118140960795 + 7599063 * 2 ^ 59
def prefixEnd_7599063 : Nat := 4983230072969 + 3 ^ 40 * 7599063 * 2
def baseEnd_7599063 : Nat := 3901971842797107364765051

theorem tailTrace_7599063 : CollatzResearch.WordTrace tailWord_7599063 prefixEnd_7599063 3901971842797107364765051 := by
  unfold tailWord_7599063
  simp only [CollatzResearch.WordTrace]
  refine ⟨277160597268900042481049843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184773731512600028320699895 277160597268900042481049843)
  ·
    refine ⟨415740895903350063721574765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277160597268900042481049843 415740895903350063721574765)
    ·
      refine ⟨155902835963756273895590537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415740895903350063721574765 155902835963756273895590537)
      ·
        refine ⟨116927126972817205421692903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155902835963756273895590537 116927126972817205421692903)
        ·
          refine ⟨175390690459225808132539355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116927126972817205421692903 175390690459225808132539355)
          ·
            refine ⟨263086035688838712198809033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175390690459225808132539355 263086035688838712198809033)
            ·
              refine ⟨197314526766629034149106775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263086035688838712198809033 197314526766629034149106775)
              ·
                refine ⟨295971790149943551223660163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197314526766629034149106775 295971790149943551223660163)
                ·
                  refine ⟨443957685224915326835490245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295971790149943551223660163 443957685224915326835490245)
                  ·
                    refine ⟨83242065979671623781654421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443957685224915326835490245 83242065979671623781654421)
                    ·
                      refine ⟨3901971842797107364765051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83242065979671623781654421 3901971842797107364765051)
                      ·
                        rfl

theorem cell23_7599063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_7599063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599063 prefixEnd_7599063 := by exact prefixLift 7599063
  have htrace : WordTrace (prefixWord ++ tailWord_7599063) baseStart_7599063 baseEnd_7599063 := by
    simpa [prefixWord, tailWord_7599063, baseEnd_7599063] using wordTrace_append hprefix tailTrace_7599063
  have hstable : (prefixWord ++ tailWord_7599063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599063).length < 2 ^ (prefixWord ++ tailWord_7599063).sum := by decide
  have hdescent : baseEnd_7599063 < baseStart_7599063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599064 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 2, 4]
def baseStart_7599064 : Nat := 118140960795 + 7599064 * 2 ^ 59
def prefixEnd_7599064 : Nat := 4983230072969 + 3 ^ 40 * 7599064 * 2
def baseEnd_7599064 : Nat := 1300657452092587286950849

theorem tailTrace_7599064 : CollatzResearch.WordTrace tailWord_7599064 prefixEnd_7599064 1300657452092587286950849 := by
  unfold tailWord_7599064
  simp only [CollatzResearch.WordTrace]
  refine ⟨138580316870948209825918123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184773755827930946434557497 138580316870948209825918123)
  ·
    refine ⟨207870475306422314738877185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138580316870948209825918123 207870475306422314738877185)
    ·
      refine ⟨155902856479816736054157889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207870475306422314738877185 155902856479816736054157889)
      ·
        refine ⟨116927142359862552040618417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155902856479816736054157889 116927142359862552040618417)
        ·
          refine ⟨87695356769896914030463813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116927142359862552040618417 87695356769896914030463813)
          ·
            refine ⟨16442879394355671380711965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87695356769896914030463813 16442879394355671380711965)
            ·
              refine ⟨6166079772883376767766987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16442879394355671380711965 6166079772883376767766987)
              ·
                refine ⟨9249119659325065151650481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166079772883376767766987 9249119659325065151650481)
                ·
                  refine ⟨6936839744493798863737861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249119659325065151650481 6936839744493798863737861)
                  ·
                    refine ⟨1300657452092587286950849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6936839744493798863737861 1300657452092587286950849)
                    ·
                      rfl

theorem cell23_7599064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_7599064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599064 prefixEnd_7599064 := by exact prefixLift 7599064
  have htrace : WordTrace (prefixWord ++ tailWord_7599064) baseStart_7599064 baseEnd_7599064 := by
    simpa [prefixWord, tailWord_7599064, baseEnd_7599064] using wordTrace_append hprefix tailTrace_7599064
  have hstable : (prefixWord ++ tailWord_7599064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599064).length < 2 ^ (prefixWord ++ tailWord_7599064).sum := by decide
  have hdescent : baseEnd_7599064 < baseStart_7599064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599077 : List Nat := [1, 3, 1, 6, 1, 1, 1, 9]
def baseStart_7599077 : Nat := 118140960795 + 7599077 * 2 ^ 59
def prefixEnd_7599077 : Nat := 4983230072969 + 3 ^ 40 * 7599077 * 2
def baseEnd_7599077 : Nat := 144517741908380381851481

theorem tailTrace_7599077 : CollatzResearch.WordTrace tailWord_7599077 prefixEnd_7599077 144517741908380381851481 := by
  unfold tailWord_7599077
  simp only [CollatzResearch.WordTrace]
  refine ⟨277161107890849322872059485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184774071927232881914706323 277161107890849322872059485)
  ·
    refine ⟨103935415459068496077022307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277161107890849322872059485 103935415459068496077022307)
    ·
      refine ⟨155903123188602744115533461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103935415459068496077022307 155903123188602744115533461)
      ·
        refine ⟨7307958899465753630415631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155903123188602744115533461 7307958899465753630415631)
        ·
          refine ⟨10961938349198630445623447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307958899465753630415631 10961938349198630445623447)
          ·
            refine ⟨16442907523797945668435171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961938349198630445623447 16442907523797945668435171)
            ·
              refine ⟨24664361285696918502652757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442907523797945668435171 24664361285696918502652757)
              ·
                refine ⟨144517741908380381851481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24664361285696918502652757 144517741908380381851481)
                ·
                  rfl

theorem cell23_7599077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 9].length) (baseStart_7599077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599077 prefixEnd_7599077 := by exact prefixLift 7599077
  have htrace : WordTrace (prefixWord ++ tailWord_7599077) baseStart_7599077 baseEnd_7599077 := by
    simpa [prefixWord, tailWord_7599077, baseEnd_7599077] using wordTrace_append hprefix tailTrace_7599077
  have hstable : (prefixWord ++ tailWord_7599077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599077).length < 2 ^ (prefixWord ++ tailWord_7599077).sum := by decide
  have hdescent : baseEnd_7599077 < baseStart_7599077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599087 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 3]
def baseStart_7599087 : Nat := 118140960795 + 7599087 * 2 ^ 59
def prefixEnd_7599087 : Nat := 4983230072969 + 3 ^ 40 * 7599087 * 2
def baseEnd_7599087 : Nat := 3901984166332815270864941

theorem tailTrace_7599087 : CollatzResearch.WordTrace tailWord_7599087 prefixEnd_7599087 3901984166332815270864941 := by
  unfold tailWord_7599087
  simp only [CollatzResearch.WordTrace]
  refine ⟨277161472620813094579923515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184774315080542063053282343 277161472620813094579923515)
  ·
    refine ⟨415742208931219641869885273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277161472620813094579923515 415742208931219641869885273)
    ·
      refine ⟨311806656698414731402413955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415742208931219641869885273 311806656698414731402413955)
      ·
        refine ⟨467709985047622097103620933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311806656698414731402413955 467709985047622097103620933)
        ·
          refine ⟨87695622196429143206928925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467709985047622097103620933 87695622196429143206928925)
          ·
            refine ⟨32885858323660928702598347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87695622196429143206928925 32885858323660928702598347)
            ·
              refine ⟨49328787485491393053897521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32885858323660928702598347 49328787485491393053897521)
              ·
                refine ⟨36996590614118544790423141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49328787485491393053897521 36996590614118544790423141)
                ·
                  refine ⟨6936860740147227148204339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36996590614118544790423141 6936860740147227148204339)
                  ·
                    refine ⟨10405291110220840722306509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6936860740147227148204339 10405291110220840722306509)
                    ·
                      refine ⟨3901984166332815270864941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10405291110220840722306509 3901984166332815270864941)
                      ·
                        rfl

theorem cell23_7599087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_7599087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599087 prefixEnd_7599087 := by exact prefixLift 7599087
  have htrace : WordTrace (prefixWord ++ tailWord_7599087) baseStart_7599087 baseEnd_7599087 := by
    simpa [prefixWord, tailWord_7599087, baseEnd_7599087] using wordTrace_append hprefix tailTrace_7599087
  have hstable : (prefixWord ++ tailWord_7599087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599087).length < 2 ^ (prefixWord ++ tailWord_7599087).sum := by decide
  have hdescent : baseEnd_7599087 < baseStart_7599087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599130 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_7599130 : Nat := 118140960795 + 7599130 * 2 ^ 59
def prefixEnd_7599130 : Nat := 4983230072969 + 3 ^ 40 * 7599130 * 2
def baseEnd_7599130 : Nat := 3902006246000958602627243

theorem tailTrace_7599130 : CollatzResearch.WordTrace tailWord_7599130 prefixEnd_7599130 3902006246000958602627243 := by
  unfold tailWord_7599130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69290760239914328230934711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184775360639771541949159229 69290760239914328230934711)
  ·
    refine ⟨103936140359871492346402067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69290760239914328230934711 103936140359871492346402067)
    ·
      refine ⟨155904210539807238519603101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103936140359871492346402067 155904210539807238519603101)
      ·
        refine ⟨58464078952427714444851163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155904210539807238519603101 58464078952427714444851163)
        ·
          refine ⟨87696118428641571667276745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58464078952427714444851163 87696118428641571667276745)
          ·
            refine ⟨65772088821481178750457559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87696118428641571667276745 65772088821481178750457559)
            ·
              refine ⟨98658133232221768125686339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65772088821481178750457559 98658133232221768125686339)
              ·
                refine ⟨147987199848332652188529509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98658133232221768125686339 147987199848332652188529509)
                ·
                  refine ⟨27747599971562372285349283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147987199848332652188529509 27747599971562372285349283)
                  ·
                    refine ⟨41621399957343558428023925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27747599971562372285349283 41621399957343558428023925)
                    ·
                      refine ⟨3902006246000958602627243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41621399957343558428023925 3902006246000958602627243)
                      ·
                        rfl

theorem cell23_7599130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_7599130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599130 prefixEnd_7599130 := by exact prefixLift 7599130
  have htrace : WordTrace (prefixWord ++ tailWord_7599130) baseStart_7599130 baseEnd_7599130 := by
    simpa [prefixWord, tailWord_7599130, baseEnd_7599130] using wordTrace_append hprefix tailTrace_7599130
  have hstable : (prefixWord ++ tailWord_7599130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599130).length < 2 ^ (prefixWord ++ tailWord_7599130).sum := by decide
  have hdescent : baseEnd_7599130 < baseStart_7599130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599161 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7599161 : Nat := 118140960795 + 7599161 * 2 ^ 59
def prefixEnd_7599161 : Nat := 4983230072969 + 3 ^ 40 * 7599161 * 2
def baseEnd_7599161 : Nat := 3902022163901247981339601

theorem tailTrace_7599161 : CollatzResearch.WordTrace tailWord_7599161 prefixEnd_7599161 3902022163901247981339601 := by
  unfold tailWord_7599161
  simp only [CollatzResearch.WordTrace]
  refine ⟨277164171622545005218117337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184776114415030003478744891 277164171622545005218117337)
  ·
    refine ⟨207873128716908753913588003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277164171622545005218117337 207873128716908753913588003)
    ·
      refine ⟨311809693075363130870382005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207873128716908753913588003 311809693075363130870382005)
      ·
        refine ⟨29232158725815293519098313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311809693075363130870382005 29232158725815293519098313)
        ·
          refine ⟨21924119044361470139323735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29232158725815293519098313 21924119044361470139323735)
          ·
            refine ⟨32886178566542205208985603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21924119044361470139323735 32886178566542205208985603)
            ·
              refine ⟨49329267849813307813478405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32886178566542205208985603 49329267849813307813478405)
              ·
                refine ⟨9249237721839995215027201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49329267849813307813478405 9249237721839995215027201)
                ·
                  refine ⟨6936928291379996411270401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249237721839995215027201 6936928291379996411270401)
                  ·
                    refine ⟨5202696218534997308452801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6936928291379996411270401 5202696218534997308452801)
                    ·
                      refine ⟨3902022163901247981339601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202696218534997308452801 3902022163901247981339601)
                      ·
                        rfl

theorem cell23_7599161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7599161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599161 prefixEnd_7599161 := by exact prefixLift 7599161
  have htrace : WordTrace (prefixWord ++ tailWord_7599161) baseStart_7599161 baseEnd_7599161 := by
    simpa [prefixWord, tailWord_7599161, baseEnd_7599161] using wordTrace_append hprefix tailTrace_7599161
  have hstable : (prefixWord ++ tailWord_7599161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599161).length < 2 ^ (prefixWord ++ tailWord_7599161).sum := by decide
  have hdescent : baseEnd_7599161 < baseStart_7599161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599174 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7599174 : Nat := 118140960795 + 7599174 * 2 ^ 59
def prefixEnd_7599174 : Nat := 4983230072969 + 3 ^ 40 * 7599174 * 2
def baseEnd_7599174 : Nat := 3902028839149756430477041

theorem tailTrace_7599174 : CollatzResearch.WordTrace tailWord_7599174 prefixEnd_7599174 3902028839149756430477041 := by
  unfold tailWord_7599174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8661395180359309638698143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184776430514331938958893717 8661395180359309638698143)
  ·
    refine ⟨12992092770538964458047215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8661395180359309638698143 12992092770538964458047215)
    ·
      refine ⟨19488139155808446687070823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992092770538964458047215 19488139155808446687070823)
      ·
        refine ⟨29232208733712670030606235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488139155808446687070823 29232208733712670030606235)
        ·
          refine ⟨43848313100569005045909353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29232208733712670030606235 43848313100569005045909353)
          ·
            refine ⟨32886234825426753784432015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43848313100569005045909353 32886234825426753784432015)
            ·
              refine ⟨49329352238140130676648023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32886234825426753784432015 49329352238140130676648023)
              ·
                refine ⟨73994028357210196014972035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49329352238140130676648023 73994028357210196014972035)
                ·
                  refine ⟨110991042535815294022458053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73994028357210196014972035 110991042535815294022458053)
                  ·
                    refine ⟨20810820475465367629210885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110991042535815294022458053 20810820475465367629210885)
                    ·
                      refine ⟨3902028839149756430477041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20810820475465367629210885 3902028839149756430477041)
                      ·
                        rfl

theorem cell23_7599174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7599174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599174 prefixEnd_7599174 := by exact prefixLift 7599174
  have htrace : WordTrace (prefixWord ++ tailWord_7599174) baseStart_7599174 baseEnd_7599174 := by
    simpa [prefixWord, tailWord_7599174, baseEnd_7599174] using wordTrace_append hprefix tailTrace_7599174
  have hstable : (prefixWord ++ tailWord_7599174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599174).length < 2 ^ (prefixWord ++ tailWord_7599174).sum := by decide
  have hdescent : baseEnd_7599174 < baseStart_7599174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599180 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_7599180 : Nat := 118140960795 + 7599180 * 2 ^ 59
def prefixEnd_7599180 : Nat := 4983230072969 + 3 ^ 40 * 7599180 * 2
def baseEnd_7599180 : Nat := 1300677306677894469000671

theorem tailTrace_7599180 : CollatzResearch.WordTrace tailWord_7599180 prefixEnd_7599180 1300677306677894469000671 := by
  unfold tailWord_7599180
  simp only [CollatzResearch.WordTrace]
  refine ⟨138582432304738085731529497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184776576406317447642039329 138582432304738085731529497)
  ·
    refine ⟨103936824228553564298647123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138582432304738085731529497 103936824228553564298647123)
    ·
      refine ⟨155905236342830346447970685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103936824228553564298647123 155905236342830346447970685)
      ·
        refine ⟨58464463628561379917989007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155905236342830346447970685 58464463628561379917989007)
        ·
          refine ⟨87696695442842069876983511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58464463628561379917989007 87696695442842069876983511)
          ·
            refine ⟨131545043164263104815475267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87696695442842069876983511 131545043164263104815475267)
            ·
              refine ⟨197317564746394657223212901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131545043164263104815475267 197317564746394657223212901)
              ·
                refine ⟨36997043389948998229352419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197317564746394657223212901 36997043389948998229352419)
                ·
                  refine ⟨55495565084923497344028629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36997043389948998229352419 55495565084923497344028629)
                  ·
                    refine ⟨1300677306677894469000671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55495565084923497344028629 1300677306677894469000671)
                    ·
                      rfl

theorem cell23_7599180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_7599180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599180 prefixEnd_7599180 := by exact prefixLift 7599180
  have htrace : WordTrace (prefixWord ++ tailWord_7599180) baseStart_7599180 baseEnd_7599180 := by
    simpa [prefixWord, tailWord_7599180, baseEnd_7599180] using wordTrace_append hprefix tailTrace_7599180
  have hstable : (prefixWord ++ tailWord_7599180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599180).length < 2 ^ (prefixWord ++ tailWord_7599180).sum := by decide
  have hdescent : baseEnd_7599180 < baseStart_7599180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599271 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7599271 : Nat := 118140960795 + 7599271 * 2 ^ 59
def prefixEnd_7599271 : Nat := 4983230072969 + 3 ^ 40 * 7599271 * 2
def baseEnd_7599271 : Nat := 3902078646773242550964095

theorem tailTrace_7599271 : CollatzResearch.WordTrace tailWord_7599271 prefixEnd_7599271 3902078646773242550964095 := by
  unfold tailWord_7599271
  simp only [CollatzResearch.WordTrace]
  refine ⟨277168183652146494004621667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184778789101430996003081111 277168183652146494004621667)
  ·
    refine ⟨415752275478219741006932501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277168183652146494004621667 415752275478219741006932501)
    ·
      refine ⟨19488387913041550359699961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 415752275478219741006932501 19488387913041550359699961)
      ·
        refine ⟨14616290934781162769774971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19488387913041550359699961 14616290934781162769774971)
        ·
          refine ⟨21924436402171744154662457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14616290934781162769774971 21924436402171744154662457)
          ·
            refine ⟨16443327301628808115996843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21924436402171744154662457 16443327301628808115996843)
            ·
              refine ⟨24664990952443212173995265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16443327301628808115996843 24664990952443212173995265)
              ·
                refine ⟨18498743214332409130496449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24664990952443212173995265 18498743214332409130496449)
                ·
                  refine ⟨13874057410749306847872337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18498743214332409130496449 13874057410749306847872337)
                  ·
                    refine ⟨10405543058061980135904253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13874057410749306847872337 10405543058061980135904253)
                    ·
                      refine ⟨3902078646773242550964095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10405543058061980135904253 3902078646773242550964095)
                      ·
                        rfl

theorem cell23_7599271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7599271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599271 prefixEnd_7599271 := by exact prefixLift 7599271
  have htrace : WordTrace (prefixWord ++ tailWord_7599271) baseStart_7599271 baseEnd_7599271 := by
    simpa [prefixWord, tailWord_7599271, baseEnd_7599271] using wordTrace_append hprefix tailTrace_7599271
  have hstable : (prefixWord ++ tailWord_7599271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599271).length < 2 ^ (prefixWord ++ tailWord_7599271).sum := by decide
  have hdescent : baseEnd_7599271 < baseStart_7599271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599274 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_7599274 : Nat := 118140960795 + 7599274 * 2 ^ 59
def prefixEnd_7599274 : Nat := 4983230072969 + 3 ^ 40 * 7599274 * 2
def baseEnd_7599274 : Nat := 433564465246134004358509

theorem tailTrace_7599274 : CollatzResearch.WordTrace tailWord_7599274 prefixEnd_7599274 433564465246134004358509 := by
  unfold tailWord_7599274
  simp only [CollatzResearch.WordTrace]
  refine ⟨69292073267783906379245219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184778862047423750344653917 69292073267783906379245219)
  ·
    refine ⟨103938109901675859568867829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69292073267783906379245219 103938109901675859568867829)
    ·
      refine ⟨9744197803282111834581359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103938109901675859568867829 9744197803282111834581359)
      ·
        refine ⟨14616296704923167751872039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9744197803282111834581359 14616296704923167751872039)
        ·
          refine ⟨21924445057384751627808059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14616296704923167751872039 21924445057384751627808059)
          ·
            refine ⟨32886667586077127441712089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21924445057384751627808059 32886667586077127441712089)
            ·
              refine ⟨24665000689557845581284067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32886667586077127441712089 24665000689557845581284067)
              ·
                refine ⟨36997501034336768371926101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24665000689557845581284067 36997501034336768371926101)
                ·
                  refine ⟨433564465246134004358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36997501034336768371926101 433564465246134004358509)
                  ·
                    rfl

theorem cell23_7599274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_7599274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599274 prefixEnd_7599274 := by exact prefixLift 7599274
  have htrace : WordTrace (prefixWord ++ tailWord_7599274) baseStart_7599274 baseEnd_7599274 := by
    simpa [prefixWord, tailWord_7599274, baseEnd_7599274] using wordTrace_append hprefix tailTrace_7599274
  have hstable : (prefixWord ++ tailWord_7599274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599274).length < 2 ^ (prefixWord ++ tailWord_7599274).sum := by decide
  have hdescent : baseEnd_7599274 < baseStart_7599274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599287 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 3, 5]
def baseStart_7599287 : Nat := 118140960795 + 7599287 * 2 ^ 59
def prefixEnd_7599287 : Nat := 4983230072969 + 3 ^ 40 * 7599287 * 2
def baseEnd_7599287 : Nat := 1300695620821238162788007

theorem tailTrace_7599287 : CollatzResearch.WordTrace tailWord_7599287 prefixEnd_7599287 1300695620821238162788007 := by
  unfold tailWord_7599287
  simp only [CollatzResearch.WordTrace]
  refine ⟨277168767220088528737204115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184779178146725685824802743 277168767220088528737204115)
  ·
    refine ⟨415753150830132793105806173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277168767220088528737204115 415753150830132793105806173)
    ·
      refine ⟨155907431561299797414677315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415753150830132793105806173 155907431561299797414677315)
      ·
        refine ⟨233861147341949696122015973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155907431561299797414677315 233861147341949696122015973)
        ·
          refine ⟨43848965126615568022877995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233861147341949696122015973 43848965126615568022877995)
          ·
            refine ⟨65773447689923352034316993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43848965126615568022877995 65773447689923352034316993)
            ·
              refine ⟨49330085767442514025737745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65773447689923352034316993 49330085767442514025737745)
              ·
                refine ⟨36997564325581885519303309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49330085767442514025737745 36997564325581885519303309)
                ·
                  refine ⟨13874086622093207069738741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36997564325581885519303309 13874086622093207069738741)
                  ·
                    refine ⟨1300695620821238162788007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13874086622093207069738741 1300695620821238162788007)
                    ·
                      rfl

theorem cell23_7599287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_7599287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599287 prefixEnd_7599287 := by exact prefixLift 7599287
  have htrace : WordTrace (prefixWord ++ tailWord_7599287) baseStart_7599287 baseEnd_7599287 := by
    simpa [prefixWord, tailWord_7599287, baseEnd_7599287] using wordTrace_append hprefix tailTrace_7599287
  have hstable : (prefixWord ++ tailWord_7599287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599287).length < 2 ^ (prefixWord ++ tailWord_7599287).sum := by decide
  have hdescent : baseEnd_7599287 < baseStart_7599287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599304 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_7599304 : Nat := 118140960795 + 7599304 * 2 ^ 59
def prefixEnd_7599304 : Nat := 4983230072969 + 3 ^ 40 * 7599304 * 2
def baseEnd_7599304 : Nat := 1300698530544946973950481

theorem tailTrace_7599304 : CollatzResearch.WordTrace tailWord_7599304 prefixEnd_7599304 1300698530544946973950481 := by
  unfold tailWord_7599304
  simp only [CollatzResearch.WordTrace]
  refine ⟨138584693630513470320286483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184779591507351293760381977 138584693630513470320286483)
  ·
    refine ⟨207877040445770205480429725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138584693630513470320286483 207877040445770205480429725)
    ·
      refine ⟨77953890167163827055161147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207877040445770205480429725 77953890167163827055161147)
      ·
        refine ⟨116930835250745740582741721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77953890167163827055161147 116930835250745740582741721)
        ·
          refine ⟨87698126438059305437056291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116930835250745740582741721 87698126438059305437056291)
          ·
            refine ⟨131547189657088958155584437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87698126438059305437056291 131547189657088958155584437)
            ·
              refine ⟨12332549030352089827086041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131547189657088958155584437 12332549030352089827086041)
              ·
                refine ⟨9249411772764067370314531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12332549030352089827086041 9249411772764067370314531)
                ·
                  refine ⟨13874117659146101055471797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249411772764067370314531 13874117659146101055471797)
                  ·
                    refine ⟨1300698530544946973950481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13874117659146101055471797 1300698530544946973950481)
                    ·
                      rfl

theorem cell23_7599304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_7599304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599304 prefixEnd_7599304 := by exact prefixLift 7599304
  have htrace : WordTrace (prefixWord ++ tailWord_7599304) baseStart_7599304 baseEnd_7599304 := by
    simpa [prefixWord, tailWord_7599304, baseEnd_7599304] using wordTrace_append hprefix tailTrace_7599304
  have hstable : (prefixWord ++ tailWord_7599304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599304).length < 2 ^ (prefixWord ++ tailWord_7599304).sum := by decide
  have hdescent : baseEnd_7599304 < baseStart_7599304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599335 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7599335 : Nat := 118140960795 + 7599335 * 2 ^ 59
def prefixEnd_7599335 : Nat := 4983230072969 + 3 ^ 40 * 7599335 * 2
def baseEnd_7599335 : Nat := 3902111509535130300563801

theorem tailTrace_7599335 : CollatzResearch.WordTrace tailWord_7599335 prefixEnd_7599335 3902111509535130300563801 := by
  unfold tailWord_7599335
  simp only [CollatzResearch.WordTrace]
  refine ⟨277170517923914632934951459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184780345282609755289967639 277170517923914632934951459)
  ·
    refine ⟨415755776885871949402427189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277170517923914632934951459 415755776885871949402427189)
    ·
      refine ⟨38977104083050495256477549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 415755776885871949402427189 38977104083050495256477549)
      ·
        refine ⟨14616414031143935721179081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38977104083050495256477549 14616414031143935721179081)
        ·
          refine ⟨10962310523357951790884311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14616414031143935721179081 10962310523357951790884311)
          ·
            refine ⟨16443465785036927686326467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10962310523357951790884311 16443465785036927686326467)
            ·
              refine ⟨24665198677555391529489701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16443465785036927686326467 24665198677555391529489701)
              ·
                refine ⟨4624724752041635911779319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24665198677555391529489701 4624724752041635911779319)
                ·
                  refine ⟨6937087128062453867668979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624724752041635911779319 6937087128062453867668979)
                  ·
                    refine ⟨10405630692093680801503469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937087128062453867668979 10405630692093680801503469)
                    ·
                      refine ⟨3902111509535130300563801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10405630692093680801503469 3902111509535130300563801)
                      ·
                        rfl

theorem cell23_7599335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7599335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599335 prefixEnd_7599335 := by exact prefixLift 7599335
  have htrace : WordTrace (prefixWord ++ tailWord_7599335) baseStart_7599335 baseEnd_7599335 := by
    simpa [prefixWord, tailWord_7599335, baseEnd_7599335] using wordTrace_append hprefix tailTrace_7599335
  have hstable : (prefixWord ++ tailWord_7599335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599335).length < 2 ^ (prefixWord ++ tailWord_7599335).sum := by decide
  have hdescent : baseEnd_7599335 < baseStart_7599335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599347 : List Nat := [1, 1, 1, 2, 2, 5, 3, 8]
def baseStart_7599347 : Nat := 118140960795 + 7599347 * 2 ^ 59
def prefixEnd_7599347 : Nat := 4983230072969 + 3 ^ 40 * 7599347 * 2
def baseEnd_7599347 : Nat := 144522876714925342726435

theorem tailTrace_7599347 : CollatzResearch.WordTrace tailWord_7599347 prefixEnd_7599347 144522876714925342726435 := by
  unfold tailWord_7599347
  simp only [CollatzResearch.WordTrace]
  refine ⟨277170955599871158984388295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184780637066580772656258863 277170955599871158984388295)
  ·
    refine ⟨415756433399806738476582443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277170955599871158984388295 415756433399806738476582443)
    ·
      refine ⟨623634650099710107714873665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415756433399806738476582443 623634650099710107714873665)
      ·
        refine ⟨467725987574782580786155249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623634650099710107714873665 467725987574782580786155249)
        ·
          refine ⟨350794490681086935589616437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467725987574782580786155249 350794490681086935589616437)
          ·
            refine ⟨32886983501351900211526541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350794490681086935589616437 32886983501351900211526541)
            ·
              refine ⟨12332618813006962579322453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32886983501351900211526541 12332618813006962579322453)
              ·
                refine ⟨144522876714925342726435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12332618813006962579322453 144522876714925342726435)
                ·
                  rfl

theorem cell23_7599347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 8].length) (baseStart_7599347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599347 prefixEnd_7599347 := by exact prefixLift 7599347
  have htrace : WordTrace (prefixWord ++ tailWord_7599347) baseStart_7599347 baseEnd_7599347 := by
    simpa [prefixWord, tailWord_7599347, baseEnd_7599347] using wordTrace_append hprefix tailTrace_7599347
  have hstable : (prefixWord ++ tailWord_7599347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599347).length < 2 ^ (prefixWord ++ tailWord_7599347).sum := by decide
  have hdescent : baseEnd_7599347 < baseStart_7599347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599354 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_7599354 : Nat := 118140960795 + 7599354 * 2 ^ 59
def prefixEnd_7599354 : Nat := 4983230072969 + 3 ^ 40 * 7599354 * 2
def baseEnd_7599354 : Nat := 3902121265667565726226213

theorem tailTrace_7599354 : CollatzResearch.WordTrace tailWord_7599354 prefixEnd_7599354 3902121265667565726226213 := by
  unfold tailWord_7599354
  simp only [CollatzResearch.WordTrace]
  refine ⟨69292802727711449794973279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184780807273897199453262077 69292802727711449794973279)
  ·
    refine ⟨103939204091567174692459919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69292802727711449794973279 103939204091567174692459919)
    ·
      refine ⟨155908806137350762038689879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103939204091567174692459919 155908806137350762038689879)
      ·
        refine ⟨233863209206026143058034819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155908806137350762038689879 233863209206026143058034819)
        ·
          refine ⟨350794813809039214587052229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233863209206026143058034819 350794813809039214587052229)
          ·
            refine ⟨65774027589194852735072293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350794813809039214587052229 65774027589194852735072293)
            ·
              refine ⟨12332630172974034887826055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65774027589194852735072293 12332630172974034887826055)
              ·
                refine ⟨18498945259461052331739083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12332630172974034887826055 18498945259461052331739083)
                ·
                  refine ⟨27748417889191578497608625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18498945259461052331739083 27748417889191578497608625)
                  ·
                    refine ⟨20811313416893683873206469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27748417889191578497608625 20811313416893683873206469)
                    ·
                      refine ⟨3902121265667565726226213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20811313416893683873206469 3902121265667565726226213)
                      ·
                        rfl

theorem cell23_7599354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_7599354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599354 prefixEnd_7599354 := by exact prefixLift 7599354
  have htrace : WordTrace (prefixWord ++ tailWord_7599354) baseStart_7599354 baseEnd_7599354 := by
    simpa [prefixWord, tailWord_7599354, baseEnd_7599354] using wordTrace_append hprefix tailTrace_7599354
  have hstable : (prefixWord ++ tailWord_7599354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599354).length < 2 ^ (prefixWord ++ tailWord_7599354).sum := by decide
  have hdescent : baseEnd_7599354 < baseStart_7599354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599358 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7599358 : Nat := 118140960795 + 7599358 * 2 ^ 59
def prefixEnd_7599358 : Nat := 4983230072969 + 3 ^ 40 * 7599358 * 2
def baseEnd_7599358 : Nat := 3902123319590183710576195

theorem tailTrace_7599358 : CollatzResearch.WordTrace tailWord_7599358 prefixEnd_7599358 3902123319590183710576195 := by
  unfold tailWord_7599358
  simp only [CollatzResearch.WordTrace]
  refine ⟨34646419600353913482879841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184780904535220871908692485 34646419600353913482879841)
  ·
    refine ⟨25984814700265435112159881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34646419600353913482879841 25984814700265435112159881)
    ·
      refine ⟨19488611025199076334119911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25984814700265435112159881 19488611025199076334119911)
      ·
        refine ⟨29232916537798614501179867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488611025199076334119911 29232916537798614501179867)
        ·
          refine ⟨43849374806697921751769801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29232916537798614501179867 43849374806697921751769801)
          ·
            refine ⟨32887031105023441313827351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43849374806697921751769801 32887031105023441313827351)
            ·
              refine ⟨49330546657535161970741027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32887031105023441313827351 49330546657535161970741027)
              ·
                refine ⟨73995819986302742956111541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49330546657535161970741027 73995819986302742956111541)
                ·
                  refine ⟨6937108123715882152135457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73995819986302742956111541 6937108123715882152135457)
                  ·
                    refine ⟨5202831092786911614101593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937108123715882152135457 5202831092786911614101593)
                    ·
                      refine ⟨3902123319590183710576195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202831092786911614101593 3902123319590183710576195)
                      ·
                        rfl

theorem cell23_7599358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7599358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599358 prefixEnd_7599358 := by exact prefixLift 7599358
  have htrace : WordTrace (prefixWord ++ tailWord_7599358) baseStart_7599358 baseEnd_7599358 := by
    simpa [prefixWord, tailWord_7599358, baseEnd_7599358] using wordTrace_append hprefix tailTrace_7599358
  have hstable : (prefixWord ++ tailWord_7599358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599358).length < 2 ^ (prefixWord ++ tailWord_7599358).sum := by decide
  have hdescent : baseEnd_7599358 < baseStart_7599358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599362 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_7599362 : Nat := 118140960795 + 7599362 * 2 ^ 59
def prefixEnd_7599362 : Nat := 4983230072969 + 3 ^ 40 * 7599362 * 2
def baseEnd_7599362 : Nat := 3902125373512801694926177

theorem tailTrace_7599362 : CollatzResearch.WordTrace tailWord_7599362 prefixEnd_7599362 3902125373512801694926177 := by
  unfold tailWord_7599362
  simp only [CollatzResearch.WordTrace]
  refine ⟨69292875673704204136546085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184781001796544544364122893 69292875673704204136546085)
  ·
    refine ⟨12992414188819538275602391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69292875673704204136546085 12992414188819538275602391)
    ·
      refine ⟨19488621283229307413403587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992414188819538275602391 19488621283229307413403587)
      ·
        refine ⟨29232931924843961120105381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488621283229307413403587 29232931924843961120105381)
        ·
          refine ⟨5481174735908242710019759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29232931924843961120105381 5481174735908242710019759)
          ·
            refine ⟨8221762103862364065029639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481174735908242710019759 8221762103862364065029639)
            ·
              refine ⟨12332643155793546097544459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221762103862364065029639 12332643155793546097544459)
              ·
                refine ⟨18498964733690319146316689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12332643155793546097544459 18498964733690319146316689)
                ·
                  refine ⟨13874223550267739359737517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18498964733690319146316689 13874223550267739359737517)
                  ·
                    refine ⟨5202833831350402259901569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13874223550267739359737517 5202833831350402259901569)
                    ·
                      refine ⟨3902125373512801694926177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202833831350402259901569 3902125373512801694926177)
                      ·
                        rfl

theorem cell23_7599362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_7599362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599362 prefixEnd_7599362 := by exact prefixLift 7599362
  have htrace : WordTrace (prefixWord ++ tailWord_7599362) baseStart_7599362 baseEnd_7599362 := by
    simpa [prefixWord, tailWord_7599362, baseEnd_7599362] using wordTrace_append hprefix tailTrace_7599362
  have hstable : (prefixWord ++ tailWord_7599362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599362).length < 2 ^ (prefixWord ++ tailWord_7599362).sum := by decide
  have hdescent : baseEnd_7599362 < baseStart_7599362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599408 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3]
def baseStart_7599408 : Nat := 118140960795 + 7599408 * 2 ^ 59
def prefixEnd_7599408 : Nat := 4983230072969 + 3 ^ 40 * 7599408 * 2
def baseEnd_7599408 : Nat := 3902148993622908514950965

theorem tailTrace_7599408 : CollatzResearch.WordTrace tailWord_7599408 prefixEnd_7599408 3902148993622908514950965 := by
  unfold tailWord_7599408
  simp only [CollatzResearch.WordTrace]
  refine ⟨138586590226325083201179439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184782120301766777601572585 138586590226325083201179439)
  ·
    refine ⟨207879885339487624801769159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138586590226325083201179439 207879885339487624801769159)
    ·
      refine ⟨311819828009231437202653739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207879885339487624801769159 311819828009231437202653739)
      ·
        refine ⟨467729742013847155803980609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311819828009231437202653739 467729742013847155803980609)
        ·
          refine ⟨350797306510385366852985457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467729742013847155803980609 350797306510385366852985457)
          ·
            refine ⟨263097979882789025139739093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350797306510385366852985457 263097979882789025139739093)
            ·
              refine ⟨6166358903502867776712635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263097979882789025139739093 6166358903502867776712635)
              ·
                refine ⟨9249538355254301665068953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166358903502867776712635 9249538355254301665068953)
                ·
                  refine ⟨6937153766440726248801715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249538355254301665068953 6937153766440726248801715)
                  ·
                    refine ⟨10405730649661089373202573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937153766440726248801715 10405730649661089373202573)
                    ·
                      refine ⟨3902148993622908514950965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10405730649661089373202573 3902148993622908514950965)
                      ·
                        rfl

theorem cell23_7599408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3].length) (baseStart_7599408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599408 prefixEnd_7599408 := by exact prefixLift 7599408
  have htrace : WordTrace (prefixWord ++ tailWord_7599408) baseStart_7599408 baseEnd_7599408 := by
    simpa [prefixWord, tailWord_7599408, baseEnd_7599408] using wordTrace_append hprefix tailTrace_7599408
  have hstable : (prefixWord ++ tailWord_7599408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599408).length < 2 ^ (prefixWord ++ tailWord_7599408).sum := by decide
  have hdescent : baseEnd_7599408 < baseStart_7599408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599418 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_7599418 : Nat := 118140960795 + 7599418 * 2 ^ 59
def prefixEnd_7599418 : Nat := 4983230072969 + 3 ^ 40 * 7599418 * 2
def baseEnd_7599418 : Nat := 3902154128429453475825919

theorem tailTrace_7599418 : CollatzResearch.WordTrace tailWord_7599418 prefixEnd_7599418 3902154128429453475825919 := by
  unfold tailWord_7599418
  simp only [CollatzResearch.WordTrace]
  refine ⟨69293386295653484527555727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184782363455075958740148605 69293386295653484527555727)
  ·
    refine ⟨103940079443480226791333591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69293386295653484527555727 103940079443480226791333591)
    ·
      refine ⟨155910119165220340187000387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103940079443480226791333591 155910119165220340187000387)
      ·
        refine ⟨233865178747830510280500581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155910119165220340187000387 233865178747830510280500581)
        ·
          refine ⟨43849721015218220677593859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233865178747830510280500581 43849721015218220677593859)
          ·
            refine ⟨65774581522827331016390789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43849721015218220677593859 65774581522827331016390789)
            ·
              refine ⟨12332734035530124565573273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65774581522827331016390789 12332734035530124565573273)
              ·
                refine ⟨9249550526647593424179955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12332734035530124565573273 9249550526647593424179955)
                ·
                  refine ⟨13874325789971390136269933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249550526647593424179955 13874325789971390136269933)
                  ·
                    refine ⟨5202872171239271301101225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13874325789971390136269933 5202872171239271301101225)
                    ·
                      refine ⟨3902154128429453475825919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202872171239271301101225 3902154128429453475825919)
                      ·
                        rfl

theorem cell23_7599418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_7599418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599418 prefixEnd_7599418 := by exact prefixLift 7599418
  have htrace : WordTrace (prefixWord ++ tailWord_7599418) baseStart_7599418 baseEnd_7599418 := by
    simpa [prefixWord, tailWord_7599418, baseEnd_7599418] using wordTrace_append hprefix tailTrace_7599418
  have hstable : (prefixWord ++ tailWord_7599418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599418).length < 2 ^ (prefixWord ++ tailWord_7599418).sum := by decide
  have hdescent : baseEnd_7599418 < baseStart_7599418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599448 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_7599448 : Nat := 118140960795 + 7599448 * 2 ^ 59
def prefixEnd_7599448 : Nat := 4983230072969 + 3 ^ 40 * 7599448 * 2
def baseEnd_7599448 : Nat := 3902169532849088358450781

theorem tailTrace_7599448 : CollatzResearch.WordTrace tailWord_7599448 prefixEnd_7599448 3902169532849088358450781 := by
  unfold tailWord_7599448
  simp only [CollatzResearch.WordTrace]
  refine ⟨138587319686252626616907499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184783092915003502155876665 138587319686252626616907499)
  ·
    refine ⟨207880979529378939925361249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138587319686252626616907499 207880979529378939925361249)
    ·
      refine ⟨155910734647034204944020937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207880979529378939925361249 155910734647034204944020937)
      ·
        refine ⟨116933050985275653708015703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155910734647034204944020937 116933050985275653708015703)
        ·
          refine ⟨175399576477913480562023555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116933050985275653708015703 175399576477913480562023555)
          ·
            refine ⟨263099364716870220843035333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175399576477913480562023555 263099364716870220843035333)
            ·
              refine ⟨49331130884413166408069125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263099364716870220843035333 49331130884413166408069125)
              ·
                refine ⟨9249587040827468701512961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49331130884413166408069125 9249587040827468701512961)
                ·
                  refine ⟨6937190280620601526134721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249587040827468701512961 6937190280620601526134721)
                  ·
                    refine ⟨5202892710465451144601041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937190280620601526134721 5202892710465451144601041)
                    ·
                      refine ⟨3902169532849088358450781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202892710465451144601041 3902169532849088358450781)
                      ·
                        rfl

theorem cell23_7599448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_7599448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599448 prefixEnd_7599448 := by exact prefixLift 7599448
  have htrace : WordTrace (prefixWord ++ tailWord_7599448) baseStart_7599448 baseEnd_7599448 := by
    simpa [prefixWord, tailWord_7599448, baseEnd_7599448] using wordTrace_append hprefix tailTrace_7599448
  have hstable : (prefixWord ++ tailWord_7599448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599448).length < 2 ^ (prefixWord ++ tailWord_7599448).sum := by decide
  have hdescent : baseEnd_7599448 < baseStart_7599448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599508 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7599508 : Nat := 118140960795 + 7599508 * 2 ^ 59
def prefixEnd_7599508 : Nat := 4983230072969 + 3 ^ 40 * 7599508 * 2
def baseEnd_7599508 : Nat := 3902200341688358123700505

theorem tailTrace_7599508 : CollatzResearch.WordTrace tailWord_7599508 prefixEnd_7599508 3902200341688358123700505 := by
  unfold tailWord_7599508
  simp only [CollatzResearch.WordTrace]
  refine ⟨138588413876143941740499589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184784551834858588987332785 138588413876143941740499589)
  ·
    refine ⟨25985327601776989076343673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138588413876143941740499589 25985327601776989076343673)
    ·
      refine ⟨19488995701332741807257755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25985327601776989076343673 19488995701332741807257755)
      ·
        refine ⟨29233493551999112710886633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488995701332741807257755 29233493551999112710886633)
        ·
          refine ⟨21925120163999334533164975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29233493551999112710886633 21925120163999334533164975)
          ·
            refine ⟨32887680245999001799747463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21925120163999334533164975 32887680245999001799747463)
            ·
              refine ⟨49331520368998502699621195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32887680245999001799747463 49331520368998502699621195)
              ·
                refine ⟨73997280553497754049431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49331520368998502699621195 73997280553497754049431793)
                ·
                  refine ⟨55497960415123315537073845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73997280553497754049431793 55497960415123315537073845)
                  ·
                    refine ⟨5202933788917810831600673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55497960415123315537073845 5202933788917810831600673)
                    ·
                      refine ⟨3902200341688358123700505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202933788917810831600673 3902200341688358123700505)
                      ·
                        rfl

theorem cell23_7599508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7599508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599508 prefixEnd_7599508 := by exact prefixLift 7599508
  have htrace : WordTrace (prefixWord ++ tailWord_7599508) baseStart_7599508 baseEnd_7599508 := by
    simpa [prefixWord, tailWord_7599508, baseEnd_7599508] using wordTrace_append hprefix tailTrace_7599508
  have hstable : (prefixWord ++ tailWord_7599508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599508).length < 2 ^ (prefixWord ++ tailWord_7599508).sum := by decide
  have hdescent : baseEnd_7599508 < baseStart_7599508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599578 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_7599578 : Nat := 118140960795 + 7599578 * 2 ^ 59
def prefixEnd_7599578 : Nat := 4983230072969 + 3 ^ 40 * 7599578 * 2
def baseEnd_7599578 : Nat := 433581809481574761091687

theorem tailTrace_7599578 : CollatzResearch.WordTrace tailWord_7599578 prefixEnd_7599578 433581809481574761091687 := by
  unfold tailWord_7599578
  simp only [CollatzResearch.WordTrace]
  refine ⟨69294845215508571359011847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184786253908022856957364925 69294845215508571359011847)
  ·
    refine ⟨103942267823262857038517771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69294845215508571359011847 103942267823262857038517771)
    ·
      refine ⟨155913401734894285557776657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103942267823262857038517771 155913401734894285557776657)
      ·
        refine ⟨116935051301170714168332493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155913401734894285557776657 116935051301170714168332493)
        ·
          refine ⟨43850644237939017813124685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116935051301170714168332493 43850644237939017813124685)
          ·
            refine ⟨16443991589227131679921757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43850644237939017813124685 16443991589227131679921757)
            ·
              refine ⟨6166496845960174379970659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16443991589227131679921757 6166496845960174379970659)
              ·
                refine ⟨9249745268940261569955989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166496845960174379970659 9249745268940261569955989)
                ·
                  refine ⟨433581809481574761091687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9249745268940261569955989 433581809481574761091687)
                  ·
                    rfl

theorem cell23_7599578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_7599578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599578 prefixEnd_7599578 := by exact prefixLift 7599578
  have htrace : WordTrace (prefixWord ++ tailWord_7599578) baseStart_7599578 baseEnd_7599578 := by
    simpa [prefixWord, tailWord_7599578, baseEnd_7599578] using wordTrace_append hprefix tailTrace_7599578
  have hstable : (prefixWord ++ tailWord_7599578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599578).length < 2 ^ (prefixWord ++ tailWord_7599578).sum := by decide
  have hdescent : baseEnd_7599578 < baseStart_7599578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599598 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_7599598 : Nat := 118140960795 + 7599598 * 2 ^ 59
def prefixEnd_7599598 : Nat := 4983230072969 + 3 ^ 40 * 7599598 * 2
def baseEnd_7599598 : Nat := 3902246554947262771575091

theorem tailTrace_7599598 : CollatzResearch.WordTrace tailWord_7599598 prefixEnd_7599598 3902246554947262771575091 := by
  unfold tailWord_7599598
  simp only [CollatzResearch.WordTrace]
  refine ⟨34647513790245228606471931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184786740214641219234516965 34647513790245228606471931)
  ·
    refine ⟨51971270685367842909707897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34647513790245228606471931 51971270685367842909707897)
    ·
      refine ⟨38978453014025882182280923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51971270685367842909707897 38978453014025882182280923)
      ·
        refine ⟨58467679521038823273421385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38978453014025882182280923 58467679521038823273421385)
        ·
          refine ⟨43850759640779117455066039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58467679521038823273421385 43850759640779117455066039)
          ·
            refine ⟨65776139461168676182599059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43850759640779117455066039 65776139461168676182599059)
            ·
              refine ⟨98664209191753014273898589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65776139461168676182599059 98664209191753014273898589)
              ·
                refine ⟨36999078446907380352711971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98664209191753014273898589 36999078446907380352711971)
                ·
                  refine ⟨55498617670361070529067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36999078446907380352711971 55498617670361070529067957)
                  ·
                    refine ⟨5202995406596350362100121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55498617670361070529067957 5202995406596350362100121)
                    ·
                      refine ⟨3902246554947262771575091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5202995406596350362100121 3902246554947262771575091)
                      ·
                        rfl

theorem cell23_7599598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_7599598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599598 prefixEnd_7599598 := by exact prefixLift 7599598
  have htrace : WordTrace (prefixWord ++ tailWord_7599598) baseStart_7599598 baseEnd_7599598 := by
    simpa [prefixWord, tailWord_7599598, baseEnd_7599598] using wordTrace_append hprefix tailTrace_7599598
  have hstable : (prefixWord ++ tailWord_7599598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599598).length < 2 ^ (prefixWord ++ tailWord_7599598).sum := by decide
  have hdescent : baseEnd_7599598 < baseStart_7599598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599611 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 8, 2]
def baseStart_7599611 : Nat := 118140960795 + 7599611 * 2 ^ 59
def prefixEnd_7599611 : Nat := 4983230072969 + 3 ^ 40 * 7599611 * 2
def baseEnd_7599611 : Nat := 3902253230195771220712531

theorem tailTrace_7599611 : CollatzResearch.WordTrace tailWord_7599611 prefixEnd_7599611 3902253230195771220712531 := by
  unfold tailWord_7599611
  simp only [CollatzResearch.WordTrace]
  refine ⟨277180584470914732071998687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184787056313943154714665791 277180584470914732071998687)
  ·
    refine ⟨415770876706372098107998031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277180584470914732071998687 415770876706372098107998031)
    ·
      refine ⟨623656315059558147161997047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415770876706372098107998031 623656315059558147161997047)
      ·
        refine ⟨935484472589337220742995571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623656315059558147161997047 935484472589337220742995571)
        ·
          refine ⟨1403226708884005831114493357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935484472589337220742995571 1403226708884005831114493357)
          ·
            refine ⟨526210015831502186667935009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1403226708884005831114493357 526210015831502186667935009)
            ·
              refine ⟨394657511873626640000951257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526210015831502186667935009 394657511873626640000951257)
              ·
                refine ⟨295993133905219980000713443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394657511873626640000951257 295993133905219980000713443)
                ·
                  refine ⟨443989700857829970001070165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295993133905219980000713443 443989700857829970001070165)
                  ·
                    refine ⟨5203004306927694960950041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 443989700857829970001070165 5203004306927694960950041)
                    ·
                      refine ⟨3902253230195771220712531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203004306927694960950041 3902253230195771220712531)
                      ·
                        rfl

theorem cell23_7599611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8, 2].length) (baseStart_7599611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599611 prefixEnd_7599611 := by exact prefixLift 7599611
  have htrace : WordTrace (prefixWord ++ tailWord_7599611) baseStart_7599611 baseEnd_7599611 := by
    simpa [prefixWord, tailWord_7599611, baseEnd_7599611] using wordTrace_append hprefix tailTrace_7599611
  have hstable : (prefixWord ++ tailWord_7599611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599611).length < 2 ^ (prefixWord ++ tailWord_7599611).sum := by decide
  have hdescent : baseEnd_7599611 < baseStart_7599611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599629 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 6]
def baseStart_7599629 : Nat := 118140960795 + 7599629 * 2 ^ 59
def prefixEnd_7599629 : Nat := 4983230072969 + 3 ^ 40 * 7599629 * 2
def baseEnd_7599629 : Nat := 433584719205283572254161

theorem tailTrace_7599629 : CollatzResearch.WordTrace tailWord_7599629 prefixEnd_7599629 433584719205283572254161 := by
  unfold tailWord_7599629
  simp only [CollatzResearch.WordTrace]
  refine ⟨277181240984849521146153941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184787493989899680764102627 277181240984849521146153941)
  ·
    refine ⟨6496435335582410651862983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 277181240984849521146153941 6496435335582410651862983)
    ·
      refine ⟨9744653003373615977794475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496435335582410651862983 9744653003373615977794475)
      ·
        refine ⟨14616979505060423966691713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9744653003373615977794475 14616979505060423966691713)
        ·
          refine ⟨10962734628795317975018785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14616979505060423966691713 10962734628795317975018785)
          ·
            refine ⟨8222050971596488481264089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10962734628795317975018785 8222050971596488481264089)
            ·
              refine ⟨6166538228697366360948067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222050971596488481264089 6166538228697366360948067)
              ·
                refine ⟨9249807343046049541422101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166538228697366360948067 9249807343046049541422101)
                ·
                  refine ⟨433584719205283572254161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9249807343046049541422101 433584719205283572254161)
                  ·
                    rfl

theorem cell23_7599629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_7599629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599629 prefixEnd_7599629 := by exact prefixLift 7599629
  have htrace : WordTrace (prefixWord ++ tailWord_7599629) baseStart_7599629 baseEnd_7599629 := by
    simpa [prefixWord, tailWord_7599629, baseEnd_7599629] using wordTrace_append hprefix tailTrace_7599629
  have hstable : (prefixWord ++ tailWord_7599629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599629).length < 2 ^ (prefixWord ++ tailWord_7599629).sum := by decide
  have hdescent : baseEnd_7599629 < baseStart_7599629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599645 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_7599645 : Nat := 118140960795 + 7599645 * 2 ^ 59
def prefixEnd_7599645 : Nat := 4983230072969 + 3 ^ 40 * 7599645 * 2
def baseEnd_7599645 : Nat := 3902270688538024087687375

theorem tailTrace_7599645 : CollatzResearch.WordTrace tailWord_7599645 prefixEnd_7599645 3902270688538024087687375 := by
  unfold tailWord_7599645
  simp only [CollatzResearch.WordTrace]
  refine ⟨277181824552791555878736389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184787883035194370585824259 277181824552791555878736389)
  ·
    refine ⟨51971592103648416727263073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277181824552791555878736389 51971592103648416727263073)
    ·
      refine ⟨38978694077736312545447305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51971592103648416727263073 38978694077736312545447305)
      ·
        refine ⟨29234020558302234409085479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38978694077736312545447305 29234020558302234409085479)
        ·
          refine ⟨43851030837453351613628219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234020558302234409085479 43851030837453351613628219)
          ·
            refine ⟨65776546256180027420442329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43851030837453351613628219 65776546256180027420442329)
            ·
              refine ⟨49332409692135020565331747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65776546256180027420442329 49332409692135020565331747)
              ·
                refine ⟨73998614538202530847997621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49332409692135020565331747 73998614538202530847997621)
                ·
                  refine ⟨6937370112956487266999777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73998614538202530847997621 6937370112956487266999777)
                  ·
                    refine ⟨5203027584717365450249833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937370112956487266999777 5203027584717365450249833)
                    ·
                      refine ⟨3902270688538024087687375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203027584717365450249833 3902270688538024087687375)
                      ·
                        rfl

theorem cell23_7599645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_7599645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599645 prefixEnd_7599645 := by exact prefixLift 7599645
  have htrace : WordTrace (prefixWord ++ tailWord_7599645) baseStart_7599645 baseEnd_7599645 := by
    simpa [prefixWord, tailWord_7599645, baseEnd_7599645] using wordTrace_append hprefix tailTrace_7599645
  have hstable : (prefixWord ++ tailWord_7599645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599645).length < 2 ^ (prefixWord ++ tailWord_7599645).sum := by decide
  have hdescent : baseEnd_7599645 < baseStart_7599645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599658 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7599658 : Nat := 118140960795 + 7599658 * 2 ^ 59
def prefixEnd_7599658 : Nat := 4983230072969 + 3 ^ 40 * 7599658 * 2
def baseEnd_7599658 : Nat := 3902277363786532536824815

theorem tailTrace_7599658 : CollatzResearch.WordTrace tailWord_7599658 prefixEnd_7599658 3902277363786532536824815 := by
  unfold tailWord_7599658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69295574675436114774739907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184788199134496306065973085 69295574675436114774739907)
  ·
    refine ⟨103943362013154172162109861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69295574675436114774739907 103943362013154172162109861)
    ·
      refine ⟨19489380377466407280395599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103943362013154172162109861 19489380377466407280395599)
      ·
        refine ⟨29234070566199610920593399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19489380377466407280395599 29234070566199610920593399)
        ·
          refine ⟨43851105849299416380890099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234070566199610920593399 43851105849299416380890099)
          ·
            refine ⟨65776658773949124571335149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43851105849299416380890099 65776658773949124571335149)
            ·
              refine ⟨24666247040230921714250681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65776658773949124571335149 24666247040230921714250681)
              ·
                refine ⟨18499685280173191285688011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24666247040230921714250681 18499685280173191285688011)
                ·
                  refine ⟨27749527920259786928532017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18499685280173191285688011 27749527920259786928532017)
                  ·
                    refine ⟨20812145940194840196399013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27749527920259786928532017 20812145940194840196399013)
                    ·
                      refine ⟨3902277363786532536824815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20812145940194840196399013 3902277363786532536824815)
                      ·
                        rfl

theorem cell23_7599658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7599658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599658 prefixEnd_7599658 := by exact prefixLift 7599658
  have htrace : WordTrace (prefixWord ++ tailWord_7599658) baseStart_7599658 baseEnd_7599658 := by
    simpa [prefixWord, tailWord_7599658, baseEnd_7599658] using wordTrace_append hprefix tailTrace_7599658
  have hstable : (prefixWord ++ tailWord_7599658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599658).length < 2 ^ (prefixWord ++ tailWord_7599658).sum := by decide
  have hdescent : baseEnd_7599658 < baseStart_7599658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599662 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_7599662 : Nat := 118140960795 + 7599662 * 2 ^ 59
def prefixEnd_7599662 : Nat := 4983230072969 + 3 ^ 40 * 7599662 * 2
def baseEnd_7599662 : Nat := 3902279417709150521174797

theorem tailTrace_7599662 : CollatzResearch.WordTrace tailWord_7599662 prefixEnd_7599662 3902279417709150521174797 := by
  unfold tailWord_7599662
  simp only [CollatzResearch.WordTrace]
  refine ⟨34647805574216245972763155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184788296395819978521403493 34647805574216245972763155)
  ·
    refine ⟨51971708361324368959144733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34647805574216245972763155 51971708361324368959144733)
    ·
      refine ⟨19489390635496638359679275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51971708361324368959144733 19489390635496638359679275)
      ·
        refine ⟨29234085953244957539518913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19489390635496638359679275 29234085953244957539518913)
        ·
          refine ⟨21925564464933718154639185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29234085953244957539518913 21925564464933718154639185)
          ·
            refine ⟨16444173348700288615979389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21925564464933718154639185 16444173348700288615979389)
            ·
              refine ⟨6166565005762608230992271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16444173348700288615979389 6166565005762608230992271)
              ·
                refine ⟨9249847508643912346488407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166565005762608230992271 9249847508643912346488407)
                ·
                  refine ⟨13874771262965868519732611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249847508643912346488407 13874771262965868519732611)
                  ·
                    refine ⟨20812156894448802779598917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13874771262965868519732611 20812156894448802779598917)
                    ·
                      refine ⟨3902279417709150521174797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20812156894448802779598917 3902279417709150521174797)
                      ·
                        rfl

theorem cell23_7599662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_7599662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599662 prefixEnd_7599662 := by exact prefixLift 7599662
  have htrace : WordTrace (prefixWord ++ tailWord_7599662) baseStart_7599662 baseEnd_7599662 := by
    simpa [prefixWord, tailWord_7599662, baseEnd_7599662] using wordTrace_append hprefix tailTrace_7599662
  have hstable : (prefixWord ++ tailWord_7599662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599662).length < 2 ^ (prefixWord ++ tailWord_7599662).sum := by decide
  have hdescent : baseEnd_7599662 < baseStart_7599662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599679 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 1, 2, 2]
def baseStart_7599679 : Nat := 118140960795 + 7599679 * 2 ^ 59
def prefixEnd_7599679 : Nat := 4983230072969 + 3 ^ 40 * 7599679 * 2
def baseEnd_7599679 : Nat := 3902288146880276954662219

theorem tailTrace_7599679 : CollatzResearch.WordTrace tailWord_7599679 prefixEnd_7599679 3902288146880276954662219 := by
  unfold tailWord_7599679
  simp only [CollatzResearch.WordTrace]
  refine ⟨277183064634668379685474091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184788709756445586456982727 277183064634668379685474091)
  ·
    refine ⟨415774596952002569528211137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277183064634668379685474091 415774596952002569528211137)
    ·
      refine ⟨311830947714001927146158353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415774596952002569528211137 311830947714001927146158353)
      ·
        refine ⟨233873210785501445359618765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311830947714001927146158353 233873210785501445359618765)
        ·
          refine ⟨87702454044563042009857037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233873210785501445359618765 87702454044563042009857037)
          ·
            refine ⟨32888420266711140753696389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87702454044563042009857037 32888420266711140753696389)
            ·
              refine ⟨6166578800008338891318073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32888420266711140753696389 6166578800008338891318073)
              ·
                refine ⟨4624934100006254168488555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166578800008338891318073 4624934100006254168488555)
                ·
                  refine ⟨6937401150009381252732833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624934100006254168488555 6937401150009381252732833)
                  ·
                    refine ⟨5203050862507035939549625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937401150009381252732833 5203050862507035939549625)
                    ·
                      refine ⟨3902288146880276954662219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203050862507035939549625 3902288146880276954662219)
                      ·
                        rfl

theorem cell23_7599679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_7599679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599679 prefixEnd_7599679 := by exact prefixLift 7599679
  have htrace : WordTrace (prefixWord ++ tailWord_7599679) baseStart_7599679 baseEnd_7599679 := by
    simpa [prefixWord, tailWord_7599679, baseEnd_7599679] using wordTrace_append hprefix tailTrace_7599679
  have hstable : (prefixWord ++ tailWord_7599679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599679).length < 2 ^ (prefixWord ++ tailWord_7599679).sum := by decide
  have hdescent : baseEnd_7599679 < baseStart_7599679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599681 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7599681 : Nat := 118140960795 + 7599681 * 2 ^ 59
def prefixEnd_7599681 : Nat := 4983230072969 + 3 ^ 40 * 7599681 * 2
def baseEnd_7599681 : Nat := 1300763057947195315612403

theorem tailTrace_7599681 : CollatzResearch.WordTrace tailWord_7599681 prefixEnd_7599681 1300763057947195315612403 := by
  unfold tailWord_7599681
  simp only [CollatzResearch.WordTrace]
  refine ⟨277183137580661134027046897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184788758387107422684697931 277183137580661134027046897)
  ·
    refine ⟨207887353185495850520285173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277183137580661134027046897 207887353185495850520285173)
    ·
      refine ⟨19489439361140235986276735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207887353185495850520285173 19489439361140235986276735)
      ·
        refine ⟨29234159041710353979415103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19489439361140235986276735 29234159041710353979415103)
        ·
          refine ⟨43851238562565530969122655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234159041710353979415103 43851238562565530969122655)
          ·
            refine ⟨65776857843848296453683983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43851238562565530969122655 65776857843848296453683983)
            ·
              refine ⟨98665286765772444680525975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65776857843848296453683983 98665286765772444680525975)
              ·
                refine ⟨147997930148658667020788963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98665286765772444680525975 147997930148658667020788963)
                ·
                  refine ⟨221996895222988000531183445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147997930148658667020788963 221996895222988000531183445)
                  ·
                    refine ⟨1300763057947195315612403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221996895222988000531183445 1300763057947195315612403)
                    ·
                      rfl

theorem cell23_7599681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7599681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599681 prefixEnd_7599681 := by exact prefixLift 7599681
  have htrace : WordTrace (prefixWord ++ tailWord_7599681) baseStart_7599681 baseEnd_7599681 := by
    simpa [prefixWord, tailWord_7599681, baseEnd_7599681] using wordTrace_append hprefix tailTrace_7599681
  have hstable : (prefixWord ++ tailWord_7599681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599681).length < 2 ^ (prefixWord ++ tailWord_7599681).sum := by decide
  have hdescent : baseEnd_7599681 < baseStart_7599681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599701 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7599701 : Nat := 118140960795 + 7599701 * 2 ^ 59
def prefixEnd_7599701 : Nat := 4983230072969 + 3 ^ 40 * 7599701 * 2
def baseEnd_7599701 : Nat := 3902299443454675868587117

theorem tailTrace_7599701 : CollatzResearch.WordTrace tailWord_7599701 prefixEnd_7599701 3902299443454675868587117 := by
  unfold tailWord_7599701
  simp only [CollatzResearch.WordTrace]
  refine ⟨277183867040588677442774957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184789244693725784961849971 277183867040588677442774957)
  ·
    refine ⟨103943950140220754041040609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277183867040588677442774957 103943950140220754041040609)
    ·
      refine ⟨77957962605165565530780457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103943950140220754041040609 77957962605165565530780457)
      ·
        refine ⟨58468471953874174148085343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77957962605165565530780457 58468471953874174148085343)
        ·
          refine ⟨87702707930811261222128015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58468471953874174148085343 87702707930811261222128015)
          ·
            refine ⟨131554061896216891833192023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87702707930811261222128015 131554061896216891833192023)
            ·
              refine ⟨197331092844325337749788035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131554061896216891833192023 197331092844325337749788035)
              ·
                refine ⟨295996639266488006624682053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197331092844325337749788035 295996639266488006624682053)
                ·
                  refine ⟨55499369862466501242127885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295996639266488006624682053 55499369862466501242127885)
                  ·
                    refine ⟨20812263698424937965797957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55499369862466501242127885 20812263698424937965797957)
                    ·
                      refine ⟨3902299443454675868587117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20812263698424937965797957 3902299443454675868587117)
                      ·
                        rfl

theorem cell23_7599701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7599701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599701 prefixEnd_7599701 := by exact prefixLift 7599701
  have htrace : WordTrace (prefixWord ++ tailWord_7599701) baseStart_7599701 baseEnd_7599701 := by
    simpa [prefixWord, tailWord_7599701, baseEnd_7599701] using wordTrace_append hprefix tailTrace_7599701
  have hstable : (prefixWord ++ tailWord_7599701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599701).length < 2 ^ (prefixWord ++ tailWord_7599701).sum := by decide
  have hdescent : baseEnd_7599701 < baseStart_7599701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599721 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_7599721 : Nat := 118140960795 + 7599721 * 2 ^ 59
def prefixEnd_7599721 : Nat := 4983230072969 + 3 ^ 40 * 7599721 * 2
def baseEnd_7599721 : Nat := 3902309713067765790337025

theorem tailTrace_7599721 : CollatzResearch.WordTrace tailWord_7599721 prefixEnd_7599721 3902309713067765790337025 := by
  unfold tailWord_7599721
  simp only [CollatzResearch.WordTrace]
  refine ⟨277184596500516220858503017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184789731000344147239002011 277184596500516220858503017)
  ·
    refine ⟨207888447375387165643877263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277184596500516220858503017 207888447375387165643877263)
    ·
      refine ⟨311832671063080748465815895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207888447375387165643877263 311832671063080748465815895)
      ·
        refine ⟨467749006594621122698723843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311832671063080748465815895 467749006594621122698723843)
        ·
          refine ⟨701623509891931684048085765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467749006594621122698723843 701623509891931684048085765)
          ·
            refine ⟨131554408104737190759016081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 701623509891931684048085765 131554408104737190759016081)
            ·
              refine ⟨98665806078552893069262061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131554408104737190759016081 98665806078552893069262061)
              ·
                refine ⟨36999677279457334900973273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98665806078552893069262061 36999677279457334900973273)
                ·
                  refine ⟨27749757959593001175729955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36999677279457334900973273 27749757959593001175729955)
                  ·
                    refine ⟨41624636939389501763594933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27749757959593001175729955 41624636939389501763594933)
                    ·
                      refine ⟨3902309713067765790337025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41624636939389501763594933 3902309713067765790337025)
                      ·
                        rfl

theorem cell23_7599721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_7599721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599721 prefixEnd_7599721 := by exact prefixLift 7599721
  have htrace : WordTrace (prefixWord ++ tailWord_7599721) baseStart_7599721 baseEnd_7599721 := by
    simpa [prefixWord, tailWord_7599721, baseEnd_7599721] using wordTrace_append hprefix tailTrace_7599721
  have hstable : (prefixWord ++ tailWord_7599721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599721).length < 2 ^ (prefixWord ++ tailWord_7599721).sum := by decide
  have hdescent : baseEnd_7599721 < baseStart_7599721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599722 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_7599722 : Nat := 118140960795 + 7599722 * 2 ^ 59
def prefixEnd_7599722 : Nat := 4983230072969 + 3 ^ 40 * 7599722 * 2
def baseEnd_7599722 : Nat := 3902310226548420286424521

theorem tailTrace_7599722 : CollatzResearch.WordTrace tailWord_7599722 prefixEnd_7599722 3902310226548420286424521 := by
  unfold tailWord_7599722
  simp only [CollatzResearch.WordTrace]
  refine ⟨69296158243378149507322355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184789755315675065352859613 69296158243378149507322355)
  ·
    refine ⟨103944237365067224260983533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69296158243378149507322355 103944237365067224260983533)
    ·
      refine ⟨38979089011900209097868825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103944237365067224260983533 38979089011900209097868825)
      ·
        refine ⟨29234316758925156823401619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38979089011900209097868825 29234316758925156823401619)
        ·
          refine ⟨43851475138387735235102429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234316758925156823401619 43851475138387735235102429)
          ·
            refine ⟨16444303176895400713163411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43851475138387735235102429 16444303176895400713163411)
            ·
              refine ⟨24666454765343101069745117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16444303176895400713163411 24666454765343101069745117)
              ·
                refine ⟨9249920537003662901154419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24666454765343101069745117 9249920537003662901154419)
                ·
                  refine ⟨13874880805505494351731629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249920537003662901154419 13874880805505494351731629)
                  ·
                    refine ⟨5203080302064560381899361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13874880805505494351731629 5203080302064560381899361)
                    ·
                      refine ⟨3902310226548420286424521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203080302064560381899361 3902310226548420286424521)
                      ·
                        rfl

theorem cell23_7599722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_7599722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599722 prefixEnd_7599722 := by exact prefixLift 7599722
  have htrace : WordTrace (prefixWord ++ tailWord_7599722) baseStart_7599722 baseEnd_7599722 := by
    simpa [prefixWord, tailWord_7599722, baseEnd_7599722] using wordTrace_append hprefix tailTrace_7599722
  have hstable : (prefixWord ++ tailWord_7599722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599722).length < 2 ^ (prefixWord ++ tailWord_7599722).sum := by decide
  have hdescent : baseEnd_7599722 < baseStart_7599722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599758 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_7599758 : Nat := 118140960795 + 7599758 * 2 ^ 59
def prefixEnd_7599758 : Nat := 4983230072969 + 3 ^ 40 * 7599758 * 2
def baseEnd_7599758 : Nat := 433592079094664682841595

theorem tailTrace_7599758 : CollatzResearch.WordTrace tailWord_7599758 prefixEnd_7599758 433592079094664682841595 := by
  unfold tailWord_7599758
  simp only [CollatzResearch.WordTrace]
  refine ⟨34648243250172772022199991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184790630667588117451733285 34648243250172772022199991)
  ·
    refine ⟨51972364875259158033299987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34648243250172772022199991 51972364875259158033299987)
    ·
      refine ⟨77958547312888737049949981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51972364875259158033299987 77958547312888737049949981)
      ·
        refine ⟨29234455242333276393731243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77958547312888737049949981 29234455242333276393731243)
        ·
          refine ⟨43851682863499914590596865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234455242333276393731243 43851682863499914590596865)
          ·
            refine ⟨32888762147624935942947649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43851682863499914590596865 32888762147624935942947649)
            ·
              refine ⟨24666571610718701957210737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32888762147624935942947649 24666571610718701957210737)
              ·
                refine ⟨18499928708039026467908053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24666571610718701957210737 18499928708039026467908053)
                ·
                  refine ⟨433592079094664682841595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18499928708039026467908053 433592079094664682841595)
                  ·
                    rfl

theorem cell23_7599758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_7599758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599758 prefixEnd_7599758 := by exact prefixLift 7599758
  have htrace : WordTrace (prefixWord ++ tailWord_7599758) baseStart_7599758 baseEnd_7599758 := by
    simpa [prefixWord, tailWord_7599758, baseEnd_7599758] using wordTrace_append hprefix tailTrace_7599758
  have hstable : (prefixWord ++ tailWord_7599758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599758).length < 2 ^ (prefixWord ++ tailWord_7599758).sum := by decide
  have hdescent : baseEnd_7599758 < baseStart_7599758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599808 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_7599808 : Nat := 118140960795 + 7599808 * 2 ^ 59
def prefixEnd_7599808 : Nat := 4983230072969 + 3 ^ 40 * 7599808 * 2
def baseEnd_7599808 : Nat := 3902354385884706949949125

theorem tailTrace_7599808 : CollatzResearch.WordTrace tailWord_7599808 prefixEnd_7599808 3902354385884706949949125 := by
  unfold tailWord_7599808
  simp only [CollatzResearch.WordTrace]
  refine ⟨138593884825600517358460039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184791846434134023144613385 138593884825600517358460039)
  ·
    refine ⟨207890827238400776037690059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138593884825600517358460039 207890827238400776037690059)
    ·
      refine ⟨311836240857601164056535089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207890827238400776037690059 311836240857601164056535089)
      ·
        refine ⟨233877180643200873042401317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311836240857601164056535089 233877180643200873042401317)
        ·
          refine ⟨43851971370600163695450247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233877180643200873042401317 43851971370600163695450247)
          ·
            refine ⟨65777957055900245543175371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43851971370600163695450247 65777957055900245543175371)
            ·
              refine ⟨98666935583850368314763057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65777957055900245543175371 98666935583850368314763057)
              ·
                refine ⟨74000201687887776236072293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98666935583850368314763057 74000201687887776236072293)
                ·
                  refine ⟨13875037816478958044263555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74000201687887776236072293 13875037816478958044263555)
                  ·
                    refine ⟨20812556724718437066395333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13875037816478958044263555 20812556724718437066395333)
                    ·
                      refine ⟨3902354385884706949949125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20812556724718437066395333 3902354385884706949949125)
                      ·
                        rfl

theorem cell23_7599808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_7599808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599808 prefixEnd_7599808 := by exact prefixLift 7599808
  have htrace : WordTrace (prefixWord ++ tailWord_7599808) baseStart_7599808 baseEnd_7599808 := by
    simpa [prefixWord, tailWord_7599808, baseEnd_7599808] using wordTrace_append hprefix tailTrace_7599808
  have hstable : (prefixWord ++ tailWord_7599808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599808).length < 2 ^ (prefixWord ++ tailWord_7599808).sum := by decide
  have hdescent : baseEnd_7599808 < baseStart_7599808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599811 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_7599811 : Nat := 118140960795 + 7599811 * 2 ^ 59
def prefixEnd_7599811 : Nat := 4983230072969 + 3 ^ 40 * 7599811 * 2
def baseEnd_7599811 : Nat := 3902355926326670438211611

theorem tailTrace_7599811 : CollatzResearch.WordTrace tailWord_7599811 prefixEnd_7599811 3902355926326670438211611 := by
  unfold tailWord_7599811
  simp only [CollatzResearch.WordTrace]
  refine ⟨277187879070190166229279287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184791919380126777486186191 277187879070190166229279287)
  ·
    refine ⟨415781818605285249343918931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277187879070190166229279287 415781818605285249343918931)
    ·
      refine ⟨623672727907927874015878397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415781818605285249343918931 623672727907927874015878397)
      ·
        refine ⟨233877272965472952755954399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623672727907927874015878397 233877272965472952755954399)
        ·
          refine ⟨350815909448209429133931599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233877272965472952755954399 350815909448209429133931599)
          ·
            refine ⟨526223864172314143700897399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350815909448209429133931599 526223864172314143700897399)
            ·
              refine ⟨789335796258471215551346099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526223864172314143700897399 789335796258471215551346099)
              ·
                refine ⟨1184003694387706823327019149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789335796258471215551346099 1184003694387706823327019149)
                ·
                  refine ⟨444001385395390058747632181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184003694387706823327019149 444001385395390058747632181)
                  ·
                    refine ⟨41625129880817818007590517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 444001385395390058747632181 41625129880817818007590517)
                    ·
                      refine ⟨3902355926326670438211611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41625129880817818007590517 3902355926326670438211611)
                      ·
                        rfl

theorem cell23_7599811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_7599811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599811 prefixEnd_7599811 := by exact prefixLift 7599811
  have htrace : WordTrace (prefixWord ++ tailWord_7599811) baseStart_7599811 baseEnd_7599811 := by
    simpa [prefixWord, tailWord_7599811, baseEnd_7599811] using wordTrace_append hprefix tailTrace_7599811
  have hstable : (prefixWord ++ tailWord_7599811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599811).length < 2 ^ (prefixWord ++ tailWord_7599811).sum := by decide
  have hdescent : baseEnd_7599811 < baseStart_7599811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599825 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_7599825 : Nat := 118140960795 + 7599825 * 2 ^ 59
def prefixEnd_7599825 : Nat := 4983230072969 + 3 ^ 40 * 7599825 * 2
def baseEnd_7599825 : Nat := 3902363115055833383436547

theorem tailTrace_7599825 : CollatzResearch.WordTrace tailWord_7599825 prefixEnd_7599825 3902363115055833383436547 := by
  unfold tailWord_7599825
  simp only [CollatzResearch.WordTrace]
  refine ⟨277188389692139446620288929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184792259794759631080192619 277188389692139446620288929)
  ·
    refine ⟨207891292269104584965216697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277188389692139446620288929 207891292269104584965216697)
    ·
      refine ⟨155918469201828438723912523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207891292269104584965216697 155918469201828438723912523)
      ·
        refine ⟨233877703802742658085868785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155918469201828438723912523 233877703802742658085868785)
        ·
          refine ⟨175408277852056993564401589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233877703802742658085868785 175408277852056993564401589)
          ·
            refine ⟨16444526048630343146662649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175408277852056993564401589 16444526048630343146662649)
            ·
              refine ⟨12333394536472757359996987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16444526048630343146662649 12333394536472757359996987)
              ·
                refine ⟨18500091804709136039995481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12333394536472757359996987 18500091804709136039995481)
                ·
                  refine ⟨13875068853531852029996611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18500091804709136039995481 13875068853531852029996611)
                  ·
                    refine ⟨20812603280297778044994917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13875068853531852029996611 20812603280297778044994917)
                    ·
                      refine ⟨3902363115055833383436547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20812603280297778044994917 3902363115055833383436547)
                      ·
                        rfl

theorem cell23_7599825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_7599825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599825 prefixEnd_7599825 := by exact prefixLift 7599825
  have htrace : WordTrace (prefixWord ++ tailWord_7599825) baseStart_7599825 baseEnd_7599825 := by
    simpa [prefixWord, tailWord_7599825, baseEnd_7599825] using wordTrace_append hprefix tailTrace_7599825
  have hstable : (prefixWord ++ tailWord_7599825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599825).length < 2 ^ (prefixWord ++ tailWord_7599825).sum := by decide
  have hdescent : baseEnd_7599825 < baseStart_7599825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599845 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7599845 : Nat := 118140960795 + 7599845 * 2 ^ 59
def prefixEnd_7599845 : Nat := 4983230072969 + 3 ^ 40 * 7599845 * 2
def baseEnd_7599845 : Nat := 3902373384668923305186455

theorem tailTrace_7599845 : CollatzResearch.WordTrace tailWord_7599845 prefixEnd_7599845 3902373384668923305186455 := by
  unfold tailWord_7599845
  simp only [CollatzResearch.WordTrace]
  refine ⟨277189119152066990036016989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184792746101377993357344659 277189119152066990036016989)
  ·
    refine ⟨103945919682025121263506371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277189119152066990036016989 103945919682025121263506371)
    ·
      refine ⟨155918879523037681895259557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103945919682025121263506371 155918879523037681895259557)
      ·
        refine ⟨29234789910569565355361167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155918879523037681895259557 29234789910569565355361167)
        ·
          refine ⟨43852184865854348033041751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234789910569565355361167 43852184865854348033041751)
          ·
            refine ⟨65778277298781522049562627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43852184865854348033041751 65778277298781522049562627)
            ·
              refine ⟨98667415948172283074343941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65778277298781522049562627 98667415948172283074343941)
              ·
                refine ⟨18500140490282303076439489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98667415948172283074343941 18500140490282303076439489)
                ·
                  refine ⟨13875105367711727307329617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18500140490282303076439489 13875105367711727307329617)
                  ·
                    refine ⟨10406329025783795480497213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13875105367711727307329617 10406329025783795480497213)
                    ·
                      refine ⟨3902373384668923305186455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406329025783795480497213 3902373384668923305186455)
                      ·
                        rfl

theorem cell23_7599845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7599845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599845 prefixEnd_7599845 := by exact prefixLift 7599845
  have htrace : WordTrace (prefixWord ++ tailWord_7599845) baseStart_7599845 baseEnd_7599845 := by
    simpa [prefixWord, tailWord_7599845, baseEnd_7599845] using wordTrace_append hprefix tailTrace_7599845
  have hstable : (prefixWord ++ tailWord_7599845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599845).length < 2 ^ (prefixWord ++ tailWord_7599845).sum := by decide
  have hdescent : baseEnd_7599845 < baseStart_7599845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599875 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 3]
def baseStart_7599875 : Nat := 118140960795 + 7599875 * 2 ^ 59
def prefixEnd_7599875 : Nat := 4983230072969 + 3 ^ 40 * 7599875 * 2
def baseEnd_7599875 : Nat := 3902388789088558187811317

theorem tailTrace_7599875 : CollatzResearch.WordTrace tailWord_7599875 prefixEnd_7599875 3902388789088558187811317 := by
  unfold tailWord_7599875
  simp only [CollatzResearch.WordTrace]
  refine ⟨277190213341958305159609079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184793475561305536773072719 277190213341958305159609079)
  ·
    refine ⟨415785320012937457739413619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277190213341958305159609079 415785320012937457739413619)
    ·
      refine ⟨623677980019406186609120429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415785320012937457739413619 623677980019406186609120429)
      ·
        refine ⟨233879242507277319978420161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623677980019406186609120429 233879242507277319978420161)
        ·
          refine ⟨175409431880457989983815121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233879242507277319978420161 175409431880457989983815121)
          ·
            refine ⟨131557073910343492487861341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175409431880457989983815121 131557073910343492487861341)
            ·
              refine ⟨49333902716378809682948003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131557073910343492487861341 49333902716378809682948003)
              ·
                refine ⟨74000854074568214524422005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49333902716378809682948003 74000854074568214524422005)
                ·
                  refine ⟨6937580069490770111664563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74000854074568214524422005 6937580069490770111664563)
                  ·
                    refine ⟨10406370104236155167496845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937580069490770111664563 10406370104236155167496845)
                    ·
                      refine ⟨3902388789088558187811317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406370104236155167496845 3902388789088558187811317)
                      ·
                        rfl

theorem cell23_7599875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_7599875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599875 prefixEnd_7599875 := by exact prefixLift 7599875
  have htrace : WordTrace (prefixWord ++ tailWord_7599875) baseStart_7599875 baseEnd_7599875 := by
    simpa [prefixWord, tailWord_7599875, baseEnd_7599875] using wordTrace_append hprefix tailTrace_7599875
  have hstable : (prefixWord ++ tailWord_7599875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599875).length < 2 ^ (prefixWord ++ tailWord_7599875).sum := by decide
  have hdescent : baseEnd_7599875 < baseStart_7599875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599879 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7599879 : Nat := 118140960795 + 7599879 * 2 ^ 59
def prefixEnd_7599879 : Nat := 4983230072969 + 3 ^ 40 * 7599879 * 2
def baseEnd_7599879 : Nat := 3902390843011176172161299

theorem tailTrace_7599879 : CollatzResearch.WordTrace tailWord_7599879 prefixEnd_7599879 3902390843011176172161299 := by
  unfold tailWord_7599879
  simp only [CollatzResearch.WordTrace]
  refine ⟨277190359233943813842754691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184793572822629209228503127 277190359233943813842754691)
  ·
    refine ⟨415785538850915720764132037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277190359233943813842754691 415785538850915720764132037)
    ·
      refine ⟨77959788534546697643274757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415785538850915720764132037 77959788534546697643274757)
      ·
        refine ⟨14617460350227505808114017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77959788534546697643274757 14617460350227505808114017)
        ·
          refine ⟨10963095262670629356085513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14617460350227505808114017 10963095262670629356085513)
          ·
            refine ⟨8222321447002972017064135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963095262670629356085513 8222321447002972017064135)
            ·
              refine ⟨12333482170504458025596203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222321447002972017064135 12333482170504458025596203)
              ·
                refine ⟨18500223255756687038394305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12333482170504458025596203 18500223255756687038394305)
                ·
                  refine ⟨13875167441817515278795729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18500223255756687038394305 13875167441817515278795729)
                  ·
                    refine ⟨10406375581363136459096797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13875167441817515278795729 10406375581363136459096797)
                    ·
                      refine ⟨3902390843011176172161299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406375581363136459096797 3902390843011176172161299)
                      ·
                        rfl

theorem cell23_7599879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7599879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599879 prefixEnd_7599879 := by exact prefixLift 7599879
  have htrace : WordTrace (prefixWord ++ tailWord_7599879) baseStart_7599879 baseEnd_7599879 := by
    simpa [prefixWord, tailWord_7599879, baseEnd_7599879] using wordTrace_append hprefix tailTrace_7599879
  have hstable : (prefixWord ++ tailWord_7599879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599879).length < 2 ^ (prefixWord ++ tailWord_7599879).sum := by decide
  have hdescent : baseEnd_7599879 < baseStart_7599879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599909 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 1, 1, 3]
def baseStart_7599909 : Nat := 118140960795 + 7599909 * 2 ^ 59
def prefixEnd_7599909 : Nat := 4983230072969 + 3 ^ 40 * 7599909 * 2
def baseEnd_7599909 : Nat := 3902406247430811054786161

theorem tailTrace_7599909 : CollatzResearch.WordTrace tailWord_7599909 prefixEnd_7599909 3902406247430811054786161 := by
  unfold tailWord_7599909
  simp only [CollatzResearch.WordTrace]
  refine ⟨277191453423835128966346781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184794302282556752644231187 277191453423835128966346781)
  ·
    refine ⟨103946795033938173362380043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277191453423835128966346781 103946795033938173362380043)
    ·
      refine ⟨155920192550907260043570065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103946795033938173362380043 155920192550907260043570065)
      ·
        refine ⟨116940144413180445032677549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155920192550907260043570065 116940144413180445032677549)
        ·
          refine ⟨43852554154942666887254081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116940144413180445032677549 43852554154942666887254081)
          ·
            refine ⟨32889415616207000165440561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43852554154942666887254081 32889415616207000165440561)
            ·
              refine ⟨24667061712155250124080421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32889415616207000165440561 24667061712155250124080421)
              ·
                refine ⟨4625074071029109398265079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24667061712155250124080421 4625074071029109398265079)
                ·
                  refine ⟨6937611106543664097397619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625074071029109398265079 6937611106543664097397619)
                  ·
                    refine ⟨10406416659815496146096429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937611106543664097397619 10406416659815496146096429)
                    ·
                      refine ⟨3902406247430811054786161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406416659815496146096429 3902406247430811054786161)
                      ·
                        rfl

theorem cell23_7599909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_7599909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599909 prefixEnd_7599909 := by exact prefixLift 7599909
  have htrace : WordTrace (prefixWord ++ tailWord_7599909) baseStart_7599909 baseEnd_7599909 := by
    simpa [prefixWord, tailWord_7599909, baseEnd_7599909] using wordTrace_append hprefix tailTrace_7599909
  have hstable : (prefixWord ++ tailWord_7599909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599909).length < 2 ^ (prefixWord ++ tailWord_7599909).sum := by decide
  have hdescent : baseEnd_7599909 < baseStart_7599909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599929 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_7599929 : Nat := 118140960795 + 7599929 * 2 ^ 59
def prefixEnd_7599929 : Nat := 4983230072969 + 3 ^ 40 * 7599929 * 2
def baseEnd_7599929 : Nat := 1300805505681300325512023

theorem tailTrace_7599929 : CollatzResearch.WordTrace tailWord_7599929 prefixEnd_7599929 1300805505681300325512023 := by
  unfold tailWord_7599929
  simp only [CollatzResearch.WordTrace]
  refine ⟨277192182883762672382074841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184794788589175114921383227 277192182883762672382074841)
  ·
    refine ⟨207894137162822004286556131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277192182883762672382074841 207894137162822004286556131)
    ·
      refine ⟨311841205744233006429834197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207894137162822004286556131 311841205744233006429834197)
      ·
        refine ⟨7308778259630461088199239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 311841205744233006429834197 7308778259630461088199239)
        ·
          refine ⟨10963167389445691632298859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308778259630461088199239 10963167389445691632298859)
          ·
            refine ⟨16444751084168537448448289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963167389445691632298859 16444751084168537448448289)
            ·
              refine ⟨12333563313126403086336217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16444751084168537448448289 12333563313126403086336217)
              ·
                refine ⟨9250172484844802314752163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12333563313126403086336217 9250172484844802314752163)
                ·
                  refine ⟨13875258727267203472128245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250172484844802314752163 13875258727267203472128245)
                  ·
                    refine ⟨1300805505681300325512023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13875258727267203472128245 1300805505681300325512023)
                    ·
                      rfl

theorem cell23_7599929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_7599929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599929 prefixEnd_7599929 := by exact prefixLift 7599929
  have htrace : WordTrace (prefixWord ++ tailWord_7599929) baseStart_7599929 baseEnd_7599929 := by
    simpa [prefixWord, tailWord_7599929, baseEnd_7599929] using wordTrace_append hprefix tailTrace_7599929
  have hstable : (prefixWord ++ tailWord_7599929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599929).length < 2 ^ (prefixWord ++ tailWord_7599929).sum := by decide
  have hdescent : baseEnd_7599929 < baseStart_7599929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7599949 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7599949 : Nat := 118140960795 + 7599949 * 2 ^ 59
def prefixEnd_7599949 : Nat := 4983230072969 + 3 ^ 40 * 7599949 * 2
def baseEnd_7599949 : Nat := 3902426786656990898285977

theorem tailTrace_7599949 : CollatzResearch.WordTrace tailWord_7599949 prefixEnd_7599949 3902426786656990898285977 := by
  unfold tailWord_7599949
  simp only [CollatzResearch.WordTrace]
  refine ⟨277192912343690215797802901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184795274895793477198535267 277192912343690215797802901)
  ·
    refine ⟨12993417766110478865522011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277192912343690215797802901 12993417766110478865522011)
    ·
      refine ⟨19490126649165718298283017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12993417766110478865522011 19490126649165718298283017)
      ·
        refine ⟨14617594986874288723712263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19490126649165718298283017 14617594986874288723712263)
        ·
          refine ⟨21926392480311433085568395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14617594986874288723712263 21926392480311433085568395)
          ·
            refine ⟨32889588720467149628352593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21926392480311433085568395 32889588720467149628352593)
            ·
              refine ⟨24667191540350362221264445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32889588720467149628352593 24667191540350362221264445)
              ·
                refine ⟨9250196827631385832974167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24667191540350362221264445 9250196827631385832974167)
                ·
                  refine ⟨13875295241447078749461251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250196827631385832974167 13875295241447078749461251)
                  ·
                    refine ⟨20812942862170618124191877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13875295241447078749461251 20812942862170618124191877)
                    ·
                      refine ⟨3902426786656990898285977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20812942862170618124191877 3902426786656990898285977)
                      ·
                        rfl

theorem cell23_7599949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7599949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7599949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7599949 prefixEnd_7599949 := by exact prefixLift 7599949
  have htrace : WordTrace (prefixWord ++ tailWord_7599949) baseStart_7599949 baseEnd_7599949 := by
    simpa [prefixWord, tailWord_7599949, baseEnd_7599949] using wordTrace_append hprefix tailTrace_7599949
  have hstable : (prefixWord ++ tailWord_7599949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7599949).length < 2 ^ (prefixWord ++ tailWord_7599949).sum := by decide
  have hdescent : baseEnd_7599949 < baseStart_7599949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7599949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600025 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_7600025 : Nat := 118140960795 + 7600025 * 2 ^ 59
def prefixEnd_7600025 : Nat := 4983230072969 + 3 ^ 40 * 7600025 * 2
def baseEnd_7600025 : Nat := 3902465811186732600935627

theorem tailTrace_7600025 : CollatzResearch.WordTrace tailWord_7600025 prefixEnd_7600025 3902465811186732600935627 := by
  unfold tailWord_7600025
  simp only [CollatzResearch.WordTrace]
  refine ⟨277195684291414880777569529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184797122860943253851713019 277195684291414880777569529)
  ·
    refine ⟨207896763218561160583177147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277195684291414880777569529 207896763218561160583177147)
    ·
      refine ⟨311845144827841740874765721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207896763218561160583177147 311845144827841740874765721)
      ·
        refine ⟨233883858620881305656074291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311845144827841740874765721 233883858620881305656074291)
        ·
          refine ⟨350825787931321958484111437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233883858620881305656074291 350825787931321958484111437)
          ·
            refine ⟨131559670474245734431541789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350825787931321958484111437 131559670474245734431541789)
            ·
              refine ⟨49334876427842150411828171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131559670474245734431541789 49334876427842150411828171)
              ·
                refine ⟨74002314641763225617742257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49334876427842150411828171 74002314641763225617742257)
                ·
                  refine ⟨55501735981322419213306693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74002314641763225617742257 55501735981322419213306693)
                  ·
                    refine ⟨10406575496497953602495005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55501735981322419213306693 10406575496497953602495005)
                    ·
                      refine ⟨3902465811186732600935627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406575496497953602495005 3902465811186732600935627)
                      ·
                        rfl

theorem cell23_7600025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_7600025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600025 prefixEnd_7600025 := by exact prefixLift 7600025
  have htrace : WordTrace (prefixWord ++ tailWord_7600025) baseStart_7600025 baseEnd_7600025 := by
    simpa [prefixWord, tailWord_7600025, baseEnd_7600025] using wordTrace_append hprefix tailTrace_7600025
  have hstable : (prefixWord ++ tailWord_7600025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600025).length < 2 ^ (prefixWord ++ tailWord_7600025).sum := by decide
  have hdescent : baseEnd_7600025 < baseStart_7600025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600039 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7600039 : Nat := 118140960795 + 7600039 * 2 ^ 59
def prefixEnd_7600039 : Nat := 4983230072969 + 3 ^ 40 * 7600039 * 2
def baseEnd_7600039 : Nat := 3902472999915895546160563

theorem tailTrace_7600039 : CollatzResearch.WordTrace tailWord_7600039 prefixEnd_7600039 3902472999915895546160563 := by
  unfold tailWord_7600039
  simp only [CollatzResearch.WordTrace]
  refine ⟨277196194913364161168579171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184797463275576107445719447 277196194913364161168579171)
  ·
    refine ⟨415794292370046241752868757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277196194913364161168579171 415794292370046241752868757)
    ·
      refine ⟨19490357454845917582165723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 415794292370046241752868757 19490357454845917582165723)
      ·
        refine ⟨29235536182268876373248585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19490357454845917582165723 29235536182268876373248585)
        ·
          refine ⟨21926652136701657279936439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29235536182268876373248585 21926652136701657279936439)
          ·
            refine ⟨32889978205052485919904659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21926652136701657279936439 32889978205052485919904659)
            ·
              refine ⟨49334967307578728879856989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32889978205052485919904659 49334967307578728879856989)
              ·
                refine ⟨18500612740342023329946371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49334967307578728879856989 18500612740342023329946371)
                ·
                  refine ⟨27750919110513034994919557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18500612740342023329946371 27750919110513034994919557)
                  ·
                    refine ⟨5203297333221194061547417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27750919110513034994919557 5203297333221194061547417)
                    ·
                      refine ⟨3902472999915895546160563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203297333221194061547417 3902472999915895546160563)
                      ·
                        rfl

theorem cell23_7600039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7600039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600039 prefixEnd_7600039 := by exact prefixLift 7600039
  have htrace : WordTrace (prefixWord ++ tailWord_7600039) baseStart_7600039 baseEnd_7600039 := by
    simpa [prefixWord, tailWord_7600039, baseEnd_7600039] using wordTrace_append hprefix tailTrace_7600039
  have hstable : (prefixWord ++ tailWord_7600039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600039).length < 2 ^ (prefixWord ++ tailWord_7600039).sum := by decide
  have hdescent : baseEnd_7600039 < baseStart_7600039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600055 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_7600055 : Nat := 118140960795 + 7600055 * 2 ^ 59
def prefixEnd_7600055 : Nat := 4983230072969 + 3 ^ 40 * 7600055 * 2
def baseEnd_7600055 : Nat := 3902481215606367483560489

theorem tailTrace_7600055 : CollatzResearch.WordTrace tailWord_7600055 prefixEnd_7600055 3902481215606367483560489 := by
  unfold tailWord_7600055
  simp only [CollatzResearch.WordTrace]
  refine ⟨277196778481306195901161619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184797852320870797267441079 277196778481306195901161619)
  ·
    refine ⟨415795167721959293851742429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277196778481306195901161619 415795167721959293851742429)
    ·
      refine ⟨155923187895734735194403411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415795167721959293851742429 155923187895734735194403411)
      ·
        refine ⟨233884781843602102791605117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155923187895734735194403411 233884781843602102791605117)
        ·
          refine ⟨87706793191350788546851919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233884781843602102791605117 87706793191350788546851919)
          ·
            refine ⟨131560189787026182820277879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87706793191350788546851919 131560189787026182820277879)
            ·
              refine ⟨197340284680539274230416819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131560189787026182820277879 197340284680539274230416819)
              ·
                refine ⟨296010427020808911345625229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197340284680539274230416819 296010427020808911345625229)
                ·
                  refine ⟨111003910132803341754609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296010427020808911345625229 111003910132803341754609461)
                  ·
                    refine ⟨10406616574950313289494637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111003910132803341754609461 10406616574950313289494637)
                    ·
                      refine ⟨3902481215606367483560489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406616574950313289494637 3902481215606367483560489)
                      ·
                        rfl

theorem cell23_7600055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_7600055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600055 prefixEnd_7600055 := by exact prefixLift 7600055
  have htrace : WordTrace (prefixWord ++ tailWord_7600055) baseStart_7600055 baseEnd_7600055 := by
    simpa [prefixWord, tailWord_7600055, baseEnd_7600055] using wordTrace_append hprefix tailTrace_7600055
  have hstable : (prefixWord ++ tailWord_7600055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600055).length < 2 ^ (prefixWord ++ tailWord_7600055).sum := by decide
  have hdescent : baseEnd_7600055 < baseStart_7600055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600060 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7600060 : Nat := 118140960795 + 7600060 * 2 ^ 59
def prefixEnd_7600060 : Nat := 4983230072969 + 3 ^ 40 * 7600060 * 2
def baseEnd_7600060 : Nat := 3902483783009639963997967

theorem tailTrace_7600060 : CollatzResearch.WordTrace tailWord_7600060 prefixEnd_7600060 3902483783009639963997967 := by
  unfold tailWord_7600060
  simp only [CollatzResearch.WordTrace]
  refine ⟨138598480423144040877546817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184797973897525387836729089 138598480423144040877546817)
  ·
    refine ⟨103948860317358030658160113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138598480423144040877546817 103948860317358030658160113)
    ·
      refine ⟨77961645238018522993620085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103948860317358030658160113 77961645238018522993620085)
      ·
        refine ⟨7308904241064236530651883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77961645238018522993620085 7308904241064236530651883)
        ·
          refine ⟨10963356361596354795977825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308904241064236530651883 10963356361596354795977825)
          ·
            refine ⟨8222517271197266096983369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963356361596354795977825 8222517271197266096983369)
            ·
              refine ⟨6166887953397949572737527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222517271197266096983369 6166887953397949572737527)
              ·
                refine ⟨9250331930096924359106291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166887953397949572737527 9250331930096924359106291)
                ·
                  refine ⟨13875497895145386538659437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250331930096924359106291 13875497895145386538659437)
                  ·
                    refine ⟨5203311710679519951997289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13875497895145386538659437 5203311710679519951997289)
                    ·
                      refine ⟨3902483783009639963997967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203311710679519951997289 3902483783009639963997967)
                      ·
                        rfl

theorem cell23_7600060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7600060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600060 prefixEnd_7600060 := by exact prefixLift 7600060
  have htrace : WordTrace (prefixWord ++ tailWord_7600060) baseStart_7600060 baseEnd_7600060 := by
    simpa [prefixWord, tailWord_7600060, baseEnd_7600060] using wordTrace_append hprefix tailTrace_7600060
  have hstable : (prefixWord ++ tailWord_7600060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600060).length < 2 ^ (prefixWord ++ tailWord_7600060).sum := by decide
  have hdescent : baseEnd_7600060 < baseStart_7600060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600072 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_7600072 : Nat := 118140960795 + 7600072 * 2 ^ 59
def prefixEnd_7600072 : Nat := 4983230072969 + 3 ^ 40 * 7600072 * 2
def baseEnd_7600072 : Nat := 3902489944777493917047911

theorem tailTrace_7600072 : CollatzResearch.WordTrace tailWord_7600072 prefixEnd_7600072 3902489944777493917047911 := by
  unfold tailWord_7600072
  simp only [CollatzResearch.WordTrace]
  refine ⟨138598699261122303902265235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184798265681496405203020313 138598699261122303902265235)
  ·
    refine ⟨207898048891683455853397853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138598699261122303902265235 207898048891683455853397853)
    ·
      refine ⟨77961768334381295945024195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207898048891683455853397853 77961768334381295945024195)
      ·
        refine ⟨116942652501571943917536293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77961768334381295945024195 116942652501571943917536293)
        ·
          refine ⟨21926747344044739484538055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116942652501571943917536293 21926747344044739484538055)
          ·
            refine ⟨32890121016067109226807083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21926747344044739484538055 32890121016067109226807083)
            ·
              refine ⟨49335181524100663840210625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32890121016067109226807083 49335181524100663840210625)
              ·
                refine ⟨37001386143075497880157969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49335181524100663840210625 37001386143075497880157969)
                ·
                  refine ⟨27751039607306623410118477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37001386143075497880157969 27751039607306623410118477)
                  ·
                    refine ⟨10406639852739983778794429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27751039607306623410118477 10406639852739983778794429)
                    ·
                      refine ⟨3902489944777493917047911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406639852739983778794429 3902489944777493917047911)
                      ·
                        rfl

theorem cell23_7600072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_7600072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600072 prefixEnd_7600072 := by exact prefixLift 7600072
  have htrace : WordTrace (prefixWord ++ tailWord_7600072) baseStart_7600072 baseEnd_7600072 := by
    simpa [prefixWord, tailWord_7600072, baseEnd_7600072] using wordTrace_append hprefix tailTrace_7600072
  have hstable : (prefixWord ++ tailWord_7600072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600072).length < 2 ^ (prefixWord ++ tailWord_7600072).sum := by decide
  have hdescent : baseEnd_7600072 < baseStart_7600072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600075 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 4, 5]
def baseStart_7600075 : Nat := 118140960795 + 7600075 * 2 ^ 59
def prefixEnd_7600075 : Nat := 4983230072969 + 3 ^ 40 * 7600075 * 2
def baseEnd_7600075 : Nat := 1300830495073152468436799

theorem tailTrace_7600075 : CollatzResearch.WordTrace tailWord_7600075 prefixEnd_7600075 1300830495073152468436799 := by
  unfold tailWord_7600075
  simp only [CollatzResearch.WordTrace]
  refine ⟨277197507941233739316889679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184798338627489159544593119 277197507941233739316889679)
  ·
    refine ⟨415796261911850608975334519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277197507941233739316889679 415796261911850608975334519)
    ·
      refine ⟨623694392867775913463001779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415796261911850608975334519 623694392867775913463001779)
      ·
        refine ⟨935541589301663870194502669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623694392867775913463001779 935541589301663870194502669)
        ·
          refine ⟨350828095988123951322938501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935541589301663870194502669 350828095988123951322938501)
          ·
            refine ⟨65780267997773240873050969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350828095988123951322938501 65780267997773240873050969)
            ·
              refine ⟨49335200998329930654788227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65780267997773240873050969 49335200998329930654788227)
              ·
                refine ⟨74002801497494895982182341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49335200998329930654788227 74002801497494895982182341)
                ·
                  refine ⟨13875525280780292996659189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74002801497494895982182341 13875525280780292996659189)
                  ·
                    refine ⟨1300830495073152468436799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13875525280780292996659189 1300830495073152468436799)
                    ·
                      rfl

theorem cell23_7600075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 5].length) (baseStart_7600075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600075 prefixEnd_7600075 := by exact prefixLift 7600075
  have htrace : WordTrace (prefixWord ++ tailWord_7600075) baseStart_7600075 baseEnd_7600075 := by
    simpa [prefixWord, tailWord_7600075, baseEnd_7600075] using wordTrace_append hprefix tailTrace_7600075
  have hstable : (prefixWord ++ tailWord_7600075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600075).length < 2 ^ (prefixWord ++ tailWord_7600075).sum := by decide
  have hdescent : baseEnd_7600075 < baseStart_7600075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600112 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2]
def baseStart_7600112 : Nat := 118140960795 + 7600112 * 2 ^ 59
def prefixEnd_7600112 : Nat := 4983230072969 + 3 ^ 40 * 7600112 * 2
def baseEnd_7600112 : Nat := 3902510484003673760547727

theorem tailTrace_7600112 : CollatzResearch.WordTrace tailWord_7600112 prefixEnd_7600112 3902510484003673760547727 := by
  unfold tailWord_7600112
  simp only [CollatzResearch.WordTrace]
  refine ⟨138599428721049847317993295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184799238294733129757324393 138599428721049847317993295)
  ·
    refine ⟨207899143081574770976989943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138599428721049847317993295 207899143081574770976989943)
    ·
      refine ⟨311848714622362156465484915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207899143081574770976989943 311848714622362156465484915)
      ·
        refine ⟨467773071933543234698227373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311848714622362156465484915 467773071933543234698227373)
        ·
          refine ⟨175414901975078713011835265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467773071933543234698227373 175414901975078713011835265)
          ·
            refine ⟨131561176481309034758876449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175414901975078713011835265 131561176481309034758876449)
            ·
              refine ⟨98670882360981776069157337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131561176481309034758876449 98670882360981776069157337)
              ·
                refine ⟨74003161770736332051868003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98670882360981776069157337 74003161770736332051868003)
                ·
                  refine ⟨111004742656104498077802005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74003161770736332051868003 111004742656104498077802005)
                  ·
                    refine ⟨5203347312004898347396969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111004742656104498077802005 5203347312004898347396969)
                    ·
                      refine ⟨3902510484003673760547727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203347312004898347396969 3902510484003673760547727)
                      ·
                        rfl

theorem cell23_7600112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2].length) (baseStart_7600112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600112 prefixEnd_7600112 := by exact prefixLift 7600112
  have htrace : WordTrace (prefixWord ++ tailWord_7600112) baseStart_7600112 baseEnd_7600112 := by
    simpa [prefixWord, tailWord_7600112, baseEnd_7600112] using wordTrace_append hprefix tailTrace_7600112
  have hstable : (prefixWord ++ tailWord_7600112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600112).length < 2 ^ (prefixWord ++ tailWord_7600112).sum := by decide
  have hdescent : baseEnd_7600112 < baseStart_7600112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600125 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7600125 : Nat := 118140960795 + 7600125 * 2 ^ 59
def prefixEnd_7600125 : Nat := 4983230072969 + 3 ^ 40 * 7600125 * 2
def baseEnd_7600125 : Nat := 3902517159252182209685167

theorem tailTrace_7600125 : CollatzResearch.WordTrace tailWord_7600125 prefixEnd_7600125 3902517159252182209685167 := by
  unfold tailWord_7600125
  simp only [CollatzResearch.WordTrace]
  refine ⟨277199331591052597856209829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184799554394035065237473219 277199331591052597856209829)
  ·
    refine ⟨51974874673322362098039343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277199331591052597856209829 51974874673322362098039343)
    ·
      refine ⟨77962312009983543147059015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51974874673322362098039343 77962312009983543147059015)
      ·
        refine ⟨116943468014975314720588523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77962312009983543147059015 116943468014975314720588523)
        ·
          refine ⟨175415202022462972080882785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116943468014975314720588523 175415202022462972080882785)
          ·
            refine ⟨131561401516847229060662089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175415202022462972080882785 131561401516847229060662089)
            ·
              refine ⟨98671051137635421795496567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131561401516847229060662089 98671051137635421795496567)
              ·
                refine ⟨148006576706453132693244851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98671051137635421795496567 148006576706453132693244851)
                ·
                  refine ⟨222009865059679699039867277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148006576706453132693244851 222009865059679699039867277)
                  ·
                    refine ⟨83253699397379887139950229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222009865059679699039867277 83253699397379887139950229)
                    ·
                      refine ⟨3902517159252182209685167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83253699397379887139950229 3902517159252182209685167)
                      ·
                        rfl

theorem cell23_7600125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7600125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600125 prefixEnd_7600125 := by exact prefixLift 7600125
  have htrace : WordTrace (prefixWord ++ tailWord_7600125) baseStart_7600125 baseEnd_7600125 := by
    simpa [prefixWord, tailWord_7600125, baseEnd_7600125] using wordTrace_append hprefix tailTrace_7600125
  have hstable : (prefixWord ++ tailWord_7600125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600125).length < 2 ^ (prefixWord ++ tailWord_7600125).sum := by decide
  have hdescent : baseEnd_7600125 < baseStart_7600125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600141 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7600141 : Nat := 118140960795 + 7600141 * 2 ^ 59
def prefixEnd_7600141 : Nat := 4983230072969 + 3 ^ 40 * 7600141 * 2
def baseEnd_7600141 : Nat := 3902525374942654147085095

theorem tailTrace_7600141 : CollatzResearch.WordTrace tailWord_7600141 prefixEnd_7600141 3902525374942654147085095 := by
  unfold tailWord_7600141
  simp only [CollatzResearch.WordTrace]
  refine ⟨277199915158994632588792277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184799943439329755059194851 277199915158994632588792277)
  ·
    refine ⟨6496873011538936701299819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 277199915158994632588792277 6496873011538936701299819)
    ·
      refine ⟨9745309517308405051949729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496873011538936701299819 9745309517308405051949729)
      ·
        refine ⟨7308982137981303788962297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9745309517308405051949729 7308982137981303788962297)
        ·
          refine ⟨5481736603485977841721723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7308982137981303788962297 5481736603485977841721723)
          ·
            refine ⟨8222604905228966762582585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481736603485977841721723 8222604905228966762582585)
            ·
              refine ⟨6166953678921725071936939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222604905228966762582585 6166953678921725071936939)
              ·
                refine ⟨9250430518382587607905409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166953678921725071936939 9250430518382587607905409)
                ·
                  refine ⟨6937822888786940705929057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250430518382587607905409 6937822888786940705929057)
                  ·
                    refine ⟨5203367166590205529446793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937822888786940705929057 5203367166590205529446793)
                    ·
                      refine ⟨3902525374942654147085095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203367166590205529446793 3902525374942654147085095)
                      ·
                        rfl

theorem cell23_7600141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7600141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600141 prefixEnd_7600141 := by exact prefixLift 7600141
  have htrace : WordTrace (prefixWord ++ tailWord_7600141) baseStart_7600141 baseEnd_7600141 := by
    simpa [prefixWord, tailWord_7600141, baseEnd_7600141] using wordTrace_append hprefix tailTrace_7600141
  have hstable : (prefixWord ++ tailWord_7600141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600141).length < 2 ^ (prefixWord ++ tailWord_7600141).sum := by decide
  have hdescent : baseEnd_7600141 < baseStart_7600141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600152 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 6]
def baseStart_7600152 : Nat := 118140960795 + 7600152 * 2 ^ 59
def prefixEnd_7600152 : Nat := 4983230072969 + 3 ^ 40 * 7600152 * 2
def baseEnd_7600152 : Nat := 433614558136650400449727

theorem tailTrace_7600152 : CollatzResearch.WordTrace tailWord_7600152 prefixEnd_7600152 433614558136650400449727 := by
  unfold tailWord_7600152
  simp only [CollatzResearch.WordTrace]
  refine ⟨138600158180977390733721355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184800210907969854311628473 138600158180977390733721355)
  ·
    refine ⟨207900237271466086100582033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138600158180977390733721355 207900237271466086100582033)
    ·
      refine ⟨155925177953599564575436525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207900237271466086100582033 155925177953599564575436525)
      ·
        refine ⟨58471941732599836715788697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155925177953599564575436525 58471941732599836715788697)
        ·
          refine ⟨43853956299449877536841523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58471941732599836715788697 43853956299449877536841523)
          ·
            refine ⟨65780934449174816305262285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43853956299449877536841523 65780934449174816305262285)
            ·
              refine ⟨24667850418440556114473357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65780934449174816305262285 24667850418440556114473357)
              ·
                refine ⟨9250443906915208542927509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24667850418440556114473357 9250443906915208542927509)
                ·
                  refine ⟨433614558136650400449727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9250443906915208542927509 433614558136650400449727)
                  ·
                    rfl

theorem cell23_7600152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_7600152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600152 prefixEnd_7600152 := by exact prefixLift 7600152
  have htrace : WordTrace (prefixWord ++ tailWord_7600152) baseStart_7600152 baseEnd_7600152 := by
    simpa [prefixWord, tailWord_7600152, baseEnd_7600152] using wordTrace_append hprefix tailTrace_7600152
  have hstable : (prefixWord ++ tailWord_7600152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600152).length < 2 ^ (prefixWord ++ tailWord_7600152).sum := by decide
  have hdescent : baseEnd_7600152 < baseStart_7600152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600175 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_7600175 : Nat := 118140960795 + 7600175 * 2 ^ 59
def prefixEnd_7600175 : Nat := 4983230072969 + 3 ^ 40 * 7600175 * 2
def baseEnd_7600175 : Nat := 3902542833284907014059937

theorem tailTrace_7600175 : CollatzResearch.WordTrace tailWord_7600175 prefixEnd_7600175 3902542833284907014059937 := by
  unfold tailWord_7600175
  simp only [CollatzResearch.WordTrace]
  refine ⟨277201155240871456395529979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184800770160580970930353319 277201155240871456395529979)
  ·
    refine ⟨415801732861307184593294969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277201155240871456395529979 415801732861307184593294969)
    ·
      refine ⟨311851299645980388444971227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415801732861307184593294969 311851299645980388444971227)
      ·
        refine ⟨467776949468970582667456841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311851299645980388444971227 467776949468970582667456841)
        ·
          refine ⟨350832712101727937000592631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467776949468970582667456841 350832712101727937000592631)
          ·
            refine ⟨526249068152591905500888947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350832712101727937000592631 526249068152591905500888947)
            ·
              refine ⟨789373602228887858251333421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526249068152591905500888947 789373602228887858251333421)
              ·
                refine ⟨296015100835832946844250033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789373602228887858251333421 296015100835832946844250033)
                ·
                  refine ⟨222011325626874710133187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296015100835832946844250033 222011325626874710133187525)
                  ·
                    refine ⟨41627123555039008149972661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222011325626874710133187525 41627123555039008149972661)
                    ·
                      refine ⟨3902542833284907014059937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41627123555039008149972661 3902542833284907014059937)
                      ·
                        rfl

theorem cell23_7600175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_7600175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600175 prefixEnd_7600175 := by exact prefixLift 7600175
  have htrace : WordTrace (prefixWord ++ tailWord_7600175) baseStart_7600175 baseEnd_7600175 := by
    simpa [prefixWord, tailWord_7600175, baseEnd_7600175] using wordTrace_append hprefix tailTrace_7600175
  have hstable : (prefixWord ++ tailWord_7600175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600175).length < 2 ^ (prefixWord ++ tailWord_7600175).sum := by decide
  have hdescent : baseEnd_7600175 < baseStart_7600175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600236 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_7600236 : Nat := 118140960795 + 7600236 * 2 ^ 59
def prefixEnd_7600236 : Nat := 4983230072969 + 3 ^ 40 * 7600236 * 2
def baseEnd_7600236 : Nat := 3902574155604831275397157

theorem tailTrace_7600236 : CollatzResearch.WordTrace tailWord_7600236 prefixEnd_7600236 3902574155604831275397157 := by
  unfold tailWord_7600236
  simp only [CollatzResearch.WordTrace]
  refine ⟨138601690046825231906750281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184802253395766975875667041 138601690046825231906750281)
  ·
    refine ⟨103951267535118923930062711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138601690046825231906750281 103951267535118923930062711)
    ·
      refine ⟨155926901302678385895094067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103951267535118923930062711 155926901302678385895094067)
      ·
        refine ⟨233890351954017578842641101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155926901302678385895094067 233890351954017578842641101)
        ·
          refine ⟨87708881982756592065990413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233890351954017578842641101 87708881982756592065990413)
          ·
            refine ⟨32890830743533722024746405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87708881982756592065990413 32890830743533722024746405)
            ·
              refine ⟨6167030764412572879639951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32890830743533722024746405 6167030764412572879639951)
              ·
                refine ⟨9250546146618859319459927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167030764412572879639951 9250546146618859319459927)
                ·
                  refine ⟨13875819219928288979189891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250546146618859319459927 13875819219928288979189891)
                  ·
                    refine ⟨20813728829892433468784837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13875819219928288979189891 20813728829892433468784837)
                    ·
                      refine ⟨3902574155604831275397157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20813728829892433468784837 3902574155604831275397157)
                      ·
                        rfl

theorem cell23_7600236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_7600236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600236 prefixEnd_7600236 := by exact prefixLift 7600236
  have htrace : WordTrace (prefixWord ++ tailWord_7600236) baseStart_7600236 baseEnd_7600236 := by
    simpa [prefixWord, tailWord_7600236, baseEnd_7600236] using wordTrace_append hprefix tailTrace_7600236
  have hstable : (prefixWord ++ tailWord_7600236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600236).length < 2 ^ (prefixWord ++ tailWord_7600236).sum := by decide
  have hdescent : baseEnd_7600236 < baseStart_7600236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600242 : List Nat := [3, 2, 1, 2, 2, 3, 10]
def baseStart_7600242 : Nat := 118140960795 + 7600242 * 2 ^ 59
def prefixEnd_7600242 : Nat := 4983230072969 + 3 ^ 40 * 7600242 * 2
def baseEnd_7600242 : Nat := 48179965882577262369409

theorem tailTrace_7600242 : CollatzResearch.WordTrace tailWord_7600242 prefixEnd_7600242 48179965882577262369409 := by
  unfold tailWord_7600242
  simp only [CollatzResearch.WordTrace]
  refine ⟨69300899732907181709554745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184802399287752484558812653 69300899732907181709554745)
  ·
    refine ⟨51975674799680386282166059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69300899732907181709554745 51975674799680386282166059)
    ·
      refine ⟨77963512199520579423249089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51975674799680386282166059 77963512199520579423249089)
      ·
        refine ⟨58472634149640434567436817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77963512199520579423249089 58472634149640434567436817)
        ·
          refine ⟨43854475612230325925577613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58472634149640434567436817 43854475612230325925577613)
          ·
            refine ⟨16445428354586372222091605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43854475612230325925577613 16445428354586372222091605)
            ·
              refine ⟨48179965882577262369409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16445428354586372222091605 48179965882577262369409)
              ·
                rfl

theorem cell23_7600242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 10].length) (baseStart_7600242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600242 prefixEnd_7600242 := by exact prefixLift 7600242
  have htrace : WordTrace (prefixWord ++ tailWord_7600242) baseStart_7600242 baseEnd_7600242 := by
    simpa [prefixWord, tailWord_7600242, baseEnd_7600242] using wordTrace_append hprefix tailTrace_7600242
  have hstable : (prefixWord ++ tailWord_7600242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600242).length < 2 ^ (prefixWord ++ tailWord_7600242).sum := by decide
  have hdescent : baseEnd_7600242 < baseStart_7600242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600246 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_7600246 : Nat := 118140960795 + 7600246 * 2 ^ 59
def prefixEnd_7600246 : Nat := 4983230072969 + 3 ^ 40 * 7600246 * 2
def baseEnd_7600246 : Nat := 1300859763470458745424037

theorem tailTrace_7600246 : CollatzResearch.WordTrace tailWord_7600246 prefixEnd_7600246 1300859763470458745424037 := by
  unfold tailWord_7600246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325234051475889720085287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184802496549076157014243061 17325234051475889720085287)
  ·
    refine ⟨25987851077213834580127931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325234051475889720085287 25987851077213834580127931)
    ·
      refine ⟨38981776615820751870191897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25987851077213834580127931 38981776615820751870191897)
      ·
        refine ⟨29236332461865563902643923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38981776615820751870191897 29236332461865563902643923)
        ·
          refine ⟨43854498692798345853965885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29236332461865563902643923 43854498692798345853965885)
          ·
            refine ⟨16445437009799379695237207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43854498692798345853965885 16445437009799379695237207)
            ·
              refine ⟨24668155514699069542855811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16445437009799379695237207 24668155514699069542855811)
              ·
                refine ⟨37002233272048604314283717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24668155514699069542855811 37002233272048604314283717)
                ·
                  refine ⟨6937918738509113308928197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37002233272048604314283717 6937918738509113308928197)
                  ·
                    refine ⟨1300859763470458745424037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6937918738509113308928197 1300859763470458745424037)
                    ·
                      rfl

theorem cell23_7600246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_7600246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600246 prefixEnd_7600246 := by exact prefixLift 7600246
  have htrace : WordTrace (prefixWord ++ tailWord_7600246) baseStart_7600246 baseEnd_7600246 := by
    simpa [prefixWord, tailWord_7600246, baseEnd_7600246] using wordTrace_append hprefix tailTrace_7600246
  have hstable : (prefixWord ++ tailWord_7600246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600246).length < 2 ^ (prefixWord ++ tailWord_7600246).sum := by decide
  have hdescent : baseEnd_7600246 < baseStart_7600246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600253 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_7600253 : Nat := 118140960795 + 7600253 * 2 ^ 59
def prefixEnd_7600253 : Nat := 4983230072969 + 3 ^ 40 * 7600253 * 2
def baseEnd_7600253 : Nat := 3902582884775957708884579

theorem tailTrace_7600253 : CollatzResearch.WordTrace tailWord_7600253 prefixEnd_7600253 3902582884775957708884579 := by
  unfold tailWord_7600253
  simp only [CollatzResearch.WordTrace]
  refine ⟨277204000134588875716869413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184802666756392583811246275 277204000134588875716869413)
  ·
    refine ⟨51975750025235414196913015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277204000134588875716869413 51975750025235414196913015)
    ·
      refine ⟨77963625037853121295369523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51975750025235414196913015 77963625037853121295369523)
      ·
        refine ⟨116945437556779681943054285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77963625037853121295369523 116945437556779681943054285)
        ·
          refine ⟨43854539083792380728645357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116945437556779681943054285 43854539083792380728645357)
          ·
            refine ⟨16445452156422142773242009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43854539083792380728645357 16445452156422142773242009)
            ·
              refine ⟨12334089117316607079931507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445452156422142773242009 12334089117316607079931507)
              ·
                refine ⟨18501133675974910619897261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12334089117316607079931507 18501133675974910619897261)
                ·
                  refine ⟨6937925128490591482461473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18501133675974910619897261 6937925128490591482461473)
                  ·
                    refine ⟨5203443846367943611846105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937925128490591482461473 5203443846367943611846105)
                    ·
                      refine ⟨3902582884775957708884579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203443846367943611846105 3902582884775957708884579)
                      ·
                        rfl

theorem cell23_7600253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_7600253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600253 prefixEnd_7600253 := by exact prefixLift 7600253
  have htrace : WordTrace (prefixWord ++ tailWord_7600253) baseStart_7600253 baseEnd_7600253 := by
    simpa [prefixWord, tailWord_7600253, baseEnd_7600253] using wordTrace_append hprefix tailTrace_7600253
  have hstable : (prefixWord ++ tailWord_7600253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600253).length < 2 ^ (prefixWord ++ tailWord_7600253).sum := by decide
  have hdescent : baseEnd_7600253 < baseStart_7600253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600266 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_7600266 : Nat := 118140960795 + 7600266 * 2 ^ 59
def prefixEnd_7600266 : Nat := 4983230072969 + 3 ^ 40 * 7600266 * 2
def baseEnd_7600266 : Nat := 3902589560024466158022019

theorem tailTrace_7600266 : CollatzResearch.WordTrace tailWord_7600266 prefixEnd_7600266 3902589560024466158022019 := by
  unfold tailWord_7600266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69301118570885444734273163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184802982855694519291395101 69301118570885444734273163)
  ·
    refine ⟨103951677856328167101409745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69301118570885444734273163 103951677856328167101409745)
    ·
      refine ⟨77963758392246125326057309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103951677856328167101409745 77963758392246125326057309)
      ·
        refine ⟨29236409397092296997271491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77963758392246125326057309 29236409397092296997271491)
        ·
          refine ⟨43854614095638445495907237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29236409397092296997271491 43854614095638445495907237)
          ·
            refine ⟨8222740142932208530482607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43854614095638445495907237 8222740142932208530482607)
            ·
              refine ⟨12334110214398312795723911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222740142932208530482607 12334110214398312795723911)
              ·
                refine ⟨18501165321597469193585867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12334110214398312795723911 18501165321597469193585867)
                ·
                  refine ⟨27751747982396203790378801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18501165321597469193585867 27751747982396203790378801)
                  ·
                    refine ⟨20813810986797152842784101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27751747982396203790378801 20813810986797152842784101)
                    ·
                      refine ⟨3902589560024466158022019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20813810986797152842784101 3902589560024466158022019)
                      ·
                        rfl

theorem cell23_7600266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_7600266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600266 prefixEnd_7600266 := by exact prefixLift 7600266
  have htrace : WordTrace (prefixWord ++ tailWord_7600266) baseStart_7600266 baseEnd_7600266 := by
    simpa [prefixWord, tailWord_7600266, baseEnd_7600266] using wordTrace_append hprefix tailTrace_7600266
  have hstable : (prefixWord ++ tailWord_7600266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600266).length < 2 ^ (prefixWord ++ tailWord_7600266).sum := by decide
  have hdescent : baseEnd_7600266 < baseStart_7600266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600276 : List Nat := [2, 4, 2, 3, 1, 1, 1, 9]
def baseStart_7600276 : Nat := 118140960795 + 7600276 * 2 ^ 59
def prefixEnd_7600276 : Nat := 4983230072969 + 3 ^ 40 * 7600276 * 2
def baseEnd_7600276 : Nat := 144540544253000411810999

theorem tailTrace_7600276 : CollatzResearch.WordTrace tailWord_7600276 prefixEnd_7600276 144540544253000411810999 := by
  unfold tailWord_7600276
  simp only [CollatzResearch.WordTrace]
  refine ⟨138602419506752775322478341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184803226009003700429971121 138602419506752775322478341)
  ·
    refine ⟨25987953657516145372964689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138602419506752775322478341 25987953657516145372964689)
    ·
      refine ⟨19490965243137109029723517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25987953657516145372964689 19490965243137109029723517)
      ·
        refine ⟨7309111966176415886146319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19490965243137109029723517 7309111966176415886146319)
        ·
          refine ⟨10963667949264623829219479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309111966176415886146319 10963667949264623829219479)
          ·
            refine ⟨16445501923896935743829219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963667949264623829219479 16445501923896935743829219)
            ·
              refine ⟨24668252885845403615743829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16445501923896935743829219 24668252885845403615743829)
              ·
                refine ⟨144540544253000411810999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24668252885845403615743829 144540544253000411810999)
                ·
                  rfl

theorem cell23_7600276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 9].length) (baseStart_7600276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600276 prefixEnd_7600276 := by exact prefixLift 7600276
  have htrace : WordTrace (prefixWord ++ tailWord_7600276) baseStart_7600276 baseEnd_7600276 := by
    simpa [prefixWord, tailWord_7600276, baseEnd_7600276] using wordTrace_append hprefix tailTrace_7600276
  have hstable : (prefixWord ++ tailWord_7600276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600276).length < 2 ^ (prefixWord ++ tailWord_7600276).sum := by decide
  have hdescent : baseEnd_7600276 < baseStart_7600276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600287 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7600287 : Nat := 118140960795 + 7600287 * 2 ^ 59
def prefixEnd_7600287 : Nat := 4983230072969 + 3 ^ 40 * 7600287 * 2
def baseEnd_7600287 : Nat := 3902600343118210575859423

theorem tailTrace_7600287 : CollatzResearch.WordTrace tailWord_7600287 prefixEnd_7600287 3902600343118210575859423 := by
  unfold tailWord_7600287
  simp only [CollatzResearch.WordTrace]
  refine ⟨277205240216465699523607115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184803493477643799682404743 277205240216465699523607115)
  ·
    refine ⟨415807860324698549285410673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277205240216465699523607115 415807860324698549285410673)
    ·
      refine ⟨311855895243523911964058005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415807860324698549285410673 311855895243523911964058005)
      ·
        refine ⟨14618245089540183373315219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 311855895243523911964058005 14618245089540183373315219)
        ·
          refine ⟨21927367634310275059972829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14618245089540183373315219 21927367634310275059972829)
          ·
            refine ⟨8222762862866353147489811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21927367634310275059972829 8222762862866353147489811)
            ·
              refine ⟨12334144294299529721234717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222762862866353147489811 12334144294299529721234717)
              ·
                refine ⟨4625304110362323645463019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12334144294299529721234717 4625304110362323645463019)
                ·
                  refine ⟨6937956165543485468194529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625304110362323645463019 6937956165543485468194529)
                  ·
                    refine ⟨5203467124157614101145897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937956165543485468194529 5203467124157614101145897)
                    ·
                      refine ⟨3902600343118210575859423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203467124157614101145897 3902600343118210575859423)
                      ·
                        rfl

theorem cell23_7600287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7600287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600287 prefixEnd_7600287 := by exact prefixLift 7600287
  have htrace : WordTrace (prefixWord ++ tailWord_7600287) baseStart_7600287 baseEnd_7600287 := by
    simpa [prefixWord, tailWord_7600287, baseEnd_7600287] using wordTrace_append hprefix tailTrace_7600287
  have hstable : (prefixWord ++ tailWord_7600287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600287).length < 2 ^ (prefixWord ++ tailWord_7600287).sum := by decide
  have hdescent : baseEnd_7600287 < baseStart_7600287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600312 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_7600312 : Nat := 118140960795 + 7600312 * 2 ^ 59
def prefixEnd_7600312 : Nat := 4983230072969 + 3 ^ 40 * 7600312 * 2
def baseEnd_7600312 : Nat := 3902613180134572978046807

theorem tailTrace_7600312 : CollatzResearch.WordTrace tailWord_7600312 prefixEnd_7600312 3902613180134572978046807 := by
  unfold tailWord_7600312
  simp only [CollatzResearch.WordTrace]
  refine ⟨138603076020687564396633595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184804101360916752528844793 138603076020687564396633595)
  ·
    refine ⟨207904614031031346594950393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138603076020687564396633595 207904614031031346594950393)
    ·
      refine ⟨155928460523273509946212795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207904614031031346594950393 155928460523273509946212795)
      ·
        refine ⟨233892690784910264919319193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155928460523273509946212795 233892690784910264919319193)
        ·
          refine ⟨175419518088682698689489395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233892690784910264919319193 175419518088682698689489395)
          ·
            refine ⟨263129277133024048034234093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175419518088682698689489395 263129277133024048034234093)
            ·
              refine ⟨98673478924884018012837785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263129277133024048034234093 98673478924884018012837785)
              ·
                refine ⟨74005109193663013509628339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98673478924884018012837785 74005109193663013509628339)
                ·
                  refine ⟨111007663790494520264442509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74005109193663013509628339 111007663790494520264442509)
                  ·
                    refine ⟨41627873921435445099165941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111007663790494520264442509 41627873921435445099165941)
                    ·
                      refine ⟨3902613180134572978046807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41627873921435445099165941 3902613180134572978046807)
                      ·
                        rfl

theorem cell23_7600312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_7600312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600312 prefixEnd_7600312 := by exact prefixLift 7600312
  have htrace : WordTrace (prefixWord ++ tailWord_7600312) baseStart_7600312 baseEnd_7600312 := by
    simpa [prefixWord, tailWord_7600312, baseEnd_7600312] using wordTrace_append hprefix tailTrace_7600312
  have hstable : (prefixWord ++ tailWord_7600312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600312).length < 2 ^ (prefixWord ++ tailWord_7600312).sum := by decide
  have hdescent : baseEnd_7600312 < baseStart_7600312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600320 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3]
def baseStart_7600320 : Nat := 118140960795 + 7600320 * 2 ^ 59
def prefixEnd_7600320 : Nat := 4983230072969 + 3 ^ 40 * 7600320 * 2
def baseEnd_7600320 : Nat := 3902617287979808946746771

theorem tailTrace_7600320 : CollatzResearch.WordTrace tailWord_7600320 prefixEnd_7600320 3902617287979808946746771 := by
  unfold tailWord_7600320
  simp only [CollatzResearch.WordTrace]
  refine ⟨138603221912673073079779207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184804295883564097439705609 138603221912673073079779207)
  ·
    refine ⟨207904832869009609619668811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138603221912673073079779207 207904832869009609619668811)
    ·
      refine ⟨311857249303514414429503217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207904832869009609619668811 311857249303514414429503217)
      ·
        refine ⟨233892936977635810822127413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311857249303514414429503217 233892936977635810822127413)
        ·
          refine ⟨21927462841653357264574445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233892936977635810822127413 21927462841653357264574445)
          ·
            refine ⟨8222798565620008974215417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21927462841653357264574445 8222798565620008974215417)
            ·
              refine ⟨6167098924215006730661563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222798565620008974215417 6167098924215006730661563)
              ·
                refine ⟨9250648386322510095992345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167098924215006730661563 9250648386322510095992345)
                ·
                  refine ⟨6937986289741882571994259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250648386322510095992345 6937986289741882571994259)
                  ·
                    refine ⟨10406979434612823857991389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937986289741882571994259 10406979434612823857991389)
                    ·
                      refine ⟨3902617287979808946746771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10406979434612823857991389 3902617287979808946746771)
                      ·
                        rfl

theorem cell23_7600320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_7600320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600320 prefixEnd_7600320 := by exact prefixLift 7600320
  have htrace : WordTrace (prefixWord ++ tailWord_7600320) baseStart_7600320 baseEnd_7600320 := by
    simpa [prefixWord, tailWord_7600320, baseEnd_7600320] using wordTrace_append hprefix tailTrace_7600320
  have hstable : (prefixWord ++ tailWord_7600320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600320).length < 2 ^ (prefixWord ++ tailWord_7600320).sum := by decide
  have hdescent : baseEnd_7600320 < baseStart_7600320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600354 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7600354 : Nat := 118140960795 + 7600354 * 2 ^ 59
def prefixEnd_7600354 : Nat := 4983230072969 + 3 ^ 40 * 7600354 * 2
def baseEnd_7600354 : Nat := 3902634746322061813721615

theorem tailTrace_7600354 : CollatzResearch.WordTrace tailWord_7600354 prefixEnd_7600354 3902634746322061813721615 := by
  unfold tailWord_7600354
  simp only [CollatzResearch.WordTrace]
  refine ⟨69301920976805742491574029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184805122604815313310864077 69301920976805742491574029)
  ·
    refine ⟨25988220366302153434340261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69301920976805742491574029 25988220366302153434340261)
    ·
      refine ⟨4872791318681653768938799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25988220366302153434340261 4872791318681653768938799)
      ·
        refine ⟨7309186978022480653408199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872791318681653768938799 7309186978022480653408199)
        ·
          refine ⟨10963780467033720980112299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309186978022480653408199 10963780467033720980112299)
          ·
            refine ⟨16445670700550581470168449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963780467033720980112299 16445670700550581470168449)
            ·
              refine ⟨12334253025412936102626337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445670700550581470168449 12334253025412936102626337)
              ·
                refine ⟨9250689769059702076969753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12334253025412936102626337 9250689769059702076969753)
                ·
                  refine ⟨6938017326794776557727315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250689769059702076969753 6938017326794776557727315)
                  ·
                    refine ⟨10407025990192164836590973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938017326794776557727315 10407025990192164836590973)
                    ·
                      refine ⟨3902634746322061813721615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10407025990192164836590973 3902634746322061813721615)
                      ·
                        rfl

theorem cell23_7600354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7600354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600354 prefixEnd_7600354 := by exact prefixLift 7600354
  have htrace : WordTrace (prefixWord ++ tailWord_7600354) baseStart_7600354 baseEnd_7600354 := by
    simpa [prefixWord, tailWord_7600354, baseEnd_7600354] using wordTrace_append hprefix tailTrace_7600354
  have hstable : (prefixWord ++ tailWord_7600354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600354).length < 2 ^ (prefixWord ++ tailWord_7600354).sum := by decide
  have hdescent : baseEnd_7600354 < baseStart_7600354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600360 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7600360 : Nat := 118140960795 + 7600360 * 2 ^ 59
def prefixEnd_7600360 : Nat := 4983230072969 + 3 ^ 40 * 7600360 * 2
def baseEnd_7600360 : Nat := 3902637827205988790246587

theorem tailTrace_7600360 : CollatzResearch.WordTrace tailWord_7600360 prefixEnd_7600360 3902637827205988790246587 := by
  unfold tailWord_7600360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138603951372600616495507267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184805268496800821994009689 138603951372600616495507267)
  ·
    refine ⟨207905927058900924743260901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138603951372600616495507267 207905927058900924743260901)
    ·
      refine ⟨38982361323543923389361419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207905927058900924743260901 38982361323543923389361419)
      ·
        refine ⟨58473541985315885084042129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38982361323543923389361419 58473541985315885084042129)
        ·
          refine ⟨43855156488986913813031597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58473541985315885084042129 43855156488986913813031597)
          ·
            refine ⟨16445683683370092679886849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43855156488986913813031597 16445683683370092679886849)
            ·
              refine ⟨12334262762527569509915137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445683683370092679886849 12334262762527569509915137)
              ·
                refine ⟨9250697071895677132436353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12334262762527569509915137 9250697071895677132436353)
                ·
                  refine ⟨6938022803921757849327265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250697071895677132436353 6938022803921757849327265)
                  ·
                    refine ⟨5203517102941318386995449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6938022803921757849327265 5203517102941318386995449)
                    ·
                      refine ⟨3902637827205988790246587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203517102941318386995449 3902637827205988790246587)
                      ·
                        rfl

theorem cell23_7600360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7600360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600360 prefixEnd_7600360 := by exact prefixLift 7600360
  have htrace : WordTrace (prefixWord ++ tailWord_7600360) baseStart_7600360 baseEnd_7600360 := by
    simpa [prefixWord, tailWord_7600360, baseEnd_7600360] using wordTrace_append hprefix tailTrace_7600360
  have hstable : (prefixWord ++ tailWord_7600360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600360).length < 2 ^ (prefixWord ++ tailWord_7600360).sum := by decide
  have hdescent : baseEnd_7600360 < baseStart_7600360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600439 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 6]
def baseStart_7600439 : Nat := 118140960795 + 7600439 * 2 ^ 59
def prefixEnd_7600439 : Nat := 4983230072969 + 3 ^ 40 * 7600439 * 2
def baseEnd_7600439 : Nat := 433630932464188220128747

theorem tailTrace_7600439 : CollatzResearch.WordTrace tailWord_7600439 prefixEnd_7600439 433630932464188220128747 := by
  unfold tailWord_7600439
  simp only [CollatzResearch.WordTrace]
  refine ⟨277210784111915029483140371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184807189407943352988760247 277210784111915029483140371)
  ·
    refine ⟨415816176167872544224710557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277210784111915029483140371 415816176167872544224710557)
    ·
      refine ⟨155931066062952204084266459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415816176167872544224710557 155931066062952204084266459)
      ·
        refine ⟨233896599094428306126399689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155931066062952204084266459 233896599094428306126399689)
        ·
          refine ⟨175422449320821229594799767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233896599094428306126399689 175422449320821229594799767)
          ·
            refine ⟨263133673981231844392199651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175422449320821229594799767 263133673981231844392199651)
            ·
              refine ⟨394700510971847766588299477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263133673981231844392199651 394700510971847766588299477)
              ·
                refine ⟨9250793225902682029413269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 394700510971847766588299477 9250793225902682029413269)
                ·
                  refine ⟨433630932464188220128747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9250793225902682029413269 433630932464188220128747)
                  ·
                    rfl

theorem cell23_7600439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 6].length) (baseStart_7600439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600439 prefixEnd_7600439 := by exact prefixLift 7600439
  have htrace : WordTrace (prefixWord ++ tailWord_7600439) baseStart_7600439 baseEnd_7600439 := by
    simpa [prefixWord, tailWord_7600439, baseEnd_7600439] using wordTrace_append hprefix tailTrace_7600439
  have hstable : (prefixWord ++ tailWord_7600439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600439).length < 2 ^ (prefixWord ++ tailWord_7600439).sum := by decide
  have hdescent : baseEnd_7600439 < baseStart_7600439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600490 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_7600490 : Nat := 118140960795 + 7600490 * 2 ^ 59
def prefixEnd_7600490 : Nat := 4983230072969 + 3 ^ 40 * 7600490 * 2
def baseEnd_7600490 : Nat := 433633842187897031291221

theorem tailTrace_7600490 : CollatzResearch.WordTrace tailWord_7600490 prefixEnd_7600490 433633842187897031291221 := by
  unfold tailWord_7600490
  simp only [CollatzResearch.WordTrace]
  refine ⟨69303161058682566298311731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184808429489820176795497949 69303161058682566298311731)
  ·
    refine ⟨103954741588023849447467597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69303161058682566298311731 103954741588023849447467597)
    ·
      refine ⟨38983028095508943542800349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103954741588023849447467597 38983028095508943542800349)
      ·
        refine ⟨14618635535815853828550131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38983028095508943542800349 14618635535815853828550131)
        ·
          refine ⟨21927953303723780742825197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14618635535815853828550131 21927953303723780742825197)
          ·
            refine ⟨8222982488896417778559449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21927953303723780742825197 8222982488896417778559449)
            ·
              refine ⟨6167236866672313333919587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222982488896417778559449 6167236866672313333919587)
              ·
                refine ⟨9250855300008470000879381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167236866672313333919587 9250855300008470000879381)
                ·
                  refine ⟨433633842187897031291221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9250855300008470000879381 433633842187897031291221)
                  ·
                    rfl

theorem cell23_7600490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_7600490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600490 prefixEnd_7600490 := by exact prefixLift 7600490
  have htrace : WordTrace (prefixWord ++ tailWord_7600490) baseStart_7600490 baseEnd_7600490 := by
    simpa [prefixWord, tailWord_7600490, baseEnd_7600490] using wordTrace_append hprefix tailTrace_7600490
  have hstable : (prefixWord ++ tailWord_7600490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600490).length < 2 ^ (prefixWord ++ tailWord_7600490).sum := by decide
  have hdescent : baseEnd_7600490 < baseStart_7600490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600493 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7600493 : Nat := 118140960795 + 7600493 * 2 ^ 59
def prefixEnd_7600493 : Nat := 4983230072969 + 3 ^ 40 * 7600493 * 2
def baseEnd_7600493 : Nat := 3902706120133036769883475

theorem tailTrace_7600493 : CollatzResearch.WordTrace tailWord_7600493 prefixEnd_7600493 3902706120133036769883475 := by
  unfold tailWord_7600493
  simp only [CollatzResearch.WordTrace]
  refine ⟨277212753653719396705606133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184808502435812931137070755 277212753653719396705606133)
  ·
    refine ⟨25988695655036193441150575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277212753653719396705606133 25988695655036193441150575)
    ·
      refine ⟨38983043482554290161725863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988695655036193441150575 38983043482554290161725863)
      ·
        refine ⟨58474565223831435242588795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38983043482554290161725863 58474565223831435242588795)
        ·
          refine ⟨87711847835747152863883193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58474565223831435242588795 87711847835747152863883193)
          ·
            refine ⟨65783885876810364647912395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87711847835747152863883193 65783885876810364647912395)
            ·
              refine ⟨98675828815215546971868593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65783885876810364647912395 98675828815215546971868593)
              ·
                refine ⟨74006871611411660228901445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98675828815215546971868593 74006871611411660228901445)
                ·
                  refine ⟨13876288427139686292919021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74006871611411660228901445 13876288427139686292919021)
                  ·
                    refine ⟨5203608160177382359844633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13876288427139686292919021 5203608160177382359844633)
                    ·
                      refine ⟨3902706120133036769883475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203608160177382359844633 3902706120133036769883475)
                      ·
                        rfl

theorem cell23_7600493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7600493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600493 prefixEnd_7600493 := by exact prefixLift 7600493
  have htrace : WordTrace (prefixWord ++ tailWord_7600493) baseStart_7600493 baseEnd_7600493 := by
    simpa [prefixWord, tailWord_7600493, baseEnd_7600493] using wordTrace_append hprefix tailTrace_7600493
  have hstable : (prefixWord ++ tailWord_7600493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600493).length < 2 ^ (prefixWord ++ tailWord_7600493).sum := by decide
  have hdescent : baseEnd_7600493 < baseStart_7600493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600516 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_7600516 : Nat := 118140960795 + 7600516 * 2 ^ 59
def prefixEnd_7600516 : Nat := 4983230072969 + 3 ^ 40 * 7600516 * 2
def baseEnd_7600516 : Nat := 1300905976729363393298623

theorem tailTrace_7600516 : CollatzResearch.WordTrace tailWord_7600516 prefixEnd_7600516 1300905976729363393298623 := by
  unfold tailWord_7600516
  simp only [CollatzResearch.WordTrace]
  refine ⟨138606796266318035816846701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184809061688424047755795601 138606796266318035816846701)
  ·
    refine ⟨51977548599869263431317513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138606796266318035816846701 51977548599869263431317513)
    ·
      refine ⟨38983161449901947573488135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51977548599869263431317513 38983161449901947573488135)
      ·
        refine ⟨58474742174852921360232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38983161449901947573488135 58474742174852921360232203)
        ·
          refine ⟨87712113262279382040348305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58474742174852921360232203 87712113262279382040348305)
          ·
            refine ⟨65784084946709536530261229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87712113262279382040348305 65784084946709536530261229)
            ·
              refine ⟨24669031855016076198847961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65784084946709536530261229 24669031855016076198847961)
              ·
                refine ⟨18501773891262057149135971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24669031855016076198847961 18501773891262057149135971)
                ·
                  refine ⟨27752660836893085723703957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18501773891262057149135971 27752660836893085723703957)
                  ·
                    refine ⟨1300905976729363393298623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27752660836893085723703957 1300905976729363393298623)
                    ·
                      rfl

theorem cell23_7600516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_7600516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600516 prefixEnd_7600516 := by exact prefixLift 7600516
  have htrace : WordTrace (prefixWord ++ tailWord_7600516) baseStart_7600516 baseEnd_7600516 := by
    simpa [prefixWord, tailWord_7600516, baseEnd_7600516] using wordTrace_append hprefix tailTrace_7600516
  have hstable : (prefixWord ++ tailWord_7600516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600516).length < 2 ^ (prefixWord ++ tailWord_7600516).sum := by decide
  have hdescent : baseEnd_7600516 < baseStart_7600516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600573 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_7600573 : Nat := 118140960795 + 7600573 * 2 ^ 59
def prefixEnd_7600573 : Nat := 4983230072969 + 3 ^ 40 * 7600573 * 2
def baseEnd_7600573 : Nat := 3902747198585396456883107

theorem tailTrace_7600573 : CollatzResearch.WordTrace tailWord_7600573 prefixEnd_7600573 3902747198585396456883107 := by
  unfold tailWord_7600573
  simp only [CollatzResearch.WordTrace]
  refine ⟨277215671493429570368518373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184810447662286380245678915 277215671493429570368518373)
  ·
    refine ⟨51977938405018044444097195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277215671493429570368518373 51977938405018044444097195)
    ·
      refine ⟨77966907607527066666145793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51977938405018044444097195 77966907607527066666145793)
      ·
        refine ⟨58475180705645299999609345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77966907607527066666145793 58475180705645299999609345)
        ·
          refine ⟨43856385529233974999707009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58475180705645299999609345 43856385529233974999707009)
          ·
            refine ⟨32892289146925481249780257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43856385529233974999707009 32892289146925481249780257)
            ·
              refine ⟨24669216860194110937335193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32892289146925481249780257 24669216860194110937335193)
              ·
                refine ⟨18501912645145583203001395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24669216860194110937335193 18501912645145583203001395)
                ·
                  refine ⟨27752868967718374804502093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18501912645145583203001395 27752868967718374804502093)
                  ·
                    refine ⟨10407325862894390551688285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27752868967718374804502093 10407325862894390551688285)
                    ·
                      refine ⟨3902747198585396456883107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10407325862894390551688285 3902747198585396456883107)
                      ·
                        rfl

theorem cell23_7600573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_7600573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600573 prefixEnd_7600573 := by exact prefixLift 7600573
  have htrace : WordTrace (prefixWord ++ tailWord_7600573) baseStart_7600573 baseEnd_7600573 := by
    simpa [prefixWord, tailWord_7600573, baseEnd_7600573] using wordTrace_append hprefix tailTrace_7600573
  have hstable : (prefixWord ++ tailWord_7600573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600573).length < 2 ^ (prefixWord ++ tailWord_7600573).sum := by decide
  have hdescent : baseEnd_7600573 < baseStart_7600573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600607 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 2, 1, 3]
def baseStart_7600607 : Nat := 118140960795 + 7600607 * 2 ^ 59
def prefixEnd_7600607 : Nat := 4983230072969 + 3 ^ 40 * 7600607 * 2
def baseEnd_7600607 : Nat := 3902764656927649323857951

theorem tailTrace_7600607 : CollatzResearch.WordTrace tailWord_7600607 prefixEnd_7600607 3902764656927649323857951 := by
  unfold tailWord_7600607
  simp only [CollatzResearch.WordTrace]
  refine ⟨277216911575306394175256075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184811274383537596116837383 277216911575306394175256075)
  ·
    refine ⟨415825367362959591262884113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277216911575306394175256075 415825367362959591262884113)
    ·
      refine ⟨311869025522219693447163085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415825367362959591262884113 311869025522219693447163085)
      ·
        refine ⟨116950884570832385042686157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311869025522219693447163085 116950884570832385042686157)
        ·
          refine ⟨43856581714062144391007309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116950884570832385042686157 43856581714062144391007309)
          ·
            refine ⟨16446218142773304146627741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43856581714062144391007309 16446218142773304146627741)
            ·
              refine ⟨6167331803539989054985403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16446218142773304146627741 6167331803539989054985403)
              ·
                refine ⟨9250997705309983582478105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167331803539989054985403 9250997705309983582478105)
                ·
                  refine ⟨6938248278982487686858579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250997705309983582478105 6938248278982487686858579)
                  ·
                    refine ⟨10407372418473731530287869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938248278982487686858579 10407372418473731530287869)
                    ·
                      refine ⟨3902764656927649323857951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10407372418473731530287869 3902764656927649323857951)
                      ·
                        rfl

theorem cell23_7600607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_7600607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600607 prefixEnd_7600607 := by exact prefixLift 7600607
  have htrace : WordTrace (prefixWord ++ tailWord_7600607) baseStart_7600607 baseEnd_7600607 := by
    simpa [prefixWord, tailWord_7600607, baseEnd_7600607] using wordTrace_append hprefix tailTrace_7600607
  have hstable : (prefixWord ++ tailWord_7600607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600607).length < 2 ^ (prefixWord ++ tailWord_7600607).sum := by decide
  have hdescent : baseEnd_7600607 < baseStart_7600607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600630 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7600630 : Nat := 118140960795 + 7600630 * 2 ^ 59
def prefixEnd_7600630 : Nat := 4983230072969 + 3 ^ 40 * 7600630 * 2
def baseEnd_7600630 : Nat := 3902776466982702733870345

theorem tailTrace_7600630 : CollatzResearch.WordTrace tailWord_7600630 prefixEnd_7600630 3902776466982702733870345 := by
  unfold tailWord_7600630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326109403388941818958959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184811833636148712735562229 17326109403388941818958959)
  ·
    refine ⟨25989164105083412728438439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17326109403388941818958959 25989164105083412728438439)
    ·
      refine ⟨38983746157625119092657659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25989164105083412728438439 38983746157625119092657659)
      ·
        refine ⟨58475619236437678638986489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38983746157625119092657659 58475619236437678638986489)
        ·
          refine ⟨43856714427328258979239867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58475619236437678638986489 43856714427328258979239867)
          ·
            refine ⟨65785071640992388468859801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43856714427328258979239867 65785071640992388468859801)
            ·
              refine ⟨49338803730744291351644851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65785071640992388468859801 49338803730744291351644851)
              ·
                refine ⟨74008205596116437027467277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49338803730744291351644851 74008205596116437027467277)
                ·
                  refine ⟨27753077098543663885300229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74008205596116437027467277 27753077098543663885300229)
                  ·
                    refine ⟨5203701955976936978493793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27753077098543663885300229 5203701955976936978493793)
                    ·
                      refine ⟨3902776466982702733870345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203701955976936978493793 3902776466982702733870345)
                      ·
                        rfl

theorem cell23_7600630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7600630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600630 prefixEnd_7600630 := by exact prefixLift 7600630
  have htrace : WordTrace (prefixWord ++ tailWord_7600630) baseStart_7600630 baseEnd_7600630 := by
    simpa [prefixWord, tailWord_7600630, baseEnd_7600630] using wordTrace_append hprefix tailTrace_7600630
  have hstable : (prefixWord ++ tailWord_7600630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600630).length < 2 ^ (prefixWord ++ tailWord_7600630).sum := by decide
  have hdescent : baseEnd_7600630 < baseStart_7600630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600664 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_7600664 : Nat := 118140960795 + 7600664 * 2 ^ 59
def prefixEnd_7600664 : Nat := 4983230072969 + 3 ^ 40 * 7600664 * 2
def baseEnd_7600664 : Nat := 3902793925324955600845189

theorem tailTrace_7600664 : CollatzResearch.WordTrace tailWord_7600664 prefixEnd_7600664 3902793925324955600845189 := by
  unfold tailWord_7600664
  simp only [CollatzResearch.WordTrace]
  refine ⟨138609495268049946455040523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184812660357399928606720697 138609495268049946455040523)
  ·
    refine ⟨207914242902074919682560785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138609495268049946455040523 207914242902074919682560785)
    ·
      refine ⟨155935682176556189761920589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207914242902074919682560785 155935682176556189761920589)
      ·
        refine ⟨58475880816208571160720221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155935682176556189761920589 58475880816208571160720221)
        ·
          refine ⟨21928455306078214185270083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58475880816208571160720221 21928455306078214185270083)
          ·
            refine ⟨32892682959117321277905125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21928455306078214185270083 32892682959117321277905125)
            ·
              refine ⟨6167378054834497739607211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32892682959117321277905125 6167378054834497739607211)
              ·
                refine ⟨9251067082251746609410817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167378054834497739607211 9251067082251746609410817)
                ·
                  refine ⟨6938300311688809957058113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9251067082251746609410817 6938300311688809957058113)
                  ·
                    refine ⟨5203725233766607467793585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6938300311688809957058113 5203725233766607467793585)
                    ·
                      refine ⟨3902793925324955600845189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203725233766607467793585 3902793925324955600845189)
                      ·
                        rfl

theorem cell23_7600664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_7600664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600664 prefixEnd_7600664 := by exact prefixLift 7600664
  have htrace : WordTrace (prefixWord ++ tailWord_7600664) baseStart_7600664 baseEnd_7600664 := by
    simpa [prefixWord, tailWord_7600664, baseEnd_7600664] using wordTrace_append hprefix tailTrace_7600664
  have hstable : (prefixWord ++ tailWord_7600664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600664).length < 2 ^ (prefixWord ++ tailWord_7600664).sum := by decide
  have hdescent : baseEnd_7600664 < baseStart_7600664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600666 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_7600666 : Nat := 118140960795 + 7600666 * 2 ^ 59
def prefixEnd_7600666 : Nat := 4983230072969 + 3 ^ 40 * 7600666 * 2
def baseEnd_7600666 : Nat := 1300931650762088197673393

theorem tailTrace_7600666 : CollatzResearch.WordTrace tailWord_7600666 prefixEnd_7600666 1300931650762088197673393 := by
  unfold tailWord_7600666
  simp only [CollatzResearch.WordTrace]
  refine ⟨69304765870523161812913463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184812708988061764834435901 69304765870523161812913463)
  ·
    refine ⟨103957148805784742719370195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69304765870523161812913463 103957148805784742719370195)
    ·
      refine ⟨155935723208677114079055293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103957148805784742719370195 155935723208677114079055293)
      ·
        refine ⟨58475896203253917779645735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155935723208677114079055293 58475896203253917779645735)
        ·
          refine ⟨87713844304880876669468603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58475896203253917779645735 87713844304880876669468603)
          ·
            refine ⟨131570766457321315004202905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87713844304880876669468603 131570766457321315004202905)
            ·
              refine ⟨98678074842990986253152179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131570766457321315004202905 98678074842990986253152179)
              ·
                refine ⟨148017112264486479379728269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98678074842990986253152179 148017112264486479379728269)
                ·
                  refine ⟨55506417099182429767398101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148017112264486479379728269 55506417099182429767398101)
                  ·
                    refine ⟨1300931650762088197673393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55506417099182429767398101 1300931650762088197673393)
                    ·
                      rfl

theorem cell23_7600666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_7600666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600666 prefixEnd_7600666 := by exact prefixLift 7600666
  have htrace : WordTrace (prefixWord ++ tailWord_7600666) baseStart_7600666 baseEnd_7600666 := by
    simpa [prefixWord, tailWord_7600666, baseEnd_7600666] using wordTrace_append hprefix tailTrace_7600666
  have hstable : (prefixWord ++ tailWord_7600666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600666).length < 2 ^ (prefixWord ++ tailWord_7600666).sum := by decide
  have hdescent : baseEnd_7600666 < baseStart_7600666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600703 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_7600703 : Nat := 118140960795 + 7600703 * 2 ^ 59
def prefixEnd_7600703 : Nat := 4983230072969 + 3 ^ 40 * 7600703 * 2
def baseEnd_7600703 : Nat := 3902813951070480948257509

theorem tailTrace_7600703 : CollatzResearch.WordTrace tailWord_7600703 prefixEnd_7600703 3902813951070480948257509 := by
  unfold tailWord_7600703
  simp only [CollatzResearch.WordTrace]
  refine ⟨277220412982958602570750763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184813608655305735047167175 277220412982958602570750763)
  ·
    refine ⟨415830619474437903856126145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277220412982958602570750763 415830619474437903856126145)
    ·
      refine ⟨311872964605828427892094609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415830619474437903856126145 311872964605828427892094609)
      ·
        refine ⟨233904723454371320919070957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311872964605828427892094609 233904723454371320919070957)
        ·
          refine ⟨87714271295389245344651609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233904723454371320919070957 87714271295389245344651609)
          ·
            refine ⟨65785703471541934008488707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87714271295389245344651609 65785703471541934008488707)
            ·
              refine ⟨98678555207312901012733061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65785703471541934008488707 98678555207312901012733061)
              ·
                refine ⟨18502229101371168939887449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98678555207312901012733061 18502229101371168939887449)
                ·
                  refine ⟨13876671826028376704915587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18502229101371168939887449 13876671826028376704915587)
                  ·
                    refine ⟨20815007739042565057373381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13876671826028376704915587 20815007739042565057373381)
                    ·
                      refine ⟨3902813951070480948257509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20815007739042565057373381 3902813951070480948257509)
                      ·
                        rfl

theorem cell23_7600703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_7600703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600703 prefixEnd_7600703 := by exact prefixLift 7600703
  have htrace : WordTrace (prefixWord ++ tailWord_7600703) baseStart_7600703 baseEnd_7600703 := by
    simpa [prefixWord, tailWord_7600703, baseEnd_7600703] using wordTrace_append hprefix tailTrace_7600703
  have hstable : (prefixWord ++ tailWord_7600703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600703).length < 2 ^ (prefixWord ++ tailWord_7600703).sum := by decide
  have hdescent : baseEnd_7600703 < baseStart_7600703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600734 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7600734 : Nat := 118140960795 + 7600734 * 2 ^ 59
def prefixEnd_7600734 : Nat := 4983230072969 + 3 ^ 40 * 7600734 * 2
def baseEnd_7600734 : Nat := 1300943289656923442323289

theorem tailTrace_7600734 : CollatzResearch.WordTrace tailWord_7600734 prefixEnd_7600734 1300943289656923442323289 := by
  unfold tailWord_7600734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34652692955730786858141157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184814362430564196576752837 34652692955730786858141157)
  ·
    refine ⟨6497379929199522535901467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34652692955730786858141157 6497379929199522535901467)
    ·
      refine ⟨9746069893799283803852201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497379929199522535901467 9746069893799283803852201)
      ·
        refine ⟨7309552420349462852889151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9746069893799283803852201 7309552420349462852889151)
        ·
          refine ⟨10964328630524194279333727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309552420349462852889151 10964328630524194279333727)
          ·
            refine ⟨16446492945786291419000591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10964328630524194279333727 16446492945786291419000591)
            ·
              refine ⟨24669739418679437128500887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16446492945786291419000591 24669739418679437128500887)
              ·
                refine ⟨37004609128019155692751331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24669739418679437128500887 37004609128019155692751331)
                ·
                  refine ⟨55506913692028733539126997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37004609128019155692751331 55506913692028733539126997)
                  ·
                    refine ⟨1300943289656923442323289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55506913692028733539126997 1300943289656923442323289)
                    ·
                      rfl

theorem cell23_7600734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7600734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600734 prefixEnd_7600734 := by exact prefixLift 7600734
  have htrace : WordTrace (prefixWord ++ tailWord_7600734) baseStart_7600734 baseEnd_7600734 := by
    simpa [prefixWord, tailWord_7600734, baseEnd_7600734] using wordTrace_append hprefix tailTrace_7600734
  have hstable : (prefixWord ++ tailWord_7600734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600734).length < 2 ^ (prefixWord ++ tailWord_7600734).sum := by decide
  have hdescent : baseEnd_7600734 < baseStart_7600734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600780 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_7600780 : Nat := 118140960795 + 7600780 * 2 ^ 59
def prefixEnd_7600780 : Nat := 4983230072969 + 3 ^ 40 * 7600780 * 2
def baseEnd_7600780 : Nat := 3902853489080877146994655

theorem tailTrace_7600780 : CollatzResearch.WordTrace tailWord_7600780 prefixEnd_7600780 3902853489080877146994655 := by
  unfold tailWord_7600780
  simp only [CollatzResearch.WordTrace]
  refine ⟨138611610701839822360651897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184815480935786429814202529 138611610701839822360651897)
  ·
    refine ⟨103958708026379866770488923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138611610701839822360651897 103958708026379866770488923)
    ·
      refine ⟨155938062039569800155733385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103958708026379866770488923 155938062039569800155733385)
      ·
        refine ⟨116953546529677350116800039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155938062039569800155733385 116953546529677350116800039)
        ·
          refine ⟨175430319794516025175200059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116953546529677350116800039 175430319794516025175200059)
          ·
            refine ⟨263145479691774037762800089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175430319794516025175200059 263145479691774037762800089)
            ·
              refine ⟨197359109768830528322100067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263145479691774037762800089 197359109768830528322100067)
              ·
                refine ⟨296038664653245792483150101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197359109768830528322100067 296038664653245792483150101)
                ·
                  refine ⟨13876812405620896522647661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 296038664653245792483150101 13876812405620896522647661)
                  ·
                    refine ⟨5203804652107836195992873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13876812405620896522647661 5203804652107836195992873)
                    ·
                      refine ⟨3902853489080877146994655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203804652107836195992873 3902853489080877146994655)
                      ·
                        rfl

theorem cell23_7600780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_7600780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600780 prefixEnd_7600780 := by exact prefixLift 7600780
  have htrace : WordTrace (prefixWord ++ tailWord_7600780) baseStart_7600780 baseEnd_7600780 := by
    simpa [prefixWord, tailWord_7600780, baseEnd_7600780] using wordTrace_append hprefix tailTrace_7600780
  have hstable : (prefixWord ++ tailWord_7600780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600780).length < 2 ^ (prefixWord ++ tailWord_7600780).sum := by decide
  have hdescent : baseEnd_7600780 < baseStart_7600780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600814 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7600814 : Nat := 118140960795 + 7600814 * 2 ^ 59
def prefixEnd_7600814 : Nat := 4983230072969 + 3 ^ 40 * 7600814 * 2
def baseEnd_7600814 : Nat := 3902870947423130013969499

theorem tailTrace_7600814 : CollatzResearch.WordTrace tailWord_7600814 prefixEnd_7600814 3902870947423130013969499 := by
  unfold tailWord_7600814
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653057685694558566005187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184816307657037645685360997 34653057685694558566005187)
  ·
    refine ⟨51979586528541837849007781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34653057685694558566005187 51979586528541837849007781)
    ·
      refine ⟨9746172474101594596688959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51979586528541837849007781 9746172474101594596688959)
      ·
        refine ⟨14619258711152391895033439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746172474101594596688959 14619258711152391895033439)
        ·
          refine ⟨21928888066728587842550159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14619258711152391895033439 21928888066728587842550159)
          ·
            refine ⟨32893332100092881763825239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21928888066728587842550159 32893332100092881763825239)
            ·
              refine ⟨49339998150139322645737859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32893332100092881763825239 49339998150139322645737859)
              ·
                refine ⟨74009997225208983968606789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49339998150139322645737859 74009997225208983968606789)
                ·
                  refine ⟨13876874479726684494113773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74009997225208983968606789 13876874479726684494113773)
                  ·
                    refine ⟨5203827929897506685292665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13876874479726684494113773 5203827929897506685292665)
                    ·
                      refine ⟨3902870947423130013969499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203827929897506685292665 3902870947423130013969499)
                      ·
                        rfl

theorem cell23_7600814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7600814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600814 prefixEnd_7600814 := by exact prefixLift 7600814
  have htrace : WordTrace (prefixWord ++ tailWord_7600814) baseStart_7600814 baseEnd_7600814 := by
    simpa [prefixWord, tailWord_7600814, baseEnd_7600814] using wordTrace_append hprefix tailTrace_7600814
  have hstable : (prefixWord ++ tailWord_7600814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600814).length < 2 ^ (prefixWord ++ tailWord_7600814).sum := by decide
  have hdescent : baseEnd_7600814 < baseStart_7600814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600830 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7600830 : Nat := 118140960795 + 7600830 * 2 ^ 59
def prefixEnd_7600830 : Nat := 4983230072969 + 3 ^ 40 * 7600830 * 2
def baseEnd_7600830 : Nat := 3902879163113601951369425

theorem tailTrace_7600830 : CollatzResearch.WordTrace tailWord_7600830 prefixEnd_7600830 3902879163113601951369425 := by
  unfold tailWord_7600830
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653130631687312907577993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184816696702332335507082629 34653130631687312907577993)
  ·
    refine ⟨25989847973765484680683495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34653130631687312907577993 25989847973765484680683495)
    ·
      refine ⟨38984771960648227021025243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25989847973765484680683495 38984771960648227021025243)
      ·
        refine ⟨58477157940972340531537865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38984771960648227021025243 58477157940972340531537865)
        ·
          refine ⟨43857868455729255398653399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58477157940972340531537865 43857868455729255398653399)
          ·
            refine ⟨65786802683593883097980099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43857868455729255398653399 65786802683593883097980099)
            ·
              refine ⟨98680204025390824646970149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65786802683593883097980099 98680204025390824646970149)
              ·
                refine ⟨18502538254760779621306903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98680204025390824646970149 18502538254760779621306903)
                ·
                  refine ⟨27753807382141169431960355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18502538254760779621306903 27753807382141169431960355)
                  ·
                    refine ⟨41630711073211754147940533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27753807382141169431960355 41630711073211754147940533)
                    ·
                      refine ⟨3902879163113601951369425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41630711073211754147940533 3902879163113601951369425)
                      ·
                        rfl

theorem cell23_7600830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7600830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600830 prefixEnd_7600830 := by exact prefixLift 7600830
  have htrace : WordTrace (prefixWord ++ tailWord_7600830) baseStart_7600830 baseEnd_7600830 := by
    simpa [prefixWord, tailWord_7600830, baseEnd_7600830] using wordTrace_append hprefix tailTrace_7600830
  have hstable : (prefixWord ++ tailWord_7600830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600830).length < 2 ^ (prefixWord ++ tailWord_7600830).sum := by decide
  have hdescent : baseEnd_7600830 < baseStart_7600830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600844 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7600844 : Nat := 118140960795 + 7600844 * 2 ^ 59
def prefixEnd_7600844 : Nat := 4983230072969 + 3 ^ 40 * 7600844 * 2
def baseEnd_7600844 : Nat := 3902886351842764896594361

theorem tailTrace_7600844 : CollatzResearch.WordTrace tailWord_7600844 prefixEnd_7600844 3902886351842764896594361 := by
  unfold tailWord_7600844
  simp only [CollatzResearch.WordTrace]
  refine ⟨138612777837723891825816793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184817037116965189101089057 138612777837723891825816793)
  ·
    refine ⟨103959583378292918869362595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138612777837723891825816793 103959583378292918869362595)
    ·
      refine ⟨155939375067439378304043893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103959583378292918869362595 155939375067439378304043893)
      ·
        refine ⟨14619316412572441716004115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155939375067439378304043893 14619316412572441716004115)
        ·
          refine ⟨21928974618858662574006173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14619316412572441716004115 21928974618858662574006173)
          ·
            refine ⟨8223365482071998465252315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21928974618858662574006173 8223365482071998465252315)
            ·
              refine ⟨12335048223107997697878473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8223365482071998465252315 12335048223107997697878473)
              ·
                refine ⟨9251286167330998273408855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12335048223107997697878473 9251286167330998273408855)
                ·
                  refine ⟨13876929250996497410113283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9251286167330998273408855 13876929250996497410113283)
                  ·
                    refine ⟨20815393876494746115169925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13876929250996497410113283 20815393876494746115169925)
                    ·
                      refine ⟨3902886351842764896594361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20815393876494746115169925 3902886351842764896594361)
                      ·
                        rfl

theorem cell23_7600844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7600844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600844 prefixEnd_7600844 := by exact prefixLift 7600844
  have htrace : WordTrace (prefixWord ++ tailWord_7600844) baseStart_7600844 baseEnd_7600844 := by
    simpa [prefixWord, tailWord_7600844, baseEnd_7600844] using wordTrace_append hprefix tailTrace_7600844
  have hstable : (prefixWord ++ tailWord_7600844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600844).length < 2 ^ (prefixWord ++ tailWord_7600844).sum := by decide
  have hdescent : baseEnd_7600844 < baseStart_7600844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600873 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_7600873 : Nat := 118140960795 + 7600873 * 2 ^ 59
def prefixEnd_7600873 : Nat := 4983230072969 + 3 ^ 40 * 7600873 * 2
def baseEnd_7600873 : Nat := 3902901242781745283131727

theorem tailTrace_7600873 : CollatzResearch.WordTrace tailWord_7600873 prefixEnd_7600873 3902901242781745283131727 := by
  unfold tailWord_7600873
  simp only [CollatzResearch.WordTrace]
  refine ⟨277226613392342721604439273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184817742261561814402959515 277226613392342721604439273)
  ·
    refine ⟨207919960044257041203329455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277226613392342721604439273 207919960044257041203329455)
    ·
      refine ⟨311879940066385561804994183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207919960044257041203329455 311879940066385561804994183)
      ·
        refine ⟨467819910099578342707491275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311879940066385561804994183 467819910099578342707491275)
        ·
          refine ⟨701729865149367514061236913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467819910099578342707491275 701729865149367514061236913)
          ·
            refine ⟨526297398862025635545927685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701729865149367514061236913 526297398862025635545927685)
            ·
              refine ⟨98680762286629806664861441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526297398862025635545927685 98680762286629806664861441)
              ·
                refine ⟨74010571714972354998646081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98680762286629806664861441 74010571714972354998646081)
                ·
                  refine ⟨55507928786229266248984561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74010571714972354998646081 55507928786229266248984561)
                  ·
                    refine ⟨41630946589671949686738421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55507928786229266248984561 41630946589671949686738421)
                    ·
                      refine ⟨3902901242781745283131727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41630946589671949686738421 3902901242781745283131727)
                      ·
                        rfl

theorem cell23_7600873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_7600873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600873 prefixEnd_7600873 := by exact prefixLift 7600873
  have htrace : WordTrace (prefixWord ++ tailWord_7600873) baseStart_7600873 baseEnd_7600873 := by
    simpa [prefixWord, tailWord_7600873, baseEnd_7600873] using wordTrace_append hprefix tailTrace_7600873
  have hstable : (prefixWord ++ tailWord_7600873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600873).length < 2 ^ (prefixWord ++ tailWord_7600873).sum := by decide
  have hdescent : baseEnd_7600873 < baseStart_7600873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600878 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_7600878 : Nat := 118140960795 + 7600878 * 2 ^ 59
def prefixEnd_7600878 : Nat := 4983230072969 + 3 ^ 40 * 7600878 * 2
def baseEnd_7600878 : Nat := 3902903810185017763569205

theorem tailTrace_7600878 : CollatzResearch.WordTrace tailWord_7600878 prefixEnd_7600878 3902903810185017763569205 := by
  unfold tailWord_7600878
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653349469665575932296411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184817863838216404972247525 34653349469665575932296411)
  ·
    refine ⟨51980024204498363898444617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34653349469665575932296411 51980024204498363898444617)
    ·
      refine ⟨38985018153373772923833463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51980024204498363898444617 38985018153373772923833463)
      ·
        refine ⟨58477527230060659385750195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38985018153373772923833463 58477527230060659385750195)
        ·
          refine ⟨87716290845090989078625293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58477527230060659385750195 87716290845090989078625293)
          ·
            refine ⟨32893609066909120904484485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87716290845090989078625293 32893609066909120904484485)
            ·
              refine ⟨6167551700045460169590841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32893609066909120904484485 6167551700045460169590841)
              ·
                refine ⟨4625663775034095127193131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167551700045460169590841 4625663775034095127193131)
                ·
                  refine ⟨6938495662551142690789697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625663775034095127193131 6938495662551142690789697)
                  ·
                    refine ⟨5203871746913357018092273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6938495662551142690789697 5203871746913357018092273)
                    ·
                      refine ⟨3902903810185017763569205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203871746913357018092273 3902903810185017763569205)
                      ·
                        rfl

theorem cell23_7600878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_7600878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600878 prefixEnd_7600878 := by exact prefixLift 7600878
  have htrace : WordTrace (prefixWord ++ tailWord_7600878) baseStart_7600878 baseEnd_7600878 := by
    simpa [prefixWord, tailWord_7600878, baseEnd_7600878] using wordTrace_append hprefix tailTrace_7600878
  have hstable : (prefixWord ++ tailWord_7600878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600878).length < 2 ^ (prefixWord ++ tailWord_7600878).sum := by decide
  have hdescent : baseEnd_7600878 < baseStart_7600878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600894 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7600894 : Nat := 118140960795 + 7600894 * 2 ^ 59
def prefixEnd_7600894 : Nat := 4983230072969 + 3 ^ 40 * 7600894 * 2
def baseEnd_7600894 : Nat := 3902912025875489700969131

theorem tailTrace_7600894 : CollatzResearch.WordTrace tailWord_7600894 prefixEnd_7600894 3902912025875489700969131 := by
  unfold tailWord_7600894
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653422415658330273869217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184818252883511094793969157 34653422415658330273869217)
  ·
    refine ⟨25990066811743747705401913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34653422415658330273869217 25990066811743747705401913)
    ·
      refine ⟨19492550108807810779051435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25990066811743747705401913 19492550108807810779051435)
      ·
        refine ⟨29238825163211716168577153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492550108807810779051435 29238825163211716168577153)
        ·
          refine ⟨21929118872408787126432865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29238825163211716168577153 21929118872408787126432865)
          ·
            refine ⟨16446839154306590344824649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21929118872408787126432865 16446839154306590344824649)
            ·
              refine ⟨12335129365729942758618487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16446839154306590344824649 12335129365729942758618487)
              ·
                refine ⟨18502694048594914137927731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12335129365729942758618487 18502694048594914137927731)
                ·
                  refine ⟨27754041072892371206891597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18502694048594914137927731 27754041072892371206891597)
                  ·
                    refine ⟨10407765402334639202584349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27754041072892371206891597 10407765402334639202584349)
                    ·
                      refine ⟨3902912025875489700969131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10407765402334639202584349 3902912025875489700969131)
                      ·
                        rfl

theorem cell23_7600894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7600894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600894 prefixEnd_7600894 := by exact prefixLift 7600894
  have htrace : WordTrace (prefixWord ++ tailWord_7600894) baseStart_7600894 baseEnd_7600894 := by
    simpa [prefixWord, tailWord_7600894, baseEnd_7600894] using wordTrace_append hprefix tailTrace_7600894
  have hstable : (prefixWord ++ tailWord_7600894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600894).length < 2 ^ (prefixWord ++ tailWord_7600894).sum := by decide
  have hdescent : baseEnd_7600894 < baseStart_7600894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600900 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7600900 : Nat := 118140960795 + 7600900 * 2 ^ 59
def prefixEnd_7600900 : Nat := 4983230072969 + 3 ^ 40 * 7600900 * 2
def baseEnd_7600900 : Nat := 3902915106759416677494103

theorem tailTrace_7600900 : CollatzResearch.WordTrace tailWord_7600900 prefixEnd_7600900 3902915106759416677494103 := by
  unfold tailWord_7600900
  simp only [CollatzResearch.WordTrace]
  refine ⟨138613799081622452607836077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184818398775496603477114769 138613799081622452607836077)
  ·
    refine ⟨51980174655608419727938529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138613799081622452607836077 51980174655608419727938529)
    ·
      refine ⟨38985130991706314795953897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51980174655608419727938529 38985130991706314795953897)
      ·
        refine ⟨29238848243779736096965423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38985130991706314795953897 29238848243779736096965423)
        ·
          refine ⟨43858272365669604145448135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29238848243779736096965423 43858272365669604145448135)
          ·
            refine ⟨65787408548504406218172203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43858272365669604145448135 65787408548504406218172203)
            ·
              refine ⟨98681112822756609327258305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65787408548504406218172203 98681112822756609327258305)
              ·
                refine ⟨74010834617067456995443729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98681112822756609327258305 74010834617067456995443729)
                ·
                  refine ⟨55508125962800592746582797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74010834617067456995443729 55508125962800592746582797)
                  ·
                    refine ⟨20815547236050222279968549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55508125962800592746582797 20815547236050222279968549)
                    ·
                      refine ⟨3902915106759416677494103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20815547236050222279968549 3902915106759416677494103)
                      ·
                        rfl

theorem cell23_7600900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7600900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600900 prefixEnd_7600900 := by exact prefixLift 7600900
  have htrace : WordTrace (prefixWord ++ tailWord_7600900) baseStart_7600900 baseEnd_7600900 := by
    simpa [prefixWord, tailWord_7600900, baseEnd_7600900] using wordTrace_append hprefix tailTrace_7600900
  have hstable : (prefixWord ++ tailWord_7600900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600900).length < 2 ^ (prefixWord ++ tailWord_7600900).sum := by decide
  have hdescent : baseEnd_7600900 < baseStart_7600900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600917 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_7600917 : Nat := 118140960795 + 7600917 * 2 ^ 59
def prefixEnd_7600917 : Nat := 4983230072969 + 3 ^ 40 * 7600917 * 2
def baseEnd_7600917 : Nat := 3902923835930543110981525

theorem tailTrace_7600917 : CollatzResearch.WordTrace tailWord_7600917 prefixEnd_7600917 3902923835930543110981525 := by
  unfold tailWord_7600917
  simp only [CollatzResearch.WordTrace]
  refine ⟨277228218204183317119041005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184818812136122211412694003 277228218204183317119041005)
  ·
    refine ⟨103960581826568743919640377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277228218204183317119041005 103960581826568743919640377)
    ·
      refine ⟨77970436369926557939730283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103960581826568743919640377 77970436369926557939730283)
      ·
        refine ⟨116955654554889836909595425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77970436369926557939730283 116955654554889836909595425)
        ·
          refine ⟨87716740916167377682196569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116955654554889836909595425 87716740916167377682196569)
          ·
            refine ⟨65787555687125533261647427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87716740916167377682196569 65787555687125533261647427)
            ·
              refine ⟨98681333530688299892471141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65787555687125533261647427 98681333530688299892471141)
              ·
                refine ⟨18502750037004056229838339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98681333530688299892471141 18502750037004056229838339)
                ·
                  refine ⟨27754125055506084344757509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18502750037004056229838339 27754125055506084344757509)
                  ·
                    refine ⟨5203898447907390814642033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27754125055506084344757509 5203898447907390814642033)
                    ·
                      refine ⟨3902923835930543110981525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203898447907390814642033 3902923835930543110981525)
                      ·
                        rfl

theorem cell23_7600917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_7600917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600917 prefixEnd_7600917 := by exact prefixLift 7600917
  have htrace : WordTrace (prefixWord ++ tailWord_7600917) baseStart_7600917 baseEnd_7600917 := by
    simpa [prefixWord, tailWord_7600917, baseEnd_7600917] using wordTrace_append hprefix tailTrace_7600917
  have hstable : (prefixWord ++ tailWord_7600917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600917).length < 2 ^ (prefixWord ++ tailWord_7600917).sum := by decide
  have hdescent : baseEnd_7600917 < baseStart_7600917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600940 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 7]
def baseStart_7600940 : Nat := 118140960795 + 7600940 * 2 ^ 59
def prefixEnd_7600940 : Nat := 4983230072969 + 3 ^ 40 * 7600940 * 2
def baseEnd_7600940 : Nat := 433659516220621835665991

theorem tailTrace_7600940 : CollatzResearch.WordTrace tailWord_7600940 prefixEnd_7600940 433659516220621835665991 := by
  unfold tailWord_7600940
  simp only [CollatzResearch.WordTrace]
  refine ⟨138614528541549996023564137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184819371388733328031418849 138614528541549996023564137)
  ·
    refine ⟨103960896406162497017673103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138614528541549996023564137 103960896406162497017673103)
    ·
      refine ⟨155941344609243745526509655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103960896406162497017673103 155941344609243745526509655)
      ·
        refine ⟨233912016913865618289764483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155941344609243745526509655 233912016913865618289764483)
        ·
          refine ⟨350868025370798427434646725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233912016913865618289764483 350868025370798427434646725)
          ·
            refine ⟨65787754757024705143996261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350868025370798427434646725 65787754757024705143996261)
            ·
              refine ⟨12335204016942132214499299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65787754757024705143996261 12335204016942132214499299)
              ·
                refine ⟨18502806025413198321748949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12335204016942132214499299 18502806025413198321748949)
                ·
                  refine ⟨433659516220621835665991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18502806025413198321748949 433659516220621835665991)
                  ·
                    rfl

theorem cell23_7600940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_7600940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600940 prefixEnd_7600940 := by exact prefixLift 7600940
  have htrace : WordTrace (prefixWord ++ tailWord_7600940) baseStart_7600940 baseEnd_7600940 := by
    simpa [prefixWord, tailWord_7600940, baseEnd_7600940] using wordTrace_append hprefix tailTrace_7600940
  have hstable : (prefixWord ++ tailWord_7600940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600940).length < 2 ^ (prefixWord ++ tailWord_7600940).sum := by decide
  have hdescent : baseEnd_7600940 < baseStart_7600940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600943 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_7600943 : Nat := 118140960795 + 7600943 * 2 ^ 59
def prefixEnd_7600943 : Nat := 4983230072969 + 3 ^ 40 * 7600943 * 2
def baseEnd_7600943 : Nat := 3902937186427560009256405

theorem tailTrace_7600943 : CollatzResearch.WordTrace tailWord_7600943 prefixEnd_7600943 3902937186427560009256405 := by
  unfold tailWord_7600943
  simp only [CollatzResearch.WordTrace]
  refine ⟨277229166502089123559487483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184819444334726082372991655 277229166502089123559487483)
  ·
    refine ⟨415843749753133685339231225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277229166502089123559487483 415843749753133685339231225)
    ·
      refine ⟨311882812314850264004423419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415843749753133685339231225 311882812314850264004423419)
      ·
        refine ⟨467824218472275396006635129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311882812314850264004423419 467824218472275396006635129)
        ·
          refine ⟨350868163854206547004976347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467824218472275396006635129 350868163854206547004976347)
          ·
            refine ⟨526302245781309820507464521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350868163854206547004976347 526302245781309820507464521)
            ·
              refine ⟨394726684335982365380598391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526302245781309820507464521 394726684335982365380598391)
              ·
                refine ⟨592090026503973548070897587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394726684335982365380598391 592090026503973548070897587)
                ·
                  refine ⟨888135039755960322106346381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592090026503973548070897587 888135039755960322106346381)
                  ·
                    refine ⟨333050639908485120789879893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888135039755960322106346381 333050639908485120789879893)
                    ·
                      refine ⟨3902937186427560009256405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333050639908485120789879893 3902937186427560009256405)
                      ·
                        rfl

theorem cell23_7600943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_7600943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600943 prefixEnd_7600943 := by exact prefixLift 7600943
  have htrace : WordTrace (prefixWord ++ tailWord_7600943) baseStart_7600943 baseEnd_7600943 := by
    simpa [prefixWord, tailWord_7600943, baseEnd_7600943] using wordTrace_append hprefix tailTrace_7600943
  have hstable : (prefixWord ++ tailWord_7600943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600943).length < 2 ^ (prefixWord ++ tailWord_7600943).sum := by decide
  have hdescent : baseEnd_7600943 < baseStart_7600943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7600951 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_7600951 : Nat := 118140960795 + 7600951 * 2 ^ 59
def prefixEnd_7600951 : Nat := 4983230072969 + 3 ^ 40 * 7600951 * 2
def baseEnd_7600951 : Nat := 3902941294272795977956369

theorem tailTrace_7600951 : CollatzResearch.WordTrace tailWord_7600951 prefixEnd_7600951 3902941294272795977956369 := by
  unfold tailWord_7600951
  simp only [CollatzResearch.WordTrace]
  refine ⟨277229458286060140925778707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184819638857373427283852471 277229458286060140925778707)
  ·
    refine ⟨415844187429090211388668061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277229458286060140925778707 415844187429090211388668061)
    ·
      refine ⟨155941570285908829270750523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415844187429090211388668061 155941570285908829270750523)
      ·
        refine ⟨233912355428863243906125785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155941570285908829270750523 233912355428863243906125785)
        ·
          refine ⟨175434266571647432929594339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233912355428863243906125785 175434266571647432929594339)
          ·
            refine ⟨263151399857471149394391509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175434266571647432929594339 263151399857471149394391509)
            ·
              refine ⟨6167610934159480063931051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263151399857471149394391509 6167610934159480063931051)
              ·
                refine ⟨9251416401239220095896577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167610934159480063931051 9251416401239220095896577)
                ·
                  refine ⟨6938562300929415071922433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9251416401239220095896577 6938562300929415071922433)
                  ·
                    refine ⟨5203921725697061303941825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6938562300929415071922433 5203921725697061303941825)
                    ·
                      refine ⟨3902941294272795977956369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203921725697061303941825 3902941294272795977956369)
                      ·
                        rfl

theorem cell23_7600951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_7600951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7600951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7600951 prefixEnd_7600951 := by exact prefixLift 7600951
  have htrace : WordTrace (prefixWord ++ tailWord_7600951) baseStart_7600951 baseEnd_7600951 := by
    simpa [prefixWord, tailWord_7600951, baseEnd_7600951] using wordTrace_append hprefix tailTrace_7600951
  have hstable : (prefixWord ++ tailWord_7600951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7600951).length < 2 ^ (prefixWord ++ tailWord_7600951).sum := by decide
  have hdescent : baseEnd_7600951 < baseStart_7600951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7600951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601007 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 2, 4, 2]
def baseStart_7601007 : Nat := 118140960795 + 7601007 * 2 ^ 59
def prefixEnd_7601007 : Nat := 4983230072969 + 3 ^ 40 * 7601007 * 2
def baseEnd_7601007 : Nat := 3902970049189447758856111

theorem tailTrace_7601007 : CollatzResearch.WordTrace tailWord_7601007 prefixEnd_7601007 3902970049189447758856111 := by
  unfold tailWord_7601007
  simp only [CollatzResearch.WordTrace]
  refine ⟨277231500773857262489817275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184821000515904841659878183 277231500773857262489817275)
  ·
    refine ⟨415847251160785893734725913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277231500773857262489817275 415847251160785893734725913)
    ·
      refine ⟨311885438370589420301044435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415847251160785893734725913 311885438370589420301044435)
      ·
        refine ⟨467828157555884130451566653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311885438370589420301044435 467828157555884130451566653)
        ·
          refine ⟨175435559083456548919337495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467828157555884130451566653 175435559083456548919337495)
          ·
            refine ⟨263153338625184823379006243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175435559083456548919337495 263153338625184823379006243)
            ·
              refine ⟨394730007937777235068509365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263153338625184823379006243 394730007937777235068509365)
              ·
                refine ⟨37005938244166615787672753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394730007937777235068509365 37005938244166615787672753)
                ·
                  refine ⟨27754453683124961840754565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37005938244166615787672753 27754453683124961840754565)
                  ·
                    refine ⟨5203960065585930345141481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27754453683124961840754565 5203960065585930345141481)
                    ·
                      refine ⟨3902970049189447758856111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5203960065585930345141481 3902970049189447758856111)
                      ·
                        rfl

theorem cell23_7601007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4, 2].length) (baseStart_7601007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601007 prefixEnd_7601007 := by exact prefixLift 7601007
  have htrace : WordTrace (prefixWord ++ tailWord_7601007) baseStart_7601007 baseEnd_7601007 := by
    simpa [prefixWord, tailWord_7601007, baseEnd_7601007] using wordTrace_append hprefix tailTrace_7601007
  have hstable : (prefixWord ++ tailWord_7601007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601007).length < 2 ^ (prefixWord ++ tailWord_7601007).sum := by decide
  have hdescent : baseEnd_7601007 < baseStart_7601007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601020 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_7601020 : Nat := 118140960795 + 7601020 * 2 ^ 59
def prefixEnd_7601020 : Nat := 4983230072969 + 3 ^ 40 * 7601020 * 2
def baseEnd_7601020 : Nat := 3902976724437956207993551

theorem tailTrace_7601020 : CollatzResearch.WordTrace tailWord_7601020 prefixEnd_7601020 3902976724437956207993551 := by
  unfold tailWord_7601020
  simp only [CollatzResearch.WordTrace]
  refine ⟨138615987461405082855020257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184821316615206777140027009 138615987461405082855020257)
  ·
    refine ⟨103961990596053812141265193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138615987461405082855020257 103961990596053812141265193)
    ·
      refine ⟨77971492947040359105948895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103961990596053812141265193 77971492947040359105948895)
      ·
        refine ⟨116957239420560538658923343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77971492947040359105948895 116957239420560538658923343)
        ·
          refine ⟨175435859130840807988385015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116957239420560538658923343 175435859130840807988385015)
          ·
            refine ⟨263153788696261211982577523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175435859130840807988385015 263153788696261211982577523)
            ·
              refine ⟨394730683044391817973866285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263153788696261211982577523 394730683044391817973866285)
              ·
                refine ⟨148024006141646931740199857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394730683044391817973866285 148024006141646931740199857)
                ·
                  refine ⟨111018004606235198805149893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148024006141646931740199857 111018004606235198805149893)
                  ·
                    refine ⟨20815875863669099775965605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111018004606235198805149893 20815875863669099775965605)
                    ·
                      refine ⟨3902976724437956207993551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20815875863669099775965605 3902976724437956207993551)
                      ·
                        rfl

theorem cell23_7601020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_7601020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601020 prefixEnd_7601020 := by exact prefixLift 7601020
  have htrace : WordTrace (prefixWord ++ tailWord_7601020) baseStart_7601020 baseEnd_7601020 := by
    simpa [prefixWord, tailWord_7601020, baseEnd_7601020] using wordTrace_append hprefix tailTrace_7601020
  have hstable : (prefixWord ++ tailWord_7601020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601020).length < 2 ^ (prefixWord ++ tailWord_7601020).sum := by decide
  have hdescent : baseEnd_7601020 < baseStart_7601020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601044 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7601044 : Nat := 118140960795 + 7601044 * 2 ^ 59
def prefixEnd_7601044 : Nat := 4983230072969 + 3 ^ 40 * 7601044 * 2
def baseEnd_7601044 : Nat := 3902989047973664114093441

theorem tailTrace_7601044 : CollatzResearch.WordTrace tailWord_7601044 prefixEnd_7601044 3902989047973664114093441 := by
  unfold tailWord_7601044
  simp only [CollatzResearch.WordTrace]
  refine ⟨138616425137361608904457093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184821900183148811872609457 138616425137361608904457093)
  ·
    refine ⟨25990579713255301669585705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138616425137361608904457093 25990579713255301669585705)
    ·
      refine ⟨19492934784941476252189279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25990579713255301669585705 19492934784941476252189279)
      ·
        refine ⟨29239402177412214378283919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492934784941476252189279 29239402177412214378283919)
        ·
          refine ⟨43859103266118321567425879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29239402177412214378283919 43859103266118321567425879)
          ·
            refine ⟨65788654899177482351138819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43859103266118321567425879 65788654899177482351138819)
            ·
              refine ⟨98682982348766223526708229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65788654899177482351138819 98682982348766223526708229)
              ·
                refine ⟨18503059190393666911257793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98682982348766223526708229 18503059190393666911257793)
                ·
                  refine ⟨13877294392795250183443345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18503059190393666911257793 13877294392795250183443345)
                  ·
                    refine ⟨10407970794596437637582509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13877294392795250183443345 10407970794596437637582509)
                    ·
                      refine ⟨3902989047973664114093441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10407970794596437637582509 3902989047973664114093441)
                      ·
                        rfl

theorem cell23_7601044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7601044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601044 prefixEnd_7601044 := by exact prefixLift 7601044
  have htrace : WordTrace (prefixWord ++ tailWord_7601044) baseStart_7601044 baseEnd_7601044 := by
    simpa [prefixWord, tailWord_7601044, baseEnd_7601044] using wordTrace_append hprefix tailTrace_7601044
  have hstable : (prefixWord ++ tailWord_7601044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601044).length < 2 ^ (prefixWord ++ tailWord_7601044).sum := by decide
  have hdescent : baseEnd_7601044 < baseStart_7601044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601047 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 6]
def baseStart_7601047 : Nat := 118140960795 + 7601047 * 2 ^ 59
def prefixEnd_7601047 : Nat := 4983230072969 + 3 ^ 40 * 7601047 * 2
def baseEnd_7601047 : Nat := 433665620935069733595103

theorem tailTrace_7601047 : CollatzResearch.WordTrace tailWord_7601047 prefixEnd_7601047 433665620935069733595103 := by
  unfold tailWord_7601047
  simp only [CollatzResearch.WordTrace]
  refine ⟨277232959693712349321273395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184821973129141566214182263 277232959693712349321273395)
  ·
    refine ⟨415849439540568523981910093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277232959693712349321273395 415849439540568523981910093)
    ·
      refine ⟨155943539827713196493216285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415849439540568523981910093 155943539827713196493216285)
      ·
        refine ⟨58478827435392448684956107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155943539827713196493216285 58478827435392448684956107)
        ·
          refine ⟨87718241153088673027434161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58478827435392448684956107 87718241153088673027434161)
          ·
            refine ⟨65788680864816504770575621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87718241153088673027434161 65788680864816504770575621)
            ·
              refine ⟨12335377662153094644482929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65788680864816504770575621 12335377662153094644482929)
              ·
                refine ⟨9251533246614820983362197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12335377662153094644482929 9251533246614820983362197)
                ·
                  refine ⟨433665620935069733595103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9251533246614820983362197 433665620935069733595103)
                  ·
                    rfl

theorem cell23_7601047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 6].length) (baseStart_7601047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601047 prefixEnd_7601047 := by exact prefixLift 7601047
  have htrace : WordTrace (prefixWord ++ tailWord_7601047) baseStart_7601047 baseEnd_7601047 := by
    simpa [prefixWord, tailWord_7601047, baseEnd_7601047] using wordTrace_append hprefix tailTrace_7601047
  have hstable : (prefixWord ++ tailWord_7601047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601047).length < 2 ^ (prefixWord ++ tailWord_7601047).sum := by decide
  have hdescent : baseEnd_7601047 < baseStart_7601047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
