import V185TrunkScan22Chunk179

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1606447 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 8, 3]
def baseStart_1606447 : Nat := 118140960795 + 1606447 * 2 ^ 59
def prefixEnd_1606447 : Nat := 4983230072969 + 3 ^ 40 * 1606447 * 2
def baseEnd_1606447 : Nat := 549919637982254334949727

theorem tailTrace_1606447 : CollatzResearch.WordTrace tailWord_1606447 prefixEnd_1606447 549919637982254334949727 := by
  unfold tailWord_1606447
  simp only [CollatzResearch.WordTrace]
  refine ⟨58591935611124353149849595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39061290407416235433233063 58591935611124353149849595)
  ·
    refine ⟨87887903416686529724774393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58591935611124353149849595 87887903416686529724774393)
    ·
      refine ⟨65915927562514897293580795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87887903416686529724774393 65915927562514897293580795)
      ·
        refine ⟨98873891343772345940371193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65915927562514897293580795 98873891343772345940371193)
        ·
          refine ⟨74155418507829259455278395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98873891343772345940371193 74155418507829259455278395)
          ·
            refine ⟨111233127761743889182917593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74155418507829259455278395 111233127761743889182917593)
            ·
              refine ⟨83424845821307916887188195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111233127761743889182917593 83424845821307916887188195)
              ·
                refine ⟨125137268731961875330782293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83424845821307916887188195 125137268731961875330782293)
                ·
                  refine ⟨1466452367952678226532605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 125137268731961875330782293 1466452367952678226532605)
                  ·
                    refine ⟨549919637982254334949727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466452367952678226532605 549919637982254334949727)
                    ·
                      rfl

theorem cell22_1606447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_1606447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606447 prefixEnd_1606447 := by exact prefixLift 1606447
  have htrace : WordTrace (prefixWord ++ tailWord_1606447) baseStart_1606447 baseEnd_1606447 := by
    simpa [prefixWord, tailWord_1606447, baseEnd_1606447] using wordTrace_append hprefix tailTrace_1606447
  have hstable : (prefixWord ++ tailWord_1606447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606447).length < 2 ^ (prefixWord ++ tailWord_1606447).sum := by decide
  have hdescent : baseEnd_1606447 < baseStart_1606447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606498 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1606498 : Nat := 118140960795 + 1606498 * 2 ^ 59
def prefixEnd_1606498 : Nat := 4983230072969 + 3 ^ 40 * 1606498 * 2
def baseEnd_1606498 : Nat := 549937096324507201924571

theorem tailTrace_1606498 : CollatzResearch.WordTrace tailWord_1606498 prefixEnd_1606498 549937096324507201924571 := by
  unfold tailWord_1606498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648448933484897214989037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39062530489293059239970765 14648448933484897214989037)
  ·
    refine ⟨5493168350056836455620889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14648448933484897214989037 5493168350056836455620889)
    ·
      refine ⟨4119876262542627341715667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493168350056836455620889 4119876262542627341715667)
      ·
        refine ⟨6179814393813941012573501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119876262542627341715667 6179814393813941012573501)
        ·
          refine ⟨2317430397680227879715063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6179814393813941012573501 2317430397680227879715063)
          ·
            refine ⟨3476145596520341819572595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317430397680227879715063 3476145596520341819572595)
            ·
              refine ⟨5214218394780512729358893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476145596520341819572595 5214218394780512729358893)
              ·
                refine ⟨1955331898042692273509585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214218394780512729358893 1955331898042692273509585)
                ·
                  refine ⟨1466498923532019205132189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955331898042692273509585 1466498923532019205132189)
                  ·
                    refine ⟨549937096324507201924571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466498923532019205132189 549937096324507201924571)
                    ·
                      rfl

theorem cell22_1606498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1606498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606498 prefixEnd_1606498 := by exact prefixLift 1606498
  have htrace : WordTrace (prefixWord ++ tailWord_1606498) baseStart_1606498 baseEnd_1606498 := by
    simpa [prefixWord, tailWord_1606498, baseEnd_1606498] using wordTrace_append hprefix tailTrace_1606498
  have hstable : (prefixWord ++ tailWord_1606498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606498).length < 2 ^ (prefixWord ++ tailWord_1606498).sum := by decide
  have hdescent : baseEnd_1606498 < baseStart_1606498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606509 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1606509 : Nat := 118140960795 + 1606509 * 2 ^ 59
def prefixEnd_1606509 : Nat := 4983230072969 + 3 ^ 40 * 1606509 * 2
def baseEnd_1606509 : Nat := 549940861849306839899537

theorem tailTrace_1606509 : CollatzResearch.WordTrace tailWord_1606509 prefixEnd_1606509 549940861849306839899537 := by
  unfold tailWord_1606509
  simp only [CollatzResearch.WordTrace]
  refine ⟨58594196936899737738606581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39062797957933158492404387 58594196936899737738606581)
  ·
    refine ⟨5493205962834350412994367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58594196936899737738606581 5493205962834350412994367)
    ·
      refine ⟨8239808944251525619491551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493205962834350412994367 8239808944251525619491551)
      ·
        refine ⟨12359713416377288429237327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239808944251525619491551 12359713416377288429237327)
        ·
          refine ⟨18539570124565932643855991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359713416377288429237327 18539570124565932643855991)
          ·
            refine ⟨27809355186848898965783987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18539570124565932643855991 27809355186848898965783987)
            ·
              refine ⟨41714032780273348448675981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27809355186848898965783987 41714032780273348448675981)
              ·
                refine ⟨15642762292602505668253493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41714032780273348448675981 15642762292602505668253493)
                ·
                  refine ⟨1466508964931484906398765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15642762292602505668253493 1466508964931484906398765)
                  ·
                    refine ⟨549940861849306839899537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466508964931484906398765 549940861849306839899537)
                    ·
                      rfl

theorem cell22_1606509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1606509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606509 prefixEnd_1606509 := by exact prefixLift 1606509
  have htrace : WordTrace (prefixWord ++ tailWord_1606509) baseStart_1606509 baseEnd_1606509 := by
    simpa [prefixWord, tailWord_1606509, baseEnd_1606509] using wordTrace_append hprefix tailTrace_1606509
  have hstable : (prefixWord ++ tailWord_1606509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606509).length < 2 ^ (prefixWord ++ tailWord_1606509).sum := by decide
  have hdescent : baseEnd_1606509 < baseStart_1606509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606569 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_1606569 : Nat := 118140960795 + 1606569 * 2 ^ 59
def prefixEnd_1606569 : Nat := 4983230072969 + 3 ^ 40 * 1606569 * 2
def baseEnd_1606569 : Nat := 549961401075486683399353

theorem tailTrace_1606569 : CollatzResearch.WordTrace tailWord_1606569 prefixEnd_1606569 549961401075486683399353 := by
  unfold tailWord_1606569
  simp only [CollatzResearch.WordTrace]
  refine ⟨58596385316682367985790761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39064256877788245323860507 58596385316682367985790761)
  ·
    refine ⟨43947288987511775989343071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58596385316682367985790761 43947288987511775989343071)
    ·
      refine ⟨65920933481267663984014607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43947288987511775989343071 65920933481267663984014607)
      ·
        refine ⟨98881400221901495976021911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65920933481267663984014607 98881400221901495976021911)
        ·
          refine ⟨148322100332852243964032867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98881400221901495976021911 148322100332852243964032867)
          ·
            refine ⟨222483150499278365946049301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148322100332852243964032867 222483150499278365946049301)
            ·
              refine ⟨10428897679653673403721061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222483150499278365946049301 10428897679653673403721061)
              ·
                refine ⟨1955418314935063763197699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10428897679653673403721061 1955418314935063763197699)
                ·
                  refine ⟨2933127472402595644796549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955418314935063763197699 2933127472402595644796549)
                  ·
                    refine ⟨549961401075486683399353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933127472402595644796549 549961401075486683399353)
                    ·
                      rfl

theorem cell22_1606569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_1606569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606569 prefixEnd_1606569 := by exact prefixLift 1606569
  have htrace : WordTrace (prefixWord ++ tailWord_1606569) baseStart_1606569 baseEnd_1606569 := by
    simpa [prefixWord, tailWord_1606569, baseEnd_1606569] using wordTrace_append hprefix tailTrace_1606569
  have hstable : (prefixWord ++ tailWord_1606569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606569).length < 2 ^ (prefixWord ++ tailWord_1606569).sum := by decide
  have hdescent : baseEnd_1606569 < baseStart_1606569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606616 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_1606616 : Nat := 118140960795 + 1606616 * 2 ^ 59
def prefixEnd_1606616 : Nat := 4983230072969 + 3 ^ 40 * 1606616 * 2
def baseEnd_1606616 : Nat := 549977490135994227474209

theorem tailTrace_1606616 : CollatzResearch.WordTrace tailWord_1606616 prefixEnd_1606616 549977490135994227474209 := by
  unfold tailWord_1606616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29299049773756047506375851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39065399698341396675167801 29299049773756047506375851)
  ·
    refine ⟨43948574660634071259563777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29299049773756047506375851 43948574660634071259563777)
    ·
      refine ⟨32961430995475553444672833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43948574660634071259563777 32961430995475553444672833)
      ·
        refine ⟨24721073246606665083504625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32961430995475553444672833 24721073246606665083504625)
        ·
          refine ⟨18540804934954998812628469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24721073246606665083504625 18540804934954998812628469)
          ·
            refine ⟨1738200462652031138683919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18540804934954998812628469 1738200462652031138683919)
            ·
              refine ⟨2607300693978046708025879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738200462652031138683919 2607300693978046708025879)
              ·
                refine ⟨3910951040967070062038819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607300693978046708025879 3910951040967070062038819)
                ·
                  refine ⟨5866426561450605093058229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910951040967070062038819 5866426561450605093058229)
                  ·
                    refine ⟨549977490135994227474209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5866426561450605093058229 549977490135994227474209)
                    ·
                      rfl

theorem cell22_1606616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_1606616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606616 prefixEnd_1606616 := by exact prefixLift 1606616
  have htrace : WordTrace (prefixWord ++ tailWord_1606616) baseStart_1606616 baseEnd_1606616 := by
    simpa [prefixWord, tailWord_1606616, baseEnd_1606616] using wordTrace_append hprefix tailTrace_1606616
  have hstable : (prefixWord ++ tailWord_1606616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606616).length < 2 ^ (prefixWord ++ tailWord_1606616).sum := by decide
  have hdescent : baseEnd_1606616 < baseStart_1606616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606646 : List Nat := [5, 1, 1, 1, 3, 3, 8]
def baseStart_1606646 : Nat := 118140960795 + 1606646 * 2 ^ 59
def prefixEnd_1606646 : Nat := 4983230072969 + 3 ^ 40 * 1606646 * 2
def baseEnd_1606646 : Nat := 20369917027743857378671

theorem tailTrace_1606646 : CollatzResearch.WordTrace tailWord_1606646 prefixEnd_1606646 20369917027743857378671 := by
  unfold tailWord_1606646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662449608587713133521487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39066129158268940090895861 3662449608587713133521487)
  ·
    refine ⟨5493674412881569700282231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3662449608587713133521487 5493674412881569700282231)
    ·
      refine ⟨8240511619322354550423347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493674412881569700282231 8240511619322354550423347)
      ·
        refine ⟨12360767428983531825635021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240511619322354550423347 12360767428983531825635021)
        ·
          refine ⟨4635287785868824434613133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12360767428983531825635021 4635287785868824434613133)
          ·
            refine ⟨1738232919700809162979925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4635287785868824434613133 1738232919700809162979925)
            ·
              refine ⟨20369917027743857378671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1738232919700809162979925 20369917027743857378671)
              ·
                rfl

theorem cell22_1606646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 8].length) (baseStart_1606646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606646 prefixEnd_1606646 := by exact prefixLift 1606646
  have htrace : WordTrace (prefixWord ++ tailWord_1606646) baseStart_1606646 baseEnd_1606646 := by
    simpa [prefixWord, tailWord_1606646, baseEnd_1606646] using wordTrace_append hprefix tailTrace_1606646
  have hstable : (prefixWord ++ tailWord_1606646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606646).length < 2 ^ (prefixWord ++ tailWord_1606646).sum := by decide
  have hdescent : baseEnd_1606646 < baseStart_1606646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606708 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1606708 : Nat := 118140960795 + 1606708 * 2 ^ 59
def prefixEnd_1606708 : Nat := 4983230072969 + 3 ^ 40 * 1606708 * 2
def baseEnd_1606708 : Nat := 183336327872045551391309

theorem tailTrace_1606708 : CollatzResearch.WordTrace tailWord_1606708 prefixEnd_1606708 183336327872045551391309 := by
  unfold tailWord_1606708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29300727531589397362550389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39067636708785863150067185 29300727531589397362550389)
  ·
    refine ⟨2746943206086506002739099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29300727531589397362550389 2746943206086506002739099)
    ·
      refine ⟨4120414809129759004108649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746943206086506002739099 4120414809129759004108649)
      ·
        refine ⟨3090311106847319253081487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4120414809129759004108649 3090311106847319253081487)
        ·
          refine ⟨4635466660270978879622231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090311106847319253081487 4635466660270978879622231)
          ·
            refine ⟨6953199990406468319433347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635466660270978879622231 6953199990406468319433347)
            ·
              refine ⟨10429799985609702479150021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953199990406468319433347 10429799985609702479150021)
              ·
                refine ⟨1955587497301819214840629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10429799985609702479150021 1955587497301819214840629)
                ·
                  refine ⟨183336327872045551391309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955587497301819214840629 183336327872045551391309)
                  ·
                    rfl

theorem cell22_1606708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1606708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606708 prefixEnd_1606708 := by exact prefixLift 1606708
  have htrace : WordTrace (prefixWord ++ tailWord_1606708) baseStart_1606708 baseEnd_1606708 := by
    simpa [prefixWord, tailWord_1606708, baseEnd_1606708] using wordTrace_append hprefix tailTrace_1606708
  have hstable : (prefixWord ++ tailWord_1606708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606708).length < 2 ^ (prefixWord ++ tailWord_1606708).sum := by decide
  have hdescent : baseEnd_1606708 < baseStart_1606708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606712 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 1, 3]
def baseStart_1606712 : Nat := 118140960795 + 1606712 * 2 ^ 59
def prefixEnd_1606712 : Nat := 4983230072969 + 3 ^ 40 * 1606712 * 2
def baseEnd_1606712 : Nat := 550010352897881977073915

theorem tailTrace_1606712 : CollatzResearch.WordTrace tailWord_1606712 prefixEnd_1606712 550010352897881977073915 := by
  unfold tailWord_1606712
  simp only [CollatzResearch.WordTrace]
  refine ⟨29300800477582151704123195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39067733970109535605497593 29300800477582151704123195)
  ·
    refine ⟨43951200716373227556184793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29300800477582151704123195 43951200716373227556184793)
    ·
      refine ⟨32963400537279920667138595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43951200716373227556184793 32963400537279920667138595)
      ·
        refine ⟨49445100805919881000707893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32963400537279920667138595 49445100805919881000707893)
        ·
          refine ⟨4635478200554988843816365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49445100805919881000707893 4635478200554988843816365)
          ·
            refine ⟨1738304325208120816431137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4635478200554988843816365 1738304325208120816431137)
            ·
              refine ⟨1303728243906090612323353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738304325208120816431137 1303728243906090612323353)
              ·
                refine ⟨977796182929567959242515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1303728243906090612323353 977796182929567959242515)
                ·
                  refine ⟨1466694274394351938863773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977796182929567959242515 1466694274394351938863773)
                  ·
                    refine ⟨550010352897881977073915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466694274394351938863773 550010352897881977073915)
                    ·
                      rfl

theorem cell22_1606712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_1606712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606712 prefixEnd_1606712 := by exact prefixLift 1606712
  have htrace : WordTrace (prefixWord ++ tailWord_1606712) baseStart_1606712 baseEnd_1606712 := by
    simpa [prefixWord, tailWord_1606712, baseEnd_1606712] using wordTrace_append hprefix tailTrace_1606712
  have hstable : (prefixWord ++ tailWord_1606712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606712).length < 2 ^ (prefixWord ++ tailWord_1606712).sum := by decide
  have hdescent : baseEnd_1606712 < baseStart_1606712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606719 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 6]
def baseStart_1606719 : Nat := 118140960795 + 1606719 * 2 ^ 59
def prefixEnd_1606719 : Nat := 4983230072969 + 3 ^ 40 * 1606719 * 2
def baseEnd_1606719 : Nat := 183337583046978764049631

theorem tailTrace_1606719 : CollatzResearch.WordTrace tailWord_1606719 prefixEnd_1606719 183337583046978764049631 := by
  unfold tailWord_1606719
  simp only [CollatzResearch.WordTrace]
  refine ⟨58601856266138943603751211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39067904177425962402500807 58601856266138943603751211)
  ·
    refine ⟨87902784399208415405626817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58601856266138943603751211 87902784399208415405626817)
    ·
      refine ⟨65927088299406311554220113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87902784399208415405626817 65927088299406311554220113)
      ·
        refine ⟨49445316224554733665665085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65927088299406311554220113 49445316224554733665665085)
        ·
          refine ⟨18541993584208025124624407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49445316224554733665665085 18541993584208025124624407)
          ·
            refine ⟨27812990376312037686936611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18541993584208025124624407 27812990376312037686936611)
            ·
              refine ⟨41719485564468056530404917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27812990376312037686936611 41719485564468056530404917)
              ·
                refine ⟨3911201771668880299725461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41719485564468056530404917 3911201771668880299725461)
                ·
                  refine ⟨183337583046978764049631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3911201771668880299725461 183337583046978764049631)
                  ·
                    rfl

theorem cell22_1606719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_1606719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606719 prefixEnd_1606719 := by exact prefixLift 1606719
  have htrace : WordTrace (prefixWord ++ tailWord_1606719) baseStart_1606719 baseEnd_1606719 := by
    simpa [prefixWord, tailWord_1606719, baseEnd_1606719] using wordTrace_append hprefix tailTrace_1606719
  have hstable : (prefixWord ++ tailWord_1606719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606719).length < 2 ^ (prefixWord ++ tailWord_1606719).sum := by decide
  have hdescent : baseEnd_1606719 < baseStart_1606719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606751 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 4, 3]
def baseStart_1606751 : Nat := 118140960795 + 1606751 * 2 ^ 59
def prefixEnd_1606751 : Nat := 4983230072969 + 3 ^ 40 * 1606751 * 2
def baseEnd_1606751 : Nat := 550023703394898875348795

theorem tailTrace_1606751 : CollatzResearch.WordTrace tailWord_1606751 prefixEnd_1606751 550023703394898875348795 := by
  unfold tailWord_1606751
  simp only [CollatzResearch.WordTrace]
  refine ⟨58603023402023013068916107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39068682268015342045944071 58603023402023013068916107)
  ·
    refine ⟨87904535103034519603374161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58603023402023013068916107 87904535103034519603374161)
    ·
      refine ⟨65928401327275889702530621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87904535103034519603374161 65928401327275889702530621)
      ·
        refine ⟨24723150497728458638448983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65928401327275889702530621 24723150497728458638448983)
        ·
          refine ⟨37084725746592687957673475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24723150497728458638448983 37084725746592687957673475)
          ·
            refine ⟨55627088619889031936510213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37084725746592687957673475 55627088619889031936510213)
            ·
              refine ⟨10430079116229193488095665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55627088619889031936510213 10430079116229193488095665)
              ·
                refine ⟨7822559337171895116071749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10430079116229193488095665 7822559337171895116071749)
                ·
                  refine ⟨1466729875719730334263453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7822559337171895116071749 1466729875719730334263453)
                  ·
                    refine ⟨550023703394898875348795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466729875719730334263453 550023703394898875348795)
                    ·
                      rfl

theorem cell22_1606751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_1606751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606751 prefixEnd_1606751 := by exact prefixLift 1606751
  have htrace : WordTrace (prefixWord ++ tailWord_1606751) baseStart_1606751 baseEnd_1606751 := by
    simpa [prefixWord, tailWord_1606751, baseEnd_1606751] using wordTrace_append hprefix tailTrace_1606751
  have hstable : (prefixWord ++ tailWord_1606751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606751).length < 2 ^ (prefixWord ++ tailWord_1606751).sum := by decide
  have hdescent : baseEnd_1606751 < baseStart_1606751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606764 : List Nat := [2, 2, 1, 1, 3, 2, 11]
def baseStart_1606764 : Nat := 118140960795 + 1606764 * 2 ^ 59
def prefixEnd_1606764 : Nat := 4983230072969 + 3 ^ 40 * 1606764 * 2
def baseEnd_1606764 : Nat := 20371413094835969436065

theorem tailTrace_1606764 : CollatzResearch.WordTrace tailWord_1606764 prefixEnd_1606764 20371413094835969436065 := by
  unfold tailWord_1606764
  simp only [CollatzResearch.WordTrace]
  refine ⟨29301748775487958144569673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39068998367317277526092897 29301748775487958144569673)
  ·
    refine ⟨21976311581615968608427255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29301748775487958144569673 21976311581615968608427255)
    ·
      refine ⟨32964467372423952912640883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21976311581615968608427255 32964467372423952912640883)
      ·
        refine ⟨49446701058635929368961325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32964467372423952912640883 49446701058635929368961325)
        ·
          refine ⟨18542512896988473513360497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49446701058635929368961325 18542512896988473513360497)
          ·
            refine ⟨13906884672741355135020373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18542512896988473513360497 13906884672741355135020373)
            ·
              refine ⟨20371413094835969436065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13906884672741355135020373 20371413094835969436065)
              ·
                rfl

theorem cell22_1606764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 11].length) (baseStart_1606764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606764 prefixEnd_1606764 := by exact prefixLift 1606764
  have htrace : WordTrace (prefixWord ++ tailWord_1606764) baseStart_1606764 baseEnd_1606764 := by
    simpa [prefixWord, tailWord_1606764, baseEnd_1606764] using wordTrace_append hprefix tailTrace_1606764
  have hstable : (prefixWord ++ tailWord_1606764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606764).length < 2 ^ (prefixWord ++ tailWord_1606764).sum := by decide
  have hdescent : baseEnd_1606764 < baseStart_1606764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606798 : List Nat := [4, 1, 1, 3, 2, 1, 4, 6]
def baseStart_1606798 : Nat := 118140960795 + 1606798 * 2 ^ 59
def prefixEnd_1606798 : Nat := 4983230072969 + 3 ^ 40 * 1606798 * 2
def baseEnd_1606798 : Nat := 61115532495045157713739

theorem tailTrace_1606798 : CollatzResearch.WordTrace tailWord_1606798 prefixEnd_1606798 61115532495045157713739 := by
  unfold tailWord_1606798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325592204106592511984631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39069825088568493397251365 7325592204106592511984631)
  ·
    refine ⟨10988388306159888767976947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7325592204106592511984631 10988388306159888767976947)
    ·
      refine ⟨16482582459239833151965421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10988388306159888767976947 16482582459239833151965421)
      ·
        refine ⟨6180968422214937431987033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16482582459239833151965421 6180968422214937431987033)
        ·
          refine ⟨4635726316661203073990275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6180968422214937431987033 4635726316661203073990275)
          ·
            refine ⟨6953589474991804610985413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635726316661203073990275 6953589474991804610985413)
            ·
              refine ⟨1303798026560963364559765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6953589474991804610985413 1303798026560963364559765)
              ·
                refine ⟨61115532495045157713739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1303798026560963364559765 61115532495045157713739)
                ·
                  rfl

theorem cell22_1606798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_1606798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606798 prefixEnd_1606798 := by exact prefixLift 1606798
  have htrace : WordTrace (prefixWord ++ tailWord_1606798) baseStart_1606798 baseEnd_1606798 := by
    simpa [prefixWord, tailWord_1606798, baseEnd_1606798] using wordTrace_append hprefix tailTrace_1606798
  have hstable : (prefixWord ++ tailWord_1606798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606798).length < 2 ^ (prefixWord ++ tailWord_1606798).sum := by decide
  have hdescent : baseEnd_1606798 < baseStart_1606798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606954 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1606954 : Nat := 118140960795 + 1606954 * 2 ^ 59
def prefixEnd_1606954 : Nat := 4983230072969 + 3 ^ 40 * 1606954 * 2
def baseEnd_1606954 : Nat := 550093194443474012523173

theorem tailTrace_1606954 : CollatzResearch.WordTrace tailWord_1606954 prefixEnd_1606954 550093194443474012523173 := by
  unfold tailWord_1606954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652606855071894684638979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39073618280191719159037277 14652606855071894684638979)
  ·
    refine ⟨21978910282607842026958469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14652606855071894684638979 21978910282607842026958469)
    ·
      refine ⟨4121045677988970380054713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21978910282607842026958469 4121045677988970380054713)
      ·
        refine ⟨3090784258491727785041035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121045677988970380054713 3090784258491727785041035)
        ·
          refine ⟨4636176387737591677561553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090784258491727785041035 4636176387737591677561553)
          ·
            refine ⟨3477132290803193758171165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4636176387737591677561553 3477132290803193758171165)
            ·
              refine ⟨1303924609051197659314187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3477132290803193758171165 1303924609051197659314187)
              ·
                refine ⟨1955886913576796488971281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303924609051197659314187 1955886913576796488971281)
                ·
                  refine ⟨1466915185182597366728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955886913576796488971281 1466915185182597366728461)
                  ·
                    refine ⟨550093194443474012523173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466915185182597366728461 550093194443474012523173)
                    ·
                      rfl

theorem cell22_1606954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1606954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606954 prefixEnd_1606954 := by exact prefixLift 1606954
  have htrace : WordTrace (prefixWord ++ tailWord_1606954) baseStart_1606954 baseEnd_1606954 := by
    simpa [prefixWord, tailWord_1606954, baseEnd_1606954] using wordTrace_append hprefix tailTrace_1606954
  have hstable : (prefixWord ++ tailWord_1606954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606954).length < 2 ^ (prefixWord ++ tailWord_1606954).sum := by decide
  have hdescent : baseEnd_1606954 < baseStart_1606954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606965 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1606965 : Nat := 118140960795 + 1606965 * 2 ^ 59
def prefixEnd_1606965 : Nat := 4983230072969 + 3 ^ 40 * 1606965 * 2
def baseEnd_1606965 : Nat := 550096959968273650498139

theorem tailTrace_1606965 : CollatzResearch.WordTrace tailWord_1606965 prefixEnd_1606965 550096959968273650498139 := by
  unfold tailWord_1606965
  simp only [CollatzResearch.WordTrace]
  refine ⟨58610828623247727617206349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39073885748831818411470899 58610828623247727617206349)
  ·
    refine ⟨21979060733717897856452381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58610828623247727617206349 21979060733717897856452381)
    ·
      refine ⟨8242147775144211696169643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21979060733717897856452381 8242147775144211696169643)
      ·
        refine ⟨12363221662716317544254465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8242147775144211696169643 12363221662716317544254465)
        ·
          refine ⟨9272416247037238158190849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12363221662716317544254465 9272416247037238158190849)
          ·
            refine ⟨6954312185277928618643137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9272416247037238158190849 6954312185277928618643137)
            ·
              refine ⟨5215734138958446463982353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954312185277928618643137 5215734138958446463982353)
              ·
                refine ⟨3911800604218834847986765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5215734138958446463982353 3911800604218834847986765)
                ·
                  refine ⟨1466925226582063067995037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3911800604218834847986765 1466925226582063067995037)
                  ·
                    refine ⟨550096959968273650498139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466925226582063067995037 550096959968273650498139)
                    ·
                      rfl

theorem cell22_1606965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1606965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606965 prefixEnd_1606965 := by exact prefixLift 1606965
  have htrace : WordTrace (prefixWord ++ tailWord_1606965) baseStart_1606965 baseEnd_1606965 := by
    simpa [prefixWord, tailWord_1606965, baseEnd_1606965] using wordTrace_append hprefix tailTrace_1606965
  have hstable : (prefixWord ++ tailWord_1606965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606965).length < 2 ^ (prefixWord ++ tailWord_1606965).sum := by decide
  have hdescent : baseEnd_1606965 < baseStart_1606965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606991 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1606991 : Nat := 118140960795 + 1606991 * 2 ^ 59
def prefixEnd_1606991 : Nat := 4983230072969 + 3 ^ 40 * 1606991 * 2
def baseEnd_1606991 : Nat := 550105860299618249348059

theorem tailTrace_1606991 : CollatzResearch.WordTrace tailWord_1606991 prefixEnd_1606991 550105860299618249348059 := by
  unfold tailWord_1606991
  simp only [CollatzResearch.WordTrace]
  refine ⟨58611776921153534057652827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39074517947435689371768551 58611776921153534057652827)
  ·
    refine ⟨87917665381730301086479241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58611776921153534057652827 87917665381730301086479241)
    ·
      refine ⟨65938249036297725814859431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87917665381730301086479241 65938249036297725814859431)
      ·
        refine ⟨98907373554446588722289147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65938249036297725814859431 98907373554446588722289147)
        ·
          refine ⟨148361060331669883083433721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98907373554446588722289147 148361060331669883083433721)
          ·
            refine ⟨111270795248752412312575291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148361060331669883083433721 111270795248752412312575291)
            ·
              refine ⟨166906192873128618468862937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111270795248752412312575291 166906192873128618468862937)
              ·
                refine ⟨125179644654846463851647203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166906192873128618468862937 125179644654846463851647203)
                ·
                  refine ⟨187769466982269695777470805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125179644654846463851647203 187769466982269695777470805)
                  ·
                    refine ⟨550105860299618249348059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 187769466982269695777470805 550105860299618249348059)
                    ·
                      rfl

theorem cell22_1606991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1606991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606991 prefixEnd_1606991 := by exact prefixLift 1606991
  have htrace : WordTrace (prefixWord ++ tailWord_1606991) baseStart_1606991 baseEnd_1606991 := by
    simpa [prefixWord, tailWord_1606991, baseEnd_1606991] using wordTrace_append hprefix tailTrace_1606991
  have hstable : (prefixWord ++ tailWord_1606991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606991).length < 2 ^ (prefixWord ++ tailWord_1606991).sum := by decide
  have hdescent : baseEnd_1606991 < baseStart_1606991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606999 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 1, 3]
def baseStart_1606999 : Nat := 118140960795 + 1606999 * 2 ^ 59
def prefixEnd_1606999 : Nat := 4983230072969 + 3 ^ 40 * 1606999 * 2
def baseEnd_1606999 : Nat := 550108598863108895148035

theorem tailTrace_1606999 : CollatzResearch.WordTrace tailWord_1606999 prefixEnd_1606999 550108598863108895148035 := by
  unfold tailWord_1606999
  simp only [CollatzResearch.WordTrace]
  refine ⟨58612068705124551423944051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39074712470083034282629367 58612068705124551423944051)
  ·
    refine ⟨87918103057686827135916077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58612068705124551423944051 87918103057686827135916077)
    ·
      refine ⟨32969288646632560175968529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87918103057686827135916077 32969288646632560175968529)
      ·
        refine ⟨24726966484974420131976397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32969288646632560175968529 24726966484974420131976397)
        ·
          refine ⟨9272612431865407549491149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24726966484974420131976397 9272612431865407549491149)
          ·
            refine ⟨3477229661949527831059181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9272612431865407549491149 3477229661949527831059181)
            ·
              refine ⟨1303961123231072936647193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3477229661949527831059181 1303961123231072936647193)
              ·
                refine ⟨977970842423304702485395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1303961123231072936647193 977970842423304702485395)
                ·
                  refine ⟨1466956263634957053728093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977970842423304702485395 1466956263634957053728093)
                  ·
                    refine ⟨550108598863108895148035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466956263634957053728093 550108598863108895148035)
                    ·
                      rfl

theorem cell22_1606999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_1606999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606999 prefixEnd_1606999 := by exact prefixLift 1606999
  have htrace : WordTrace (prefixWord ++ tailWord_1606999) baseStart_1606999 baseEnd_1606999 := by
    simpa [prefixWord, tailWord_1606999, baseEnd_1606999] using wordTrace_append hprefix tailTrace_1606999
  have hstable : (prefixWord ++ tailWord_1606999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606999).length < 2 ^ (prefixWord ++ tailWord_1606999).sum := by decide
  have hdescent : baseEnd_1606999 < baseStart_1606999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607005 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1607005 : Nat := 118140960795 + 1607005 * 2 ^ 59
def prefixEnd_1607005 : Nat := 4983230072969 + 3 ^ 40 * 1607005 * 2
def baseEnd_1607005 : Nat := 550110652785726879498017

theorem tailTrace_1607005 : CollatzResearch.WordTrace tailWord_1607005 prefixEnd_1607005 550110652785726879498017 := by
  unfold tailWord_1607005
  simp only [CollatzResearch.WordTrace]
  refine ⟨58612287543102814448662469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39074858362068542965774979 58612287543102814448662469)
  ·
    refine ⟨10989803914331777709124213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58612287543102814448662469 10989803914331777709124213)
    ·
      refine ⟨1030294116968604160230395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10989803914331777709124213 1030294116968604160230395)
      ·
        refine ⟨1545441175452906240345593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030294116968604160230395 1545441175452906240345593)
        ·
          refine ⟨1159080881589679680259195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1545441175452906240345593 1159080881589679680259195)
          ·
            refine ⟨1738621322384519520388793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159080881589679680259195 1738621322384519520388793)
            ·
              refine ⟨1303965991788389640291595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738621322384519520388793 1303965991788389640291595)
              ·
                refine ⟨1955948987682584460437393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303965991788389640291595 1955948987682584460437393)
                ·
                  refine ⟨1466961740761938345328045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955948987682584460437393 1466961740761938345328045)
                  ·
                    refine ⟨550110652785726879498017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466961740761938345328045 550110652785726879498017)
                    ·
                      rfl

theorem cell22_1607005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1607005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607005 prefixEnd_1607005 := by exact prefixLift 1607005
  have htrace : WordTrace (prefixWord ++ tailWord_1607005) baseStart_1607005 baseEnd_1607005 := by
    simpa [prefixWord, tailWord_1607005, baseEnd_1607005] using wordTrace_append hprefix tailTrace_1607005
  have hstable : (prefixWord ++ tailWord_1607005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607005).length < 2 ^ (prefixWord ++ tailWord_1607005).sum := by decide
  have hdescent : baseEnd_1607005 < baseStart_1607005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607012 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1607012 : Nat := 118140960795 + 1607012 * 2 ^ 59
def prefixEnd_1607012 : Nat := 4983230072969 + 3 ^ 40 * 1607012 * 2
def baseEnd_1607012 : Nat := 183371016342927064857665

theorem tailTrace_1607012 : CollatzResearch.WordTrace tailWord_1607012 prefixEnd_1607012 183371016342927064857665 := by
  unfold tailWord_1607012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29306271427038727322083645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39075028569384969762778193 29306271427038727322083645)
  ·
    refine ⟨10989851785139522745781367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29306271427038727322083645 10989851785139522745781367)
    ·
      refine ⟨16484777677709284118672051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10989851785139522745781367 16484777677709284118672051)
      ·
        refine ⟨24727166516563926178008077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16484777677709284118672051 24727166516563926178008077)
        ·
          refine ⟨9272687443711472316753029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24727166516563926178008077 9272687443711472316753029)
          ·
            refine ⟨1738628895695901059391193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9272687443711472316753029 1738628895695901059391193)
            ·
              refine ⟨1303971671771925794543395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738628895695901059391193 1303971671771925794543395)
              ·
                refine ⟨1955957507657888691815093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303971671771925794543395 1955957507657888691815093)
                ·
                  refine ⟨183371016342927064857665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955957507657888691815093 183371016342927064857665)
                  ·
                    rfl

theorem cell22_1607012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1607012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607012 prefixEnd_1607012 := by exact prefixLift 1607012
  have htrace : WordTrace (prefixWord ++ tailWord_1607012) baseStart_1607012 baseEnd_1607012 := by
    simpa [prefixWord, tailWord_1607012, baseEnd_1607012] using wordTrace_append hprefix tailTrace_1607012
  have hstable : (prefixWord ++ tailWord_1607012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607012).length < 2 ^ (prefixWord ++ tailWord_1607012).sum := by decide
  have hdescent : baseEnd_1607012 < baseStart_1607012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607025 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1607025 : Nat := 118140960795 + 1607025 * 2 ^ 59
def prefixEnd_1607025 : Nat := 4983230072969 + 3 ^ 40 * 1607025 * 2
def baseEnd_1607025 : Nat := 550117499194453493997955

theorem tailTrace_1607025 : CollatzResearch.WordTrace tailWord_1607025 prefixEnd_1607025 550117499194453493997955 := by
  unfold tailWord_1607025
  simp only [CollatzResearch.WordTrace]
  refine ⟨58613017003030357864390529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39075344668686905242927019 58613017003030357864390529)
  ·
    refine ⟨43959762752272768398292897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58613017003030357864390529 43959762752272768398292897)
    ·
      refine ⟨32969822064204576298719673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43959762752272768398292897 32969822064204576298719673)
      ·
        refine ⟨24727366548153432224039755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32969822064204576298719673 24727366548153432224039755)
        ·
          refine ⟨37091049822230148336059633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24727366548153432224039755 37091049822230148336059633)
          ·
            refine ⟨27818287366672611252044725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37091049822230148336059633 27818287366672611252044725)
            ·
              refine ⟨2607964440625557304879193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27818287366672611252044725 2607964440625557304879193)
              ·
                refine ⟨1955973330469167978659395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607964440625557304879193 1955973330469167978659395)
                ·
                  refine ⟨2933959995703751967989093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955973330469167978659395 2933959995703751967989093)
                  ·
                    refine ⟨550117499194453493997955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933959995703751967989093 550117499194453493997955)
                    ·
                      rfl

theorem cell22_1607025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1607025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607025 prefixEnd_1607025 := by exact prefixLift 1607025
  have htrace : WordTrace (prefixWord ++ tailWord_1607025) baseStart_1607025 baseEnd_1607025 := by
    simpa [prefixWord, tailWord_1607025, baseEnd_1607025] using wordTrace_append hprefix tailTrace_1607025
  have hstable : (prefixWord ++ tailWord_1607025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607025).length < 2 ^ (prefixWord ++ tailWord_1607025).sum := by decide
  have hdescent : baseEnd_1607025 < baseStart_1607025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607181 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1607181 : Nat := 118140960795 + 1607181 * 2 ^ 59
def prefixEnd_1607181 : Nat := 4983230072969 + 3 ^ 40 * 1607181 * 2
def baseEnd_1607181 : Nat := 183390300394173695699159

theorem tailTrace_1607181 : CollatzResearch.WordTrace tailWord_1607181 prefixEnd_1607181 183390300394173695699159 := by
  unfold tailWord_1607181
  simp only [CollatzResearch.WordTrace]
  refine ⟨58618706790465196507069397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39079137860310131004712931 58618706790465196507069397)
  ·
    refine ⟨1373875940401528043134439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 58618706790465196507069397 1373875940401528043134439)
    ·
      refine ⟨2060813910602292064701659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373875940401528043134439 2060813910602292064701659)
      ·
        refine ⟨3091220865903438097052489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060813910602292064701659 3091220865903438097052489)
        ·
          refine ⟨2318415649427578572789367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091220865903438097052489 2318415649427578572789367)
          ·
            refine ⟨3477623474141367859184051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318415649427578572789367 3477623474141367859184051)
            ·
              refine ⟨5216435211212051788776077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477623474141367859184051 5216435211212051788776077)
              ·
                refine ⟨1956163204204519420791029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5216435211212051788776077 1956163204204519420791029)
                ·
                  refine ⟨183390300394173695699159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956163204204519420791029 183390300394173695699159)
                  ·
                    rfl

theorem cell22_1607181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1607181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607181 prefixEnd_1607181 := by exact prefixLift 1607181
  have htrace : WordTrace (prefixWord ++ tailWord_1607181) baseStart_1607181 baseEnd_1607181 := by
    simpa [prefixWord, tailWord_1607181, baseEnd_1607181] using wordTrace_append hprefix tailTrace_1607181
  have hstable : (prefixWord ++ tailWord_1607181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607181).length < 2 ^ (prefixWord ++ tailWord_1607181).sum := by decide
  have hdescent : baseEnd_1607181 < baseStart_1607181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607220 : List Nat := [2, 5, 1, 14]
def baseStart_1607220 : Nat := 118140960795 + 1607220 * 2 ^ 59
def prefixEnd_1607220 : Nat := 4983230072969 + 3 ^ 40 * 1607220 * 2
def baseEnd_1607220 : Nat := 754710907653687222733

theorem tailTrace_1607220 : CollatzResearch.WordTrace tailWord_1607220 prefixEnd_1607220 754710907653687222733 := by
  unfold tailWord_1607220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310064618661953083869557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39080086158215937445159409 29310064618661953083869557)
  ·
    refine ⟨2747818557999558101612771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29310064618661953083869557 2747818557999558101612771)
    ·
      refine ⟨4121727836999337152419157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747818557999558101612771 4121727836999337152419157)
      ·
        refine ⟨754710907653687222733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 4121727836999337152419157 754710907653687222733)
        ·
          rfl

theorem cell22_1607220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 14].length) (baseStart_1607220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607220 prefixEnd_1607220 := by exact prefixLift 1607220
  have htrace : WordTrace (prefixWord ++ tailWord_1607220) baseStart_1607220 baseEnd_1607220 := by
    simpa [prefixWord, tailWord_1607220, baseEnd_1607220] using wordTrace_append hprefix tailTrace_1607220
  have hstable : (prefixWord ++ tailWord_1607220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607220).length < 2 ^ (prefixWord ++ tailWord_1607220).sum := by decide
  have hdescent : baseEnd_1607220 < baseStart_1607220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607224 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_1607224 : Nat := 118140960795 + 1607224 * 2 ^ 59
def prefixEnd_1607224 : Nat := 4983230072969 + 3 ^ 40 * 1607224 * 2
def baseEnd_1607224 : Nat := 550185620961283308272345

theorem tailTrace_1607224 : CollatzResearch.WordTrace tailWord_1607224 prefixEnd_1607224 550185620961283308272345 := by
  unfold tailWord_1607224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310137564654707425442363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39080183419539609900589817 29310137564654707425442363)
  ·
    refine ⟨43965206346982061138163545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29310137564654707425442363 43965206346982061138163545)
    ·
      refine ⟨32973904760236545853622659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43965206346982061138163545 32973904760236545853622659)
      ·
        refine ⟨49460857140354818780433989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32973904760236545853622659 49460857140354818780433989)
        ·
          refine ⟨9273910713816528521331373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49460857140354818780433989 9273910713816528521331373)
          ·
            refine ⟨3477716517681198195499265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9273910713816528521331373 3477716517681198195499265)
            ·
              refine ⟨2608287388260898646624449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477716517681198195499265 2608287388260898646624449)
              ·
                refine ⟨1956215541195673984968337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608287388260898646624449 1956215541195673984968337)
                ·
                  refine ⟨1467161655896755488726253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956215541195673984968337 1467161655896755488726253)
                  ·
                    refine ⟨550185620961283308272345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467161655896755488726253 550185620961283308272345)
                    ·
                      rfl

theorem cell22_1607224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_1607224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607224 prefixEnd_1607224 := by exact prefixLift 1607224
  have htrace : WordTrace (prefixWord ++ tailWord_1607224) baseStart_1607224 baseEnd_1607224 := by
    simpa [prefixWord, tailWord_1607224, baseEnd_1607224] using wordTrace_append hprefix tailTrace_1607224
  have hstable : (prefixWord ++ tailWord_1607224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607224).length < 2 ^ (prefixWord ++ tailWord_1607224).sum := by decide
  have hdescent : baseEnd_1607224 < baseStart_1607224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607265 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 7]
def baseStart_1607265 : Nat := 118140960795 + 1607265 * 2 ^ 59
def prefixEnd_1607265 : Nat := 4983230072969 + 3 ^ 40 * 1607265 * 2
def baseEnd_1607265 : Nat := 183399885366390955999073

theorem tailTrace_1607265 : CollatzResearch.WordTrace tailWord_1607265 prefixEnd_1607265 183399885366390955999073 := by
  unfold tailWord_1607265
  simp only [CollatzResearch.WordTrace]
  refine ⟨58621770522160878853127249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39081180348107252568751499 58621770522160878853127249)
  ·
    refine ⟨43966327891620659139845437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58621770522160878853127249 43966327891620659139845437)
    ·
      refine ⟨16487372959357747177442039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43966327891620659139845437 16487372959357747177442039)
      ·
        refine ⟨24731059439036620766163059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16487372959357747177442039 24731059439036620766163059)
        ·
          refine ⟨37096589158554931149244589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24731059439036620766163059 37096589158554931149244589)
          ·
            refine ⟨13911220934458099180966721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37096589158554931149244589 13911220934458099180966721)
            ·
              refine ⟨10433415700843574385725041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13911220934458099180966721 10433415700843574385725041)
              ·
                refine ⟨7825061775632680789293781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10433415700843574385725041 7825061775632680789293781)
                ·
                  refine ⟨183399885366390955999073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7825061775632680789293781 183399885366390955999073)
                  ·
                    rfl

theorem cell22_1607265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_1607265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607265 prefixEnd_1607265 := by exact prefixLift 1607265
  have htrace : WordTrace (prefixWord ++ tailWord_1607265) baseStart_1607265 baseEnd_1607265 := by
    simpa [prefixWord, tailWord_1607265, baseEnd_1607265] using wordTrace_append hprefix tailTrace_1607265
  have hstable : (prefixWord ++ tailWord_1607265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607265).length < 2 ^ (prefixWord ++ tailWord_1607265).sum := by decide
  have hdescent : baseEnd_1607265 < baseStart_1607265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607282 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1607282 : Nat := 118140960795 + 1607282 * 2 ^ 59
def prefixEnd_1607282 : Nat := 4983230072969 + 3 ^ 40 * 1607282 * 2
def baseEnd_1607282 : Nat := 183401825182196830107389

theorem tailTrace_1607282 : CollatzResearch.WordTrace tailWord_1607282 prefixEnd_1607282 183401825182196830107389 := by
  unfold tailWord_1607282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655597640774822689124025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39081593708732860504330733 14655597640774822689124025)
  ·
    refine ⟨10991698230581117016843019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14655597640774822689124025 10991698230581117016843019)
    ·
      refine ⟨16487547345871675525264529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991698230581117016843019 16487547345871675525264529)
      ·
        refine ⟨12365660509403756643948397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16487547345871675525264529 12365660509403756643948397)
        ·
          refine ⟨4637122691026408741480649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12365660509403756643948397 4637122691026408741480649)
          ·
            refine ⟨3477842018269806556110487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4637122691026408741480649 3477842018269806556110487)
            ·
              refine ⟨5216763027404709834165731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477842018269806556110487 5216763027404709834165731)
              ·
                refine ⟨7825144541107064751248597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216763027404709834165731 7825144541107064751248597)
                ·
                  refine ⟨183401825182196830107389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7825144541107064751248597 183401825182196830107389)
                  ·
                    rfl

theorem cell22_1607282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1607282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607282 prefixEnd_1607282 := by exact prefixLift 1607282
  have htrace : WordTrace (prefixWord ++ tailWord_1607282) baseStart_1607282 baseEnd_1607282 := by
    simpa [prefixWord, tailWord_1607282, baseEnd_1607282] using wordTrace_append hprefix tailTrace_1607282
  have hstable : (prefixWord ++ tailWord_1607282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607282).length < 2 ^ (prefixWord ++ tailWord_1607282).sum := by decide
  have hdescent : baseEnd_1607282 < baseStart_1607282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607286 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_1607286 : Nat := 118140960795 + 1607286 * 2 ^ 59
def prefixEnd_1607286 : Nat := 4983230072969 + 3 ^ 40 * 1607286 * 2
def baseEnd_1607286 : Nat := 550206844828335813222155

theorem tailTrace_1607286 : CollatzResearch.WordTrace tailWord_1607286 prefixEnd_1607286 550206844828335813222155 := by
  unfold tailWord_1607286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663908528442799964977607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39081690970056532959761141 3663908528442799964977607)
  ·
    refine ⟨5495862792664199947466411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663908528442799964977607 5495862792664199947466411)
    ·
      refine ⟨8243794188996299921199617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495862792664199947466411 8243794188996299921199617)
      ·
        refine ⟨6182845641747224940899713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8243794188996299921199617 6182845641747224940899713)
        ·
          refine ⟨4637134231310418705674785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6182845641747224940899713 4637134231310418705674785)
          ·
            refine ⟨3477850673482814029256089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4637134231310418705674785 3477850673482814029256089)
            ·
              refine ⟨2608388005112110521942067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477850673482814029256089 2608388005112110521942067)
              ·
                refine ⟨3912582007668165782913101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608388005112110521942067 3912582007668165782913101)
                ·
                  refine ⟨1467218252875562168592413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3912582007668165782913101 1467218252875562168592413)
                  ·
                    refine ⟨550206844828335813222155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467218252875562168592413 550206844828335813222155)
                    ·
                      rfl

theorem cell22_1607286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_1607286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607286 prefixEnd_1607286 := by exact prefixLift 1607286
  have htrace : WordTrace (prefixWord ++ tailWord_1607286) baseStart_1607286 baseEnd_1607286 := by
    simpa [prefixWord, tailWord_1607286, baseEnd_1607286] using wordTrace_append hprefix tailTrace_1607286
  have hstable : (prefixWord ++ tailWord_1607286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607286).length < 2 ^ (prefixWord ++ tailWord_1607286).sum := by decide
  have hdescent : baseEnd_1607286 < baseStart_1607286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607297 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1607297 : Nat := 118140960795 + 1607297 * 2 ^ 59
def prefixEnd_1607297 : Nat := 4983230072969 + 3 ^ 40 * 1607297 * 2
def baseEnd_1607297 : Nat := 550210610353135451197121

theorem tailTrace_1607297 : CollatzResearch.WordTrace tailWord_1607297 prefixEnd_1607297 550210610353135451197121 := by
  unfold tailWord_1607297
  simp only [CollatzResearch.WordTrace]
  refine ⟨58622937658044948318292145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39081958438696632212194763 58622937658044948318292145)
  ·
    refine ⟨43967203243533711238719109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58622937658044948318292145 43967203243533711238719109)
    ·
      refine ⟨8243850608162570857259833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43967203243533711238719109 8243850608162570857259833)
      ·
        refine ⟨6182887956121928142944875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8243850608162570857259833 6182887956121928142944875)
        ·
          refine ⟨9274331934182892214417313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182887956121928142944875 9274331934182892214417313)
          ·
            refine ⟨6955748950637169160812985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9274331934182892214417313 6955748950637169160812985)
            ·
              refine ⟨5216811712977876870609739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955748950637169160812985 5216811712977876870609739)
              ·
                refine ⟨7825217569466815305914609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216811712977876870609739 7825217569466815305914609)
                ·
                  refine ⟨5868913177100111479435957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7825217569466815305914609 5868913177100111479435957)
                  ·
                    refine ⟨550210610353135451197121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5868913177100111479435957 550210610353135451197121)
                    ·
                      rfl

theorem cell22_1607297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1607297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607297 prefixEnd_1607297 := by exact prefixLift 1607297
  have htrace : WordTrace (prefixWord ++ tailWord_1607297) baseStart_1607297 baseEnd_1607297 := by
    simpa [prefixWord, tailWord_1607297, baseEnd_1607297] using wordTrace_append hprefix tailTrace_1607297
  have hstable : (prefixWord ++ tailWord_1607297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607297).length < 2 ^ (prefixWord ++ tailWord_1607297).sum := by decide
  have hdescent : baseEnd_1607297 < baseStart_1607297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607329 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1607329 : Nat := 118140960795 + 1607329 * 2 ^ 59
def prefixEnd_1607329 : Nat := 4983230072969 + 3 ^ 40 * 1607329 * 2
def baseEnd_1607329 : Nat := 550221564607098034397023

theorem tailTrace_1607329 : CollatzResearch.WordTrace tailWord_1607329 prefixEnd_1607329 550221564607098034397023 := by
  unfold tailWord_1607329
  simp only [CollatzResearch.WordTrace]
  refine ⟨58624104793929017783457041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39082736529286011855638027 58624104793929017783457041)
  ·
    refine ⟨43968078595446763337592781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58624104793929017783457041 43968078595446763337592781)
    ·
      refine ⟨16488029473292536251597293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43968078595446763337592781 16488029473292536251597293)
      ·
        refine ⟨6183011052484701094348985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16488029473292536251597293 6183011052484701094348985)
        ·
          refine ⟨4637258289363525820761739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6183011052484701094348985 4637258289363525820761739)
          ·
            refine ⟨6955887434045288731142609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637258289363525820761739 6955887434045288731142609)
            ·
              refine ⟨5216915575533966548356957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955887434045288731142609 5216915575533966548356957)
              ·
                refine ⟨1956343340825237455633859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5216915575533966548356957 1956343340825237455633859)
                ·
                  refine ⟨2934515011237856183450789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956343340825237455633859 2934515011237856183450789)
                  ·
                    refine ⟨550221564607098034397023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934515011237856183450789 550221564607098034397023)
                    ·
                      rfl

theorem cell22_1607329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1607329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607329 prefixEnd_1607329 := by exact prefixLift 1607329
  have htrace : WordTrace (prefixWord ++ tailWord_1607329) baseStart_1607329 baseEnd_1607329 := by
    simpa [prefixWord, tailWord_1607329, baseEnd_1607329] using wordTrace_append hprefix tailTrace_1607329
  have hstable : (prefixWord ++ tailWord_1607329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607329).length < 2 ^ (prefixWord ++ tailWord_1607329).sum := by decide
  have hdescent : baseEnd_1607329 < baseStart_1607329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607340 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1607340 : Nat := 118140960795 + 1607340 * 2 ^ 59
def prefixEnd_1607340 : Nat := 4983230072969 + 3 ^ 40 * 1607340 * 2
def baseEnd_1607340 : Nat := 550225330131897672371989

theorem tailTrace_1607340 : CollatzResearch.WordTrace tailWord_1607340 prefixEnd_1607340 550225330131897672371989 := by
  unfold tailWord_1607340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29312252998444583331053737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39083003997926111108071649 29312252998444583331053737)
  ·
    refine ⟨21984189748833437498290303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29312252998444583331053737 21984189748833437498290303)
    ·
      refine ⟨32976284623250156247435455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21984189748833437498290303 32976284623250156247435455)
      ·
        refine ⟨49464426934875234371153183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32976284623250156247435455 49464426934875234371153183)
        ·
          refine ⟨74196640402312851556729775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49464426934875234371153183 74196640402312851556729775)
          ·
            refine ⟨111294960603469277335094663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74196640402312851556729775 111294960603469277335094663)
            ·
              refine ⟨166942440905203916002641995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111294960603469277335094663 166942440905203916002641995)
              ·
                refine ⟨250413661357805874003962993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166942440905203916002641995 250413661357805874003962993)
                ·
                  refine ⟨187810246018354405502972245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250413661357805874003962993 187810246018354405502972245)
                  ·
                    refine ⟨550225330131897672371989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 187810246018354405502972245 550225330131897672371989)
                    ·
                      rfl

theorem cell22_1607340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1607340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607340 prefixEnd_1607340 := by exact prefixLift 1607340
  have htrace : WordTrace (prefixWord ++ tailWord_1607340) baseStart_1607340 baseEnd_1607340 := by
    simpa [prefixWord, tailWord_1607340, baseEnd_1607340] using wordTrace_append hprefix tailTrace_1607340
  have hstable : (prefixWord ++ tailWord_1607340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607340).length < 2 ^ (prefixWord ++ tailWord_1607340).sum := by decide
  have hdescent : baseEnd_1607340 < baseStart_1607340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607357 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1607357 : Nat := 118140960795 + 1607357 * 2 ^ 59
def prefixEnd_1607357 : Nat := 4983230072969 + 3 ^ 40 * 1607357 * 2
def baseEnd_1607357 : Nat := 550231149579315294696937

theorem tailTrace_1607357 : CollatzResearch.WordTrace tailWord_1607357 prefixEnd_1607357 550231149579315294696937 := by
  unfold tailWord_1607357
  simp only [CollatzResearch.WordTrace]
  refine ⟨58625126037827578565476325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39083417358551719043650883 58625126037827578565476325)
  ·
    refine ⟨10992211132092670981026811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58625126037827578565476325 10992211132092670981026811)
    ·
      refine ⟨16488316698139006471540217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10992211132092670981026811 16488316698139006471540217)
      ·
        refine ⟨12366237523604254853655163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16488316698139006471540217 12366237523604254853655163)
        ·
          refine ⟨18549356285406382280482745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12366237523604254853655163 18549356285406382280482745)
          ·
            refine ⟨13912017214054786710362059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18549356285406382280482745 13912017214054786710362059)
            ·
              refine ⟨20868025821082180065543089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13912017214054786710362059 20868025821082180065543089)
              ·
                refine ⟨15651019365811635049157317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20868025821082180065543089 15651019365811635049157317)
                ·
                  refine ⟨2934566131089681571716997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15651019365811635049157317 2934566131089681571716997)
                  ·
                    refine ⟨550231149579315294696937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934566131089681571716997 550231149579315294696937)
                    ·
                      rfl

theorem cell22_1607357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1607357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607357 prefixEnd_1607357 := by exact prefixLift 1607357
  have htrace : WordTrace (prefixWord ++ tailWord_1607357) baseStart_1607357 baseEnd_1607357 := by
    simpa [prefixWord, tailWord_1607357, baseEnd_1607357] using wordTrace_append hprefix tailTrace_1607357
  have hstable : (prefixWord ++ tailWord_1607357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607357).length < 2 ^ (prefixWord ++ tailWord_1607357).sum := by decide
  have hdescent : baseEnd_1607357 < baseStart_1607357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607359 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 2, 3]
def baseStart_1607359 : Nat := 118140960795 + 1607359 * 2 ^ 59
def prefixEnd_1607359 : Nat := 4983230072969 + 3 ^ 40 * 1607359 * 2
def baseEnd_1607359 : Nat := 550231834220187956146931

theorem tailTrace_1607359 : CollatzResearch.WordTrace tailWord_1607359 prefixEnd_1607359 550231834220187956146931 := by
  unfold tailWord_1607359
  simp only [CollatzResearch.WordTrace]
  refine ⟨58625198983820332907049131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39083465989213555271366087 58625198983820332907049131)
  ·
    refine ⟨87937798475730499360573697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58625198983820332907049131 87937798475730499360573697)
    ·
      refine ⟨65953348856797874520430273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87937798475730499360573697 65953348856797874520430273)
      ·
        refine ⟨49465011642598405890322705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65953348856797874520430273 49465011642598405890322705)
        ·
          refine ⟨37098758731948804417742029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49465011642598405890322705 37098758731948804417742029)
          ·
            refine ⟨13912034524480801656653261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37098758731948804417742029 13912034524480801656653261)
            ·
              refine ⟨5217012946680300621244973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13912034524480801656653261 5217012946680300621244973)
              ·
                refine ⟨1956379855005112732966865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5217012946680300621244973 1956379855005112732966865)
                ·
                  refine ⟨1467284891253834549725149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956379855005112732966865 1467284891253834549725149)
                  ·
                    refine ⟨550231834220187956146931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467284891253834549725149 550231834220187956146931)
                    ·
                      rfl

theorem cell22_1607359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_1607359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607359 prefixEnd_1607359 := by exact prefixLift 1607359
  have htrace : WordTrace (prefixWord ++ tailWord_1607359) baseStart_1607359 baseEnd_1607359 := by
    simpa [prefixWord, tailWord_1607359, baseEnd_1607359] using wordTrace_append hprefix tailTrace_1607359
  have hstable : (prefixWord ++ tailWord_1607359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607359).length < 2 ^ (prefixWord ++ tailWord_1607359).sum := by decide
  have hdescent : baseEnd_1607359 < baseStart_1607359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607374 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1607374 : Nat := 118140960795 + 1607374 * 2 ^ 59
def prefixEnd_1607374 : Nat := 4983230072969 + 3 ^ 40 * 1607374 * 2
def baseEnd_1607374 : Nat := 550236969026732917021885

theorem tailTrace_1607374 : CollatzResearch.WordTrace tailWord_1607374 prefixEnd_1607374 550236969026732917021885 := by
  unfold tailWord_1607374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328218259845748808605647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39083830719177326979230117 7328218259845748808605647)
  ·
    refine ⟨10992327389768623212908471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7328218259845748808605647 10992327389768623212908471)
    ·
      refine ⟨16488491084652934819362707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10992327389768623212908471 16488491084652934819362707)
      ·
        refine ⟨24732736626979402229044061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16488491084652934819362707 24732736626979402229044061)
        ·
          refine ⟨9274776235117275835891523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24732736626979402229044061 9274776235117275835891523)
          ·
            refine ⟨13912164352675913753837285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274776235117275835891523 13912164352675913753837285)
            ·
              refine ⟨2608530816126733828844491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13912164352675913753837285 2608530816126733828844491)
              ·
                refine ⟨3912796224190100743266737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608530816126733828844491 3912796224190100743266737)
                ·
                  refine ⟨2934597168142575557450053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912796224190100743266737 2934597168142575557450053)
                  ·
                    refine ⟨550236969026732917021885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934597168142575557450053 550236969026732917021885)
                    ·
                      rfl

theorem cell22_1607374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1607374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607374 prefixEnd_1607374 := by exact prefixLift 1607374
  have htrace : WordTrace (prefixWord ++ tailWord_1607374) baseStart_1607374 baseEnd_1607374 := by
    simpa [prefixWord, tailWord_1607374, baseEnd_1607374] using wordTrace_append hprefix tailTrace_1607374
  have hstable : (prefixWord ++ tailWord_1607374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607374).length < 2 ^ (prefixWord ++ tailWord_1607374).sum := by decide
  have hdescent : baseEnd_1607374 < baseStart_1607374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607389 : List Nat := [1, 4, 3, 3, 1, 10]
def baseStart_1607389 : Nat := 118140960795 + 1607389 * 2 ^ 59
def prefixEnd_1607389 : Nat := 4983230072969 + 3 ^ 40 * 1607389 * 2
def baseEnd_1607389 : Nat := 6793112393003430591319

theorem tailTrace_1607389 : CollatzResearch.WordTrace tailWord_1607389 prefixEnd_1607389 6793112393003430591319 := by
  unfold tailWord_1607389
  simp only [CollatzResearch.WordTrace]
  refine ⟨58626293173711648030641221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39084195449141098687094147 58626293173711648030641221)
  ·
    refine ⟨10992429970070934005745229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58626293173711648030641221 10992429970070934005745229)
    ·
      refine ⟨4122161238776600252154461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10992429970070934005745229 4122161238776600252154461)
      ·
        refine ⟨1545810464541225094557923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4122161238776600252154461 1545810464541225094557923)
        ·
          refine ⟨2318715696811837641836885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545810464541225094557923 2318715696811837641836885)
          ·
            refine ⟨6793112393003430591319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2318715696811837641836885 6793112393003430591319)
            ·
              rfl

theorem cell22_1607389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 10].length) (baseStart_1607389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607389 prefixEnd_1607389 := by exact prefixLift 1607389
  have htrace : WordTrace (prefixWord ++ tailWord_1607389) baseStart_1607389 baseEnd_1607389 := by
    simpa [prefixWord, tailWord_1607389, baseEnd_1607389] using wordTrace_append hprefix tailTrace_1607389
  have hstable : (prefixWord ++ tailWord_1607389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607389).length < 2 ^ (prefixWord ++ tailWord_1607389).sum := by decide
  have hdescent : baseEnd_1607389 < baseStart_1607389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607395 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 4]
def baseStart_1607395 : Nat := 118140960795 + 1607395 * 2 ^ 59
def prefixEnd_1607395 : Nat := 4983230072969 + 3 ^ 40 * 1607395 * 2
def baseEnd_1607395 : Nat := 183414719251965287415607

theorem tailTrace_1607395 : CollatzResearch.WordTrace tailWord_1607395 prefixEnd_1607395 183414719251965287415607 := by
  unfold tailWord_1607395
  simp only [CollatzResearch.WordTrace]
  refine ⟨58626512011689911055359639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39084341341126607370239759 58626512011689911055359639)
  ·
    refine ⟨87939768017534866583039459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58626512011689911055359639 87939768017534866583039459)
    ·
      refine ⟨131909652026302299874559189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87939768017534866583039459 131909652026302299874559189)
      ·
        refine ⟨3091632469366460153309981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 131909652026302299874559189 3091632469366460153309981)
        ·
          refine ⟨1159362176012422557491243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3091632469366460153309981 1159362176012422557491243)
          ·
            refine ⟨1739043264018633836236865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159362176012422557491243 1739043264018633836236865)
            ·
              refine ⟨1304282448013975377177649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739043264018633836236865 1304282448013975377177649)
              ·
                refine ⟨978211836010481532883237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304282448013975377177649 978211836010481532883237)
                ·
                  refine ⟨183414719251965287415607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978211836010481532883237 183414719251965287415607)
                  ·
                    rfl

theorem cell22_1607395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 4].length) (baseStart_1607395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607395 prefixEnd_1607395 := by exact prefixLift 1607395
  have htrace : WordTrace (prefixWord ++ tailWord_1607395) baseStart_1607395 baseEnd_1607395 := by
    simpa [prefixWord, tailWord_1607395, baseEnd_1607395] using wordTrace_append hprefix tailTrace_1607395
  have hstable : (prefixWord ++ tailWord_1607395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607395).length < 2 ^ (prefixWord ++ tailWord_1607395).sum := by decide
  have hdescent : baseEnd_1607395 < baseStart_1607395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607402 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1607402 : Nat := 118140960795 + 1607402 * 2 ^ 59
def prefixEnd_1607402 : Nat := 4983230072969 + 3 ^ 40 * 1607402 * 2
def baseEnd_1607402 : Nat := 550246553998950177321799

theorem tailTrace_1607402 : CollatzResearch.WordTrace tailWord_1607402 prefixEnd_1607402 550246553998950177321799 := by
  unfold tailWord_1607402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14656691830666137812716115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39084511548443034167242973 14656691830666137812716115)
  ·
    refine ⟨21985037745999206719074173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14656691830666137812716115 21985037745999206719074173)
    ·
      refine ⟨8244389154749702519652815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21985037745999206719074173 8244389154749702519652815)
      ·
        refine ⟨12366583732124553779479223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8244389154749702519652815 12366583732124553779479223)
        ·
          refine ⟨18549875598186830669218835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12366583732124553779479223 18549875598186830669218835)
          ·
            refine ⟨27824813397280246003828253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18549875598186830669218835 27824813397280246003828253)
            ·
              refine ⟨10434305023980092251435595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27824813397280246003828253 10434305023980092251435595)
              ·
                refine ⟨15651457535970138377153393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434305023980092251435595 15651457535970138377153393)
                ·
                  refine ⟨11738593151977603782865045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15651457535970138377153393 11738593151977603782865045)
                  ·
                    refine ⟨550246553998950177321799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11738593151977603782865045 550246553998950177321799)
                    ·
                      rfl

theorem cell22_1607402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1607402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607402 prefixEnd_1607402 := by exact prefixLift 1607402
  have htrace : WordTrace (prefixWord ++ tailWord_1607402) baseStart_1607402 baseEnd_1607402 := by
    simpa [prefixWord, tailWord_1607402, baseEnd_1607402] using wordTrace_append hprefix tailTrace_1607402
  have hstable : (prefixWord ++ tailWord_1607402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607402).length < 2 ^ (prefixWord ++ tailWord_1607402).sum := by decide
  have hdescent : baseEnd_1607402 < baseStart_1607402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607432 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1607432 : Nat := 118140960795 + 1607432 * 2 ^ 59
def prefixEnd_1607432 : Nat := 4983230072969 + 3 ^ 40 * 1607432 * 2
def baseEnd_1607432 : Nat := 550256823612040099071707

theorem tailTrace_1607432 : CollatzResearch.WordTrace tailWord_1607432 prefixEnd_1607432 550256823612040099071707 := by
  unfold tailWord_1607432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29313930756277933187228275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39085241008370577582971033 29313930756277933187228275)
  ·
    refine ⟨43970896134416899780842413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29313930756277933187228275 43970896134416899780842413)
    ·
      refine ⟨16489086050406337417815905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43970896134416899780842413 16489086050406337417815905)
      ·
        refine ⟨12366814537804753063361929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16489086050406337417815905 12366814537804753063361929)
        ·
          refine ⟨9275110903353564797521447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12366814537804753063361929 9275110903353564797521447)
          ·
            refine ⟨13912666355030347196282171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9275110903353564797521447 13912666355030347196282171)
            ·
              refine ⟨20868999532545520794423257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13912666355030347196282171 20868999532545520794423257)
              ·
                refine ⟨15651749649409140595817443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20868999532545520794423257 15651749649409140595817443)
                ·
                  refine ⟨23477624474113710893726165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15651749649409140595817443 23477624474113710893726165)
                  ·
                    refine ⟨550256823612040099071707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23477624474113710893726165 550256823612040099071707)
                    ·
                      rfl

theorem cell22_1607432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1607432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607432 prefixEnd_1607432 := by exact prefixLift 1607432
  have htrace : WordTrace (prefixWord ++ tailWord_1607432) baseStart_1607432 baseEnd_1607432 := by
    simpa [prefixWord, tailWord_1607432, baseEnd_1607432] using wordTrace_append hprefix tailTrace_1607432
  have hstable : (prefixWord ++ tailWord_1607432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607432).length < 2 ^ (prefixWord ++ tailWord_1607432).sum := by decide
  have hdescent : baseEnd_1607432 < baseStart_1607432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607444 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1607444 : Nat := 118140960795 + 1607444 * 2 ^ 59
def prefixEnd_1607444 : Nat := 4983230072969 + 3 ^ 40 * 1607444 * 2
def baseEnd_1607444 : Nat := 550260931457276067771671

theorem tailTrace_1607444 : CollatzResearch.WordTrace tailWord_1607444 prefixEnd_1607444 550260931457276067771671 := by
  unfold tailWord_1607444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29314149594256196211946693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39085532792341594949262257 29314149594256196211946693)
  ·
    refine ⟨5496403048923036789740005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29314149594256196211946693 5496403048923036789740005)
    ·
      refine ⟨1030575571673069398076251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5496403048923036789740005 1030575571673069398076251)
      ·
        refine ⟨1545863357509604097114377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030575571673069398076251 1545863357509604097114377)
        ·
          refine ⟨1159397518132203072835783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1545863357509604097114377 1159397518132203072835783)
          ·
            refine ⟨1739096277198304609253675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159397518132203072835783 1739096277198304609253675)
            ·
              refine ⟨2608644415797456913880513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739096277198304609253675 2608644415797456913880513)
              ·
                refine ⟨1956483311848092685410385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608644415797456913880513 1956483311848092685410385)
                ·
                  refine ⟨1467362483886069514057789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956483311848092685410385 1467362483886069514057789)
                  ·
                    refine ⟨550260931457276067771671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467362483886069514057789 550260931457276067771671)
                    ·
                      rfl

theorem cell22_1607444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1607444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607444 prefixEnd_1607444 := by exact prefixLift 1607444
  have htrace : WordTrace (prefixWord ++ tailWord_1607444) baseStart_1607444 baseEnd_1607444 := by
    simpa [prefixWord, tailWord_1607444, baseEnd_1607444] using wordTrace_append hprefix tailTrace_1607444
  have hstable : (prefixWord ++ tailWord_1607444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607444).length < 2 ^ (prefixWord ++ tailWord_1607444).sum := by decide
  have hdescent : baseEnd_1607444 < baseStart_1607444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607496 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_1607496 : Nat := 118140960795 + 1607496 * 2 ^ 59
def prefixEnd_1607496 : Nat := 4983230072969 + 3 ^ 40 * 1607496 * 2
def baseEnd_1607496 : Nat := 183426244039988421823837

theorem tailTrace_1607496 : CollatzResearch.WordTrace tailWord_1607496 prefixEnd_1607496 183426244039988421823837 := by
  unfold tailWord_1607496
  simp only [CollatzResearch.WordTrace]
  refine ⟨29315097892162002652393171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39086797189549336869857561 29315097892162002652393171)
  ·
    refine ⟨43972646838243003978589757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29315097892162002652393171 43972646838243003978589757)
    ·
      refine ⟨16489742564341126491971159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43972646838243003978589757 16489742564341126491971159)
      ·
        refine ⟨24734613846511689737956739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16489742564341126491971159 24734613846511689737956739)
        ·
          refine ⟨37101920769767534606935109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24734613846511689737956739 37101920769767534606935109)
          ·
            refine ⟨6956610144331412738800333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37101920769767534606935109 6956610144331412738800333)
            ·
              refine ⟨2608728804124279777050125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6956610144331412738800333 2608728804124279777050125)
              ·
                refine ⟨978273301546604916393797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2608728804124279777050125 978273301546604916393797)
                ·
                  refine ⟨183426244039988421823837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978273301546604916393797 183426244039988421823837)
                  ·
                    rfl

theorem cell22_1607496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_1607496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607496 prefixEnd_1607496 := by exact prefixLift 1607496
  have htrace : WordTrace (prefixWord ++ tailWord_1607496) baseStart_1607496 baseEnd_1607496 := by
    simpa [prefixWord, tailWord_1607496, baseEnd_1607496] using wordTrace_append hprefix tailTrace_1607496
  have hstable : (prefixWord ++ tailWord_1607496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607496).length < 2 ^ (prefixWord ++ tailWord_1607496).sum := by decide
  have hdescent : baseEnd_1607496 < baseStart_1607496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607509 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1607509 : Nat := 118140960795 + 1607509 * 2 ^ 59
def prefixEnd_1607509 : Nat := 4983230072969 + 3 ^ 40 * 1607509 * 2
def baseEnd_1607509 : Nat := 550283182285637564896471

theorem tailTrace_1607509 : CollatzResearch.WordTrace tailWord_1607509 prefixEnd_1607509 550283182285637564896471 := by
  unfold tailWord_1607509
  simp only [CollatzResearch.WordTrace]
  refine ⟨58630669933276908525009581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39087113288851272350006387 58630669933276908525009581)
  ·
    refine ⟨21986501224978840696878593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58630669933276908525009581 21986501224978840696878593)
    ·
      refine ⟨16489875918734130522658945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21986501224978840696878593 16489875918734130522658945)
      ·
        refine ⟨12367406939050597891994209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16489875918734130522658945 12367406939050597891994209)
        ·
          refine ⟨9275555204287948418995657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12367406939050597891994209 9275555204287948418995657)
          ·
            refine ⟨6956666403215961314246743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9275555204287948418995657 6956666403215961314246743)
            ·
              refine ⟨10434999604823941971370115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956666403215961314246743 10434999604823941971370115)
              ·
                refine ⟨15652499407235912957055173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434999604823941971370115 15652499407235912957055173)
                ·
                  refine ⟨2934843638856733679447845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15652499407235912957055173 2934843638856733679447845)
                  ·
                    refine ⟨550283182285637564896471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2934843638856733679447845 550283182285637564896471)
                    ·
                      rfl

theorem cell22_1607509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1607509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607509 prefixEnd_1607509 := by exact prefixLift 1607509
  have htrace : WordTrace (prefixWord ++ tailWord_1607509) baseStart_1607509 baseEnd_1607509 := by
    simpa [prefixWord, tailWord_1607509, baseEnd_1607509] using wordTrace_append hprefix tailTrace_1607509
  have hstable : (prefixWord ++ tailWord_1607509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607509).length < 2 ^ (prefixWord ++ tailWord_1607509).sum := by decide
  have hdescent : baseEnd_1607509 < baseStart_1607509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607539 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 5, 3]
def baseStart_1607539 : Nat := 118140960795 + 1607539 * 2 ^ 59
def prefixEnd_1607539 : Nat := 4983230072969 + 3 ^ 40 * 1607539 * 2
def baseEnd_1607539 : Nat := 550293451898727486646379

theorem tailTrace_1607539 : CollatzResearch.WordTrace tailWord_1607539 prefixEnd_1607539 550293451898727486646379 := by
  unfold tailWord_1607539
  simp only [CollatzResearch.WordTrace]
  refine ⟨58631764123168223648601671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39087842748778815765734447 58631764123168223648601671)
  ·
    refine ⟨87947646184752335472902507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58631764123168223648601671 87947646184752335472902507)
    ·
      refine ⟨131921469277128503209353761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87947646184752335472902507 131921469277128503209353761)
      ·
        refine ⟨98941101957846377407015321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131921469277128503209353761 98941101957846377407015321)
        ·
          refine ⟨74205826468384783055261491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98941101957846377407015321 74205826468384783055261491)
          ·
            refine ⟨111308739702577174582892237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74205826468384783055261491 111308739702577174582892237)
            ·
              refine ⟨41740777388466440468584589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111308739702577174582892237 41740777388466440468584589)
              ·
                refine ⟨15652791520674915175719221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41740777388466440468584589 15652791520674915175719221)
                ·
                  refine ⟨1467449205063273297723677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15652791520674915175719221 1467449205063273297723677)
                  ·
                    refine ⟨550293451898727486646379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467449205063273297723677 550293451898727486646379)
                    ·
                      rfl

theorem cell22_1607539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3].length) (baseStart_1607539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607539 prefixEnd_1607539 := by exact prefixLift 1607539
  have htrace : WordTrace (prefixWord ++ tailWord_1607539) baseStart_1607539 baseEnd_1607539 := by
    simpa [prefixWord, tailWord_1607539, baseEnd_1607539] using wordTrace_append hprefix tailTrace_1607539
  have hstable : (prefixWord ++ tailWord_1607539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607539).length < 2 ^ (prefixWord ++ tailWord_1607539).sum := by decide
  have hdescent : baseEnd_1607539 < baseStart_1607539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607569 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 5]
def baseStart_1607569 : Nat := 118140960795 + 1607569 * 2 ^ 59
def prefixEnd_1607569 : Nat := 4983230072969 + 3 ^ 40 * 1607569 * 2
def baseEnd_1607569 : Nat := 183434573837272469465429

theorem tailTrace_1607569 : CollatzResearch.WordTrace tailWord_1607569 prefixEnd_1607569 183434573837272469465429 := by
  unfold tailWord_1607569
  simp only [CollatzResearch.WordTrace]
  refine ⟨58632858313059538772193761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39088572208706359181462507 58632858313059538772193761)
  ·
    refine ⟨43974643734794654079145321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58632858313059538772193761 43974643734794654079145321)
    ·
      refine ⟨32980982801095990559358991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43974643734794654079145321 32980982801095990559358991)
      ·
        refine ⟨49471474201643985839038487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32980982801095990559358991 49471474201643985839038487)
        ·
          refine ⟨74207211302465978758557731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49471474201643985839038487 74207211302465978758557731)
          ·
            refine ⟨111310816953698968137836597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74207211302465978758557731 111310816953698968137836597)
            ·
              refine ⟨10435389089409278262922181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111310816953698968137836597 10435389089409278262922181)
              ·
                refine ⟨1956635454264239674297909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10435389089409278262922181 1956635454264239674297909)
                ·
                  refine ⟨183434573837272469465429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956635454264239674297909 183434573837272469465429)
                  ·
                    rfl

theorem cell22_1607569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_1607569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607569 prefixEnd_1607569 := by exact prefixLift 1607569
  have htrace : WordTrace (prefixWord ++ tailWord_1607569) baseStart_1607569 baseEnd_1607569 := by
    simpa [prefixWord, tailWord_1607569, baseEnd_1607569] using wordTrace_append hprefix tailTrace_1607569
  have hstable : (prefixWord ++ tailWord_1607569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607569).length < 2 ^ (prefixWord ++ tailWord_1607569).sum := by decide
  have hdescent : baseEnd_1607569 < baseStart_1607569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607573 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_1607573 : Nat := 118140960795 + 1607573 * 2 ^ 59
def prefixEnd_1607573 : Nat := 4983230072969 + 3 ^ 40 * 1607573 * 2
def baseEnd_1607573 : Nat := 550305090793562731296275

theorem tailTrace_1607573 : CollatzResearch.WordTrace tailWord_1607573 prefixEnd_1607573 550305090793562731296275 := by
  unfold tailWord_1607573
  simp only [CollatzResearch.WordTrace]
  refine ⟨58633004205045047455339373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39088669470030031636892915 58633004205045047455339373)
  ·
    refine ⟨21987376576891892795752265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58633004205045047455339373 21987376576891892795752265)
    ·
      refine ⟨16490532432668919596814199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21987376576891892795752265 16490532432668919596814199)
      ·
        refine ⟨24735798649003379395221299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16490532432668919596814199 24735798649003379395221299)
        ·
          refine ⟨37103697973505069092831949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24735798649003379395221299 37103697973505069092831949)
          ·
            refine ⟨13913886740064400909811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37103697973505069092831949 13913886740064400909811981)
            ·
              refine ⟨5217707527524150341179493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13913886740064400909811981 5217707527524150341179493)
              ·
                refine ⟨978320161410778188971155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5217707527524150341179493 978320161410778188971155)
                ·
                  refine ⟨1467480242116167283456733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978320161410778188971155 1467480242116167283456733)
                  ·
                    refine ⟨550305090793562731296275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467480242116167283456733 550305090793562731296275)
                    ·
                      rfl

theorem cell22_1607573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_1607573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607573 prefixEnd_1607573 := by exact prefixLift 1607573
  have htrace : WordTrace (prefixWord ++ tailWord_1607573) baseStart_1607573 baseEnd_1607573 := by
    simpa [prefixWord, tailWord_1607573, baseEnd_1607573] using wordTrace_append hprefix tailTrace_1607573
  have hstable : (prefixWord ++ tailWord_1607573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607573).length < 2 ^ (prefixWord ++ tailWord_1607573).sum := by decide
  have hdescent : baseEnd_1607573 < baseStart_1607573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607599 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_1607599 : Nat := 118140960795 + 1607599 * 2 ^ 59
def prefixEnd_1607599 : Nat := 4983230072969 + 3 ^ 40 * 1607599 * 2
def baseEnd_1607599 : Nat := 550313991124907330146195

theorem tailTrace_1607599 : CollatzResearch.WordTrace tailWord_1607599 prefixEnd_1607599 550313991124907330146195 := by
  unfold tailWord_1607599
  simp only [CollatzResearch.WordTrace]
  refine ⟨58633952502950853895785851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39089301668633902597190567 58633952502950853895785851)
  ·
    refine ⟨87950928754426280843678777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58633952502950853895785851 87950928754426280843678777)
    ·
      refine ⟨65963196565819710632759083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87950928754426280843678777 65963196565819710632759083)
      ·
        refine ⟨98944794848729565949138625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65963196565819710632759083 98944794848729565949138625)
        ·
          refine ⟨74208596136547174461853969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98944794848729565949138625 74208596136547174461853969)
          ·
            refine ⟨55656447102410380846390477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74208596136547174461853969 55656447102410380846390477)
            ·
              refine ⟨20871167663403892817396429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55656447102410380846390477 20871167663403892817396429)
              ·
                refine ⟨7826687873776459806523661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20871167663403892817396429 7826687873776459806523661)
                ·
                  refine ⟨2935007952666172427446373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7826687873776459806523661 2935007952666172427446373)
                  ·
                    refine ⟨550313991124907330146195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935007952666172427446373 550313991124907330146195)
                    ·
                      rfl

theorem cell22_1607599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_1607599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607599 prefixEnd_1607599 := by exact prefixLift 1607599
  have htrace : WordTrace (prefixWord ++ tailWord_1607599) baseStart_1607599 baseEnd_1607599 := by
    simpa [prefixWord, tailWord_1607599, baseEnd_1607599] using wordTrace_append hprefix tailTrace_1607599
  have hstable : (prefixWord ++ tailWord_1607599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607599).length < 2 ^ (prefixWord ++ tailWord_1607599).sum := by decide
  have hdescent : baseEnd_1607599 < baseStart_1607599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607616 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_1607616 : Nat := 118140960795 + 1607616 * 2 ^ 59
def prefixEnd_1607616 : Nat := 4983230072969 + 3 ^ 40 * 1607616 * 2
def baseEnd_1607616 : Nat := 550319810572324952471143

theorem tailTrace_1607616 : CollatzResearch.WordTrace tailWord_1607616 prefixEnd_1607616 550319810572324952471143 := by
  unfold tailWord_1607616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29317286271944632899577351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39089715029259510532769801 29317286271944632899577351)
  ·
    refine ⟨43975929407916949349366027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29317286271944632899577351 43975929407916949349366027)
    ·
      refine ⟨65963894111875424024049041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43975929407916949349366027 65963894111875424024049041)
      ·
        refine ⟨49472920583906568018036781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65963894111875424024049041 49472920583906568018036781)
        ·
          refine ⟨18552345218964963006763793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49472920583906568018036781 18552345218964963006763793)
          ·
            refine ⟨13914258914223722255072845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18552345218964963006763793 13914258914223722255072845)
            ·
              refine ⟨5217847092833895845652317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13914258914223722255072845 5217847092833895845652317)
              ·
                refine ⟨1956692659812710942119619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5217847092833895845652317 1956692659812710942119619)
                ·
                  refine ⟨2935038989719066413179429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956692659812710942119619 2935038989719066413179429)
                  ·
                    refine ⟨550319810572324952471143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935038989719066413179429 550319810572324952471143)
                    ·
                      rfl

theorem cell22_1607616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_1607616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607616 prefixEnd_1607616 := by exact prefixLift 1607616
  have htrace : WordTrace (prefixWord ++ tailWord_1607616) baseStart_1607616 baseEnd_1607616 := by
    simpa [prefixWord, tailWord_1607616, baseEnd_1607616] using wordTrace_append hprefix tailTrace_1607616
  have hstable : (prefixWord ++ tailWord_1607616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607616).length < 2 ^ (prefixWord ++ tailWord_1607616).sum := by decide
  have hdescent : baseEnd_1607616 < baseStart_1607616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607631 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 4]
def baseStart_1607631 : Nat := 118140960795 + 1607631 * 2 ^ 59
def prefixEnd_1607631 : Nat := 4983230072969 + 3 ^ 40 * 1607631 * 2
def baseEnd_1607631 : Nat := 183441648459623304448699

theorem tailTrace_1607631 : CollatzResearch.WordTrace tailWord_1607631 prefixEnd_1607631 183441648459623304448699 := by
  unfold tailWord_1607631
  simp only [CollatzResearch.WordTrace]
  refine ⟨58635119638834923360950747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39090079759223282240633831 58635119638834923360950747)
  ·
    refine ⟨87952679458252385041426121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58635119638834923360950747 87952679458252385041426121)
    ·
      refine ⟨65964509593689288781069591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87952679458252385041426121 65964509593689288781069591)
      ·
        refine ⟨98946764390533933171604387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65964509593689288781069591 98946764390533933171604387)
        ·
          refine ⟨148420146585800899757406581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98946764390533933171604387 148420146585800899757406581)
          ·
            refine ⟨13914388742418834352256867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148420146585800899757406581 13914388742418834352256867)
            ·
              refine ⟨20871583113628251528385301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13914388742418834352256867 20871583113628251528385301)
              ·
                refine ⟨978355458451324290393061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20871583113628251528385301 978355458451324290393061)
                ·
                  refine ⟨183441648459623304448699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978355458451324290393061 183441648459623304448699)
                  ·
                    rfl

theorem cell22_1607631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 4].length) (baseStart_1607631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607631 prefixEnd_1607631 := by exact prefixLift 1607631
  have htrace : WordTrace (prefixWord ++ tailWord_1607631) baseStart_1607631 baseEnd_1607631 := by
    simpa [prefixWord, tailWord_1607631, baseEnd_1607631] using wordTrace_append hprefix tailTrace_1607631
  have hstable : (prefixWord ++ tailWord_1607631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607631).length < 2 ^ (prefixWord ++ tailWord_1607631).sum := by decide
  have hdescent : baseEnd_1607631 < baseStart_1607631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607665 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 4]
def baseStart_1607665 : Nat := 118140960795 + 1607665 * 2 ^ 59
def prefixEnd_1607665 : Nat := 4983230072969 + 3 ^ 40 * 1607665 * 2
def baseEnd_1607665 : Nat := 183445528091235052665331

theorem tailTrace_1607665 : CollatzResearch.WordTrace tailWord_1607665 prefixEnd_1607665 183445528091235052665331 := by
  unfold tailWord_1607665
  simp only [CollatzResearch.WordTrace]
  refine ⟨58636359720711747167688449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39090906480474498111792299 58636359720711747167688449)
  ·
    refine ⟨43977269790533810375766337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58636359720711747167688449 43977269790533810375766337)
    ·
      refine ⟨32982952342900357781824753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43977269790533810375766337 32982952342900357781824753)
      ·
        refine ⟨24737214257175268336368565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32982952342900357781824753 24737214257175268336368565)
        ·
          refine ⟨2319113836610181406534553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24737214257175268336368565 2319113836610181406534553)
          ·
            refine ⟨1739335377457636054900915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319113836610181406534553 1739335377457636054900915)
            ·
              refine ⟨2609003066186454082351373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739335377457636054900915 2609003066186454082351373)
              ·
                refine ⟨978376149819920280881765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2609003066186454082351373 978376149819920280881765)
                ·
                  refine ⟨183445528091235052665331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978376149819920280881765 183445528091235052665331)
                  ·
                    rfl

theorem cell22_1607665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_1607665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607665 prefixEnd_1607665 := by exact prefixLift 1607665
  have htrace : WordTrace (prefixWord ++ tailWord_1607665) baseStart_1607665 baseEnd_1607665 := by
    simpa [prefixWord, tailWord_1607665, baseEnd_1607665] using wordTrace_append hprefix tailTrace_1607665
  have hstable : (prefixWord ++ tailWord_1607665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607665).length < 2 ^ (prefixWord ++ tailWord_1607665).sum := by decide
  have hdescent : baseEnd_1607665 < baseStart_1607665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607678 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1607678 : Nat := 118140960795 + 1607678 * 2 ^ 59
def prefixEnd_1607678 : Nat := 4983230072969 + 3 ^ 40 * 1607678 * 2
def baseEnd_1607678 : Nat := 550341034439377457420953

theorem tailTrace_1607678 : CollatzResearch.WordTrace tailWord_1607678 prefixEnd_1607678 550341034439377457420953 := by
  unfold tailWord_1607678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329604233708081298488961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39091222579776433591941125 7329604233708081298488961)
  ·
    refine ⟨5497203175281060973866721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7329604233708081298488961 5497203175281060973866721)
    ·
      refine ⟨4122902381460795730400041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5497203175281060973866721 4122902381460795730400041)
      ·
        refine ⟨3092176786095596797800031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4122902381460795730400041 3092176786095596797800031)
        ·
          refine ⟨4638265179143395196700047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092176786095596797800031 4638265179143395196700047)
          ·
            refine ⟨6957397768715092795050071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638265179143395196700047 6957397768715092795050071)
            ·
              refine ⟨10436096653072639192575107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957397768715092795050071 10436096653072639192575107)
              ·
                refine ⟨15654144979608958788862661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10436096653072639192575107 15654144979608958788862661)
                ·
                  refine ⟨2935152183676679772911749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15654144979608958788862661 2935152183676679772911749)
                  ·
                    refine ⟨550341034439377457420953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935152183676679772911749 550341034439377457420953)
                    ·
                      rfl

theorem cell22_1607678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1607678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607678 prefixEnd_1607678 := by exact prefixLift 1607678
  have htrace : WordTrace (prefixWord ++ tailWord_1607678) baseStart_1607678 baseEnd_1607678 := by
    simpa [prefixWord, tailWord_1607678, baseEnd_1607678] using wordTrace_append hprefix tailTrace_1607678
  have hstable : (prefixWord ++ tailWord_1607678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607678).length < 2 ^ (prefixWord ++ tailWord_1607678).sum := by decide
  have hdescent : baseEnd_1607678 < baseStart_1607678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607751 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1607751 : Nat := 118140960795 + 1607751 * 2 ^ 59
def prefixEnd_1607751 : Nat := 4983230072969 + 3 ^ 40 * 1607751 * 2
def baseEnd_1607751 : Nat := 550366023831229600345729

theorem tailTrace_1607751 : CollatzResearch.WordTrace tailWord_1607751 prefixEnd_1607751 550366023831229600345729 := by
  unfold tailWord_1607751
  simp only [CollatzResearch.WordTrace]
  refine ⟨58639496398400183855319107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39092997598933455903546071 58639496398400183855319107)
  ·
    refine ⟨87959244597600275782978661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58639496398400183855319107 87959244597600275782978661)
    ·
      refine ⟨16492358362050051709308499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87959244597600275782978661 16492358362050051709308499)
      ·
        refine ⟨24738537543075077563962749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16492358362050051709308499 24738537543075077563962749)
        ·
          refine ⟨9276951578653154086486031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24738537543075077563962749 9276951578653154086486031)
          ·
            refine ⟨13915427367979731129729047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9276951578653154086486031 13915427367979731129729047)
            ·
              refine ⟨20873141051969596694593571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13915427367979731129729047 20873141051969596694593571)
              ·
                refine ⟨31309711577954395041890357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20873141051969596694593571 31309711577954395041890357)
                ·
                  refine ⟨2935285460433224535177221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31309711577954395041890357 2935285460433224535177221)
                  ·
                    refine ⟨550366023831229600345729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935285460433224535177221 550366023831229600345729)
                    ·
                      rfl

theorem cell22_1607751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1607751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607751 prefixEnd_1607751 := by exact prefixLift 1607751
  have htrace : WordTrace (prefixWord ++ tailWord_1607751) baseStart_1607751 baseEnd_1607751 := by
    simpa [prefixWord, tailWord_1607751, baseEnd_1607751] using wordTrace_append hprefix tailTrace_1607751
  have hstable : (prefixWord ++ tailWord_1607751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607751).length < 2 ^ (prefixWord ++ tailWord_1607751).sum := by decide
  have hdescent : baseEnd_1607751 < baseStart_1607751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607834 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_1607834 : Nat := 118140960795 + 1607834 * 2 ^ 59
def prefixEnd_1607834 : Nat := 4983230072969 + 3 ^ 40 * 1607834 * 2
def baseEnd_1607834 : Nat := 183464812142481683506825

theorem tailTrace_1607834 : CollatzResearch.WordTrace tailWord_1607834 prefixEnd_1607834 183464812142481683506825 := by
  unfold tailWord_1607834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660630914274872257647639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39095015771399659353727037 14660630914274872257647639)
  ·
    refine ⟨21990946371412308386471459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14660630914274872257647639 21990946371412308386471459)
    ·
      refine ⟨32986419557118462579707189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21990946371412308386471459 32986419557118462579707189)
      ·
        refine ⟨3092476833479855866847549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32986419557118462579707189 3092476833479855866847549)
        ·
          refine ⟨1159678812554945950067831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3092476833479855866847549 1159678812554945950067831)
          ·
            refine ⟨1739518218832418925101747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159678812554945950067831 1739518218832418925101747)
            ·
              refine ⟨2609277328248628387652621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739518218832418925101747 2609277328248628387652621)
              ·
                refine ⟨978478998093235645369733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2609277328248628387652621 978478998093235645369733)
                ·
                  refine ⟨183464812142481683506825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978478998093235645369733 183464812142481683506825)
                  ·
                    rfl

theorem cell22_1607834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_1607834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607834 prefixEnd_1607834 := by exact prefixLift 1607834
  have htrace : WordTrace (prefixWord ++ tailWord_1607834) baseStart_1607834 baseEnd_1607834 := by
    simpa [prefixWord, tailWord_1607834, baseEnd_1607834] using wordTrace_append hprefix tailTrace_1607834
  have hstable : (prefixWord ++ tailWord_1607834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607834).length < 2 ^ (prefixWord ++ tailWord_1607834).sum := by decide
  have hdescent : baseEnd_1607834 < baseStart_1607834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607871 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_1607871 : Nat := 118140960795 + 1607871 * 2 ^ 59
def prefixEnd_1607871 : Nat := 4983230072969 + 3 ^ 40 * 1607871 * 2
def baseEnd_1607871 : Nat := 550407102283589287345361

theorem tailTrace_1607871 : CollatzResearch.WordTrace tailWord_1607871 prefixEnd_1607871 550407102283589287345361 := by
  unfold tailWord_1607871
  simp only [CollatzResearch.WordTrace]
  refine ⟨58643873157965444349687467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39095915438643629566458311 58643873157965444349687467)
  ·
    refine ⟨87965809736948166524531201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58643873157965444349687467 87965809736948166524531201)
    ·
      refine ⟨65974357302711124893398401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87965809736948166524531201 65974357302711124893398401)
      ·
        refine ⟨49480767977033343670048801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65974357302711124893398401 49480767977033343670048801)
        ·
          refine ⟨37110575982775007752536601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49480767977033343670048801 37110575982775007752536601)
          ·
            refine ⟨27832931987081255814402451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37110575982775007752536601 27832931987081255814402451)
            ·
              refine ⟨41749397980621883721603677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27832931987081255814402451 41749397980621883721603677)
              ·
                refine ⟨15656024242733206395601379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41749397980621883721603677 15656024242733206395601379)
                ·
                  refine ⟨23484036364099809593402069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15656024242733206395601379 23484036364099809593402069)
                  ·
                    refine ⟨550407102283589287345361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23484036364099809593402069 550407102283589287345361)
                    ·
                      rfl

theorem cell22_1607871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_1607871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607871 prefixEnd_1607871 := by exact prefixLift 1607871
  have htrace : WordTrace (prefixWord ++ tailWord_1607871) baseStart_1607871 baseEnd_1607871 := by
    simpa [prefixWord, tailWord_1607871, baseEnd_1607871] using wordTrace_append hprefix tailTrace_1607871
  have hstable : (prefixWord ++ tailWord_1607871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607871).length < 2 ^ (prefixWord ++ tailWord_1607871).sum := by decide
  have hdescent : baseEnd_1607871 < baseStart_1607871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607907 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 5]
def baseStart_1607907 : Nat := 118140960795 + 1607907 * 2 ^ 59
def prefixEnd_1607907 : Nat := 4983230072969 + 3 ^ 40 * 1607907 * 2
def baseEnd_1607907 : Nat := 183473141939765731148417

theorem tailTrace_1607907 : CollatzResearch.WordTrace tailWord_1607907 prefixEnd_1607907 183473141939765731148417 := by
  unfold tailWord_1607907
  simp only [CollatzResearch.WordTrace]
  refine ⟨58645186185835022497997975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39096790790556681665331983 58645186185835022497997975)
  ·
    refine ⟨87967779278752533746996963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58645186185835022497997975 87967779278752533746996963)
    ·
      refine ⟨131951668918128800620495445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87967779278752533746996963 131951668918128800620495445)
      ·
        refine ⟨1546308620134321882271431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 131951668918128800620495445 1546308620134321882271431)
        ·
          refine ⟨2319462930201482823407147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546308620134321882271431 2319462930201482823407147)
          ·
            refine ⟨3479194395302224235110721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319462930201482823407147 3479194395302224235110721)
            ·
              refine ⟨2609395796476668176333041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479194395302224235110721 2609395796476668176333041)
              ·
                refine ⟨1957046847357501132249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609395796476668176333041 1957046847357501132249781)
                ·
                  refine ⟨183473141939765731148417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1957046847357501132249781 183473141939765731148417)
                  ·
                    rfl

theorem cell22_1607907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 5].length) (baseStart_1607907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607907 prefixEnd_1607907 := by exact prefixLift 1607907
  have htrace : WordTrace (prefixWord ++ tailWord_1607907) baseStart_1607907 baseEnd_1607907 := by
    simpa [prefixWord, tailWord_1607907, baseEnd_1607907] using wordTrace_append hprefix tailTrace_1607907
  have hstable : (prefixWord ++ tailWord_1607907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607907).length < 2 ^ (prefixWord ++ tailWord_1607907).sum := by decide
  have hdescent : baseEnd_1607907 < baseStart_1607907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607911 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1607911 : Nat := 118140960795 + 1607911 * 2 ^ 59
def prefixEnd_1607911 : Nat := 4983230072969 + 3 ^ 40 * 1607911 * 2
def baseEnd_1607911 : Nat := 550420795101042516345239

theorem tailTrace_1607911 : CollatzResearch.WordTrace tailWord_1607911 prefixEnd_1607911 550420795101042516345239 := by
  unfold tailWord_1607911
  simp only [CollatzResearch.WordTrace]
  refine ⟨58645332077820531181143587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39096888051880354120762391 58645332077820531181143587)
  ·
    refine ⟨87967998116730796771715381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58645332077820531181143587 87967998116730796771715381)
    ·
      refine ⟨8246999823443512197348317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87967998116730796771715381 8246999823443512197348317)
      ·
        refine ⟨3092624933791317074005619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8246999823443512197348317 3092624933791317074005619)
        ·
          refine ⟨4638937400686975611008429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092624933791317074005619 4638937400686975611008429)
          ·
            refine ⟨1739601525257615854128161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4638937400686975611008429 1739601525257615854128161)
            ·
              refine ⟨1304701143943211890596121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739601525257615854128161 1304701143943211890596121)
              ·
                refine ⟨978525857957408917947091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304701143943211890596121 978525857957408917947091)
                ·
                  refine ⟨1467788786936113376920637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978525857957408917947091 1467788786936113376920637)
                  ·
                    refine ⟨550420795101042516345239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467788786936113376920637 550420795101042516345239)
                    ·
                      rfl

theorem cell22_1607911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1607911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607911 prefixEnd_1607911 := by exact prefixLift 1607911
  have htrace : WordTrace (prefixWord ++ tailWord_1607911) baseStart_1607911 baseEnd_1607911 := by
    simpa [prefixWord, tailWord_1607911, baseEnd_1607911] using wordTrace_append hprefix tailTrace_1607911
  have hstable : (prefixWord ++ tailWord_1607911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607911).length < 2 ^ (prefixWord ++ tailWord_1607911).sum := by decide
  have hdescent : baseEnd_1607911 < baseStart_1607911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607918 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_1607918 : Nat := 118140960795 + 1607918 * 2 ^ 59
def prefixEnd_1607918 : Nat := 4983230072969 + 3 ^ 40 * 1607918 * 2
def baseEnd_1607918 : Nat := 183474397114698943806739

theorem tailTrace_1607918 : CollatzResearch.WordTrace tailWord_1607918 prefixEnd_1607918 183474397114698943806739 := by
  unfold tailWord_1607918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330698423599396422081051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39097058259196780917765605 7330698423599396422081051)
  ·
    refine ⟨10996047635399094633121577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7330698423599396422081051 10996047635399094633121577)
    ·
      refine ⟨8247035726549320974841183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10996047635399094633121577 8247035726549320974841183)
      ·
        refine ⟨12370553589823981462261775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247035726549320974841183 12370553589823981462261775)
        ·
          refine ⟨18555830384735972193392663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370553589823981462261775 18555830384735972193392663)
          ·
            refine ⟨27833745577103958290088995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18555830384735972193392663 27833745577103958290088995)
            ·
              refine ⟨41750618365655937435133493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27833745577103958290088995 41750618365655937435133493)
              ·
                refine ⟨3914120471780244134543765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41750618365655937435133493 3914120471780244134543765)
                ·
                  refine ⟨183474397114698943806739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3914120471780244134543765 183474397114698943806739)
                  ·
                    rfl

theorem cell22_1607918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_1607918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607918 prefixEnd_1607918 := by exact prefixLift 1607918
  have htrace : WordTrace (prefixWord ++ tailWord_1607918) baseStart_1607918 baseEnd_1607918 := by
    simpa [prefixWord, tailWord_1607918, baseEnd_1607918] using wordTrace_append hprefix tailTrace_1607918
  have hstable : (prefixWord ++ tailWord_1607918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607918).length < 2 ^ (prefixWord ++ tailWord_1607918).sum := by decide
  have hdescent : baseEnd_1607918 < baseStart_1607918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607948 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_1607948 : Nat := 118140960795 + 1607948 * 2 ^ 59
def prefixEnd_1607948 : Nat := 4983230072969 + 3 ^ 40 * 1607948 * 2
def baseEnd_1607948 : Nat := 550433460957186753170125

theorem tailTrace_1607948 : CollatzResearch.WordTrace tailWord_1607948 prefixEnd_1607948 550433460957186753170125 := by
  unfold tailWord_1607948
  simp only [CollatzResearch.WordTrace]
  refine ⟨29323340789343243250120249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39097787719124324333493665 29323340789343243250120249)
  ·
    refine ⟨21992505592007432437590187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29323340789343243250120249 21992505592007432437590187)
    ·
      refine ⟨32988758388011148656385281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21992505592007432437590187 32988758388011148656385281)
      ·
        refine ⟨24741568791008361492288961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32988758388011148656385281 24741568791008361492288961)
        ·
          refine ⟨18556176593256271119216721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24741568791008361492288961 18556176593256271119216721)
          ·
            refine ⟨13917132444942203339412541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18556176593256271119216721 13917132444942203339412541)
            ·
              refine ⟨5218924666853326252279703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13917132444942203339412541 5218924666853326252279703)
              ·
                refine ⟨7828387000279989378419555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218924666853326252279703 7828387000279989378419555)
                ·
                  refine ⟨11742580500419984067629333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7828387000279989378419555 11742580500419984067629333)
                  ·
                    refine ⟨550433460957186753170125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11742580500419984067629333 550433460957186753170125)
                    ·
                      rfl

theorem cell22_1607948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_1607948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607948 prefixEnd_1607948 := by exact prefixLift 1607948
  have htrace : WordTrace (prefixWord ++ tailWord_1607948) baseStart_1607948 baseEnd_1607948 := by
    simpa [prefixWord, tailWord_1607948, baseEnd_1607948] using wordTrace_append hprefix tailTrace_1607948
  have hstable : (prefixWord ++ tailWord_1607948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607948).length < 2 ^ (prefixWord ++ tailWord_1607948).sum := by decide
  have hdescent : baseEnd_1607948 < baseStart_1607948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607950 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1607950 : Nat := 118140960795 + 1607950 * 2 ^ 59
def prefixEnd_1607950 : Nat := 4983230072969 + 3 ^ 40 * 1607950 * 2
def baseEnd_1607950 : Nat := 550434145598059414620119

theorem tailTrace_1607950 : CollatzResearch.WordTrace tailWord_1607950 prefixEnd_1607950 550434145598059414620119 := by
  unfold tailWord_1607950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330844315584905105226663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39097836349786160561208869 7330844315584905105226663)
  ·
    refine ⟨10996266473377357657839995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7330844315584905105226663 10996266473377357657839995)
    ·
      refine ⟨16494399710066036486759993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10996266473377357657839995 16494399710066036486759993)
      ·
        refine ⟨12370799782549527365069995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16494399710066036486759993 12370799782549527365069995)
        ·
          refine ⟨18556199673824291047604993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370799782549527365069995 18556199673824291047604993)
          ·
            refine ⟨13917149755368218285703745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18556199673824291047604993 13917149755368218285703745)
            ·
              refine ⟨10437862316526163714277809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13917149755368218285703745 10437862316526163714277809)
              ·
                refine ⟨7828396737394622785708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10437862316526163714277809 7828396737394622785708357)
                ·
                  refine ⟨1467824388261491772320317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7828396737394622785708357 1467824388261491772320317)
                  ·
                    refine ⟨550434145598059414620119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467824388261491772320317 550434145598059414620119)
                    ·
                      rfl

theorem cell22_1607950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1607950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607950 prefixEnd_1607950 := by exact prefixLift 1607950
  have htrace : WordTrace (prefixWord ++ tailWord_1607950) baseStart_1607950 baseEnd_1607950 := by
    simpa [prefixWord, tailWord_1607950, baseEnd_1607950] using wordTrace_append hprefix tailTrace_1607950
  have hstable : (prefixWord ++ tailWord_1607950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607950).length < 2 ^ (prefixWord ++ tailWord_1607950).sum := by decide
  have hdescent : baseEnd_1607950 < baseStart_1607950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607967 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 2, 3]
def baseStart_1607967 : Nat := 118140960795 + 1607967 * 2 ^ 59
def prefixEnd_1607967 : Nat := 4983230072969 + 3 ^ 40 * 1607967 * 2
def baseEnd_1607967 : Nat := 550439965045477036945067

theorem tailTrace_1607967 : CollatzResearch.WordTrace tailWord_1607967 prefixEnd_1607967 550439965045477036945067 := by
  unfold tailWord_1607967
  simp only [CollatzResearch.WordTrace]
  refine ⟨58647374565617652745182155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39098249710411768496788103 58647374565617652745182155)
  ·
    refine ⟨87971061848426479117773233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58647374565617652745182155 87971061848426479117773233)
    ·
      refine ⟨65978296386319859338329925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87971061848426479117773233 65978296386319859338329925)
      ·
        refine ⟨12370930572434973625936861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65978296386319859338329925 12370930572434973625936861)
        ·
          refine ⟨4639098964663115109726323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12370930572434973625936861 4639098964663115109726323)
          ·
            refine ⟨6958648446994672664589485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639098964663115109726323 6958648446994672664589485)
            ·
              refine ⟨2609493167623002249221057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6958648446994672664589485 2609493167623002249221057)
              ·
                refine ⟨1957119875717251686915793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609493167623002249221057 1957119875717251686915793)
                ·
                  refine ⟨1467839906787938765186845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1957119875717251686915793 1467839906787938765186845)
                  ·
                    refine ⟨550439965045477036945067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467839906787938765186845 550439965045477036945067)
                    ·
                      rfl

theorem cell22_1607967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_1607967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1607967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1607967 prefixEnd_1607967 := by exact prefixLift 1607967
  have htrace : WordTrace (prefixWord ++ tailWord_1607967) baseStart_1607967 baseEnd_1607967 := by
    simpa [prefixWord, tailWord_1607967, baseEnd_1607967] using wordTrace_append hprefix tailTrace_1607967
  have hstable : (prefixWord ++ tailWord_1607967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607967).length < 2 ^ (prefixWord ++ tailWord_1607967).sum := by decide
  have hdescent : baseEnd_1607967 < baseStart_1607967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608008 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_1608008 : Nat := 118140960795 + 1608008 * 2 ^ 59
def prefixEnd_1608008 : Nat := 4983230072969 + 3 ^ 40 * 1608008 * 2
def baseEnd_1608008 : Nat := 183484666727788865556647

theorem tailTrace_1608008 : CollatzResearch.WordTrace tailWord_1608008 prefixEnd_1608008 183484666727788865556647 := by
  unfold tailWord_1608008
  simp only [CollatzResearch.WordTrace]
  refine ⟨29324434979234558373712339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39099246638979411164949785 29324434979234558373712339)
  ·
    refine ⟨43986652468851837560568509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29324434979234558373712339 43986652468851837560568509)
    ·
      refine ⟨16494994675819439085213191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43986652468851837560568509 16494994675819439085213191)
      ·
        refine ⟨24742492013729158627819787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16494994675819439085213191 24742492013729158627819787)
        ·
          refine ⟨37113738020593737941729681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24742492013729158627819787 37113738020593737941729681)
          ·
            refine ⟨27835303515445303456297261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37113738020593737941729681 27835303515445303456297261)
            ·
              refine ⟨10438238818291988796111473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27835303515445303456297261 10438238818291988796111473)
              ·
                refine ⟨7828679113718991597083605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438238818291988796111473 7828679113718991597083605)
                ·
                  refine ⟨183484666727788865556647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7828679113718991597083605 183484666727788865556647)
                  ·
                    rfl

theorem cell22_1608008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_1608008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608008 prefixEnd_1608008 := by exact prefixLift 1608008
  have htrace : WordTrace (prefixWord ++ tailWord_1608008) baseStart_1608008 baseEnd_1608008 := by
    simpa [prefixWord, tailWord_1608008, baseEnd_1608008] using wordTrace_append hprefix tailTrace_1608008
  have hstable : (prefixWord ++ tailWord_1608008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608008).length < 2 ^ (prefixWord ++ tailWord_1608008).sum := by decide
  have hdescent : baseEnd_1608008 < baseStart_1608008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608042 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_1608042 : Nat := 118140960795 + 1608042 * 2 ^ 59
def prefixEnd_1608042 : Nat := 4983230072969 + 3 ^ 40 * 1608042 * 2
def baseEnd_1608042 : Nat := 183488546359400613773279

theorem tailTrace_1608042 : CollatzResearch.WordTrace tailWord_1608042 prefixEnd_1608042 183488546359400613773279 := by
  unfold tailWord_1608042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662527510086485138540595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39100073360230627036108253 14662527510086485138540595)
  ·
    refine ⟨21993791265129727707810893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14662527510086485138540595 21993791265129727707810893)
    ·
      refine ⟨8247671724423647890429085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21993791265129727707810893 8247671724423647890429085)
      ·
        refine ⟨3092876896658867958910907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8247671724423647890429085 3092876896658867958910907)
        ·
          refine ⟨4639315344988301938366361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092876896658867958910907 4639315344988301938366361)
          ·
            refine ⟨3479486508741226453774771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4639315344988301938366361 3479486508741226453774771)
            ·
              refine ⟨5219229763111839680662157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479486508741226453774771 5219229763111839680662157)
              ·
                refine ⟨1957211161166939880248309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5219229763111839680662157 1957211161166939880248309)
                ·
                  refine ⟨183488546359400613773279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1957211161166939880248309 183488546359400613773279)
                  ·
                    rfl

theorem cell22_1608042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_1608042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608042 prefixEnd_1608042 := by exact prefixLift 1608042
  have htrace : WordTrace (prefixWord ++ tailWord_1608042) baseStart_1608042 baseEnd_1608042 := by
    simpa [prefixWord, tailWord_1608042, baseEnd_1608042] using wordTrace_append hprefix tailTrace_1608042
  have hstable : (prefixWord ++ tailWord_1608042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608042).length < 2 ^ (prefixWord ++ tailWord_1608042).sum := by decide
  have hdescent : baseEnd_1608042 < baseStart_1608042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608055 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1608055 : Nat := 118140960795 + 1608055 * 2 ^ 59
def prefixEnd_1608055 : Nat := 4983230072969 + 3 ^ 40 * 1608055 * 2
def baseEnd_1608055 : Nat := 550470089243874140744797

theorem tailTrace_1608055 : CollatzResearch.WordTrace tailWord_1608055 prefixEnd_1608055 550470089243874140744797 := by
  unfold tailWord_1608055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58650584189298843774385619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39100389459532562516257079 58650584189298843774385619)
  ·
    refine ⟨87975876283948265661578429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58650584189298843774385619 87975876283948265661578429)
    ·
      refine ⟨32990953606480599623091911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87975876283948265661578429 32990953606480599623091911)
      ·
        refine ⟨49486430409720899434637867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32990953606480599623091911 49486430409720899434637867)
        ·
          refine ⟨74229645614581349151956801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49486430409720899434637867 74229645614581349151956801)
          ·
            refine ⟨55672234210936011863967601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74229645614581349151956801 55672234210936011863967601)
            ·
              refine ⟨41754175658202008897975701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55672234210936011863967601 41754175658202008897975701)
              ·
                refine ⟨1957226983978219167092611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41754175658202008897975701 1957226983978219167092611)
                ·
                  refine ⟨2935840475967328750638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957226983978219167092611 2935840475967328750638917)
                  ·
                    refine ⟨550470089243874140744797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935840475967328750638917 550470089243874140744797)
                    ·
                      rfl

theorem cell22_1608055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1608055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608055 prefixEnd_1608055 := by exact prefixLift 1608055
  have htrace : WordTrace (prefixWord ++ tailWord_1608055) baseStart_1608055 baseEnd_1608055 := by
    simpa [prefixWord, tailWord_1608055, baseEnd_1608055] using wordTrace_append hprefix tailTrace_1608055
  have hstable : (prefixWord ++ tailWord_1608055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608055).length < 2 ^ (prefixWord ++ tailWord_1608055).sum := by decide
  have hdescent : baseEnd_1608055 < baseStart_1608055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608100 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1608100 : Nat := 118140960795 + 1608100 * 2 ^ 59
def prefixEnd_1608100 : Nat := 4983230072969 + 3 ^ 40 * 1608100 * 2
def baseEnd_1608100 : Nat := 550485493663509023369659

theorem tailTrace_1608100 : CollatzResearch.WordTrace tailWord_1608100 prefixEnd_1608100 550485493663509023369659 := by
  unfold tailWord_1608100
  simp only [CollatzResearch.WordTrace]
  refine ⟨29326112737067908229886877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39101483649423877639849169 29326112737067908229886877)
  ·
    refine ⟨10997292276400465586207579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29326112737067908229886877 10997292276400465586207579)
    ·
      refine ⟨16495938414600698379311369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10997292276400465586207579 16495938414600698379311369)
      ·
        refine ⟨12371953810950523784483527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16495938414600698379311369 12371953810950523784483527)
        ·
          refine ⟨18557930716425785676725291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12371953810950523784483527 18557930716425785676725291)
          ·
            refine ⟨27836896074638678515087937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18557930716425785676725291 27836896074638678515087937)
            ·
              refine ⟨20877672055979008886315953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27836896074638678515087937 20877672055979008886315953)
              ·
                refine ⟨15658254041984256664736965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20877672055979008886315953 15658254041984256664736965)
                ·
                  refine ⟨2935922632872048124638181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15658254041984256664736965 2935922632872048124638181)
                  ·
                    refine ⟨550485493663509023369659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935922632872048124638181 550485493663509023369659)
                    ·
                      rfl

theorem cell22_1608100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1608100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608100 prefixEnd_1608100 := by exact prefixLift 1608100
  have htrace : WordTrace (prefixWord ++ tailWord_1608100) baseStart_1608100 baseEnd_1608100 := by
    simpa [prefixWord, tailWord_1608100, baseEnd_1608100] using wordTrace_append hprefix tailTrace_1608100
  have hstable : (prefixWord ++ tailWord_1608100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608100).length < 2 ^ (prefixWord ++ tailWord_1608100).sum := by decide
  have hdescent : baseEnd_1608100 < baseStart_1608100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608117 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1608117 : Nat := 118140960795 + 1608117 * 2 ^ 59
def prefixEnd_1608117 : Nat := 4983230072969 + 3 ^ 40 * 1608117 * 2
def baseEnd_1608117 : Nat := 550491313110926645694607

theorem tailTrace_1608117 : CollatzResearch.WordTrace tailWord_1608117 prefixEnd_1608117 550491313110926645694607 := by
  unfold tailWord_1608117
  simp only [CollatzResearch.WordTrace]
  refine ⟨58652845515074228363142605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39101897010049485575428403 58652845515074228363142605)
  ·
    refine ⟨21994817068152835636178477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58652845515074228363142605 21994817068152835636178477)
    ·
      refine ⟨8248056400557313363566929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21994817068152835636178477 8248056400557313363566929)
      ·
        refine ⟨6186042300417985022675197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8248056400557313363566929 6186042300417985022675197)
        ·
          refine ⟨2319765862656744383503199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6186042300417985022675197 2319765862656744383503199)
          ·
            refine ⟨3479648793985116575254799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319765862656744383503199 3479648793985116575254799)
            ·
              refine ⟨5219473190977674862882199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479648793985116575254799 5219473190977674862882199)
              ·
                refine ⟨7829209786466512294323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219473190977674862882199 7829209786466512294323299)
                ·
                  refine ⟨11743814679699768441484949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829209786466512294323299 11743814679699768441484949)
                  ·
                    refine ⟨550491313110926645694607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11743814679699768441484949 550491313110926645694607)
                    ·
                      rfl

theorem cell22_1608117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1608117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608117 prefixEnd_1608117 := by exact prefixLift 1608117
  have htrace : WordTrace (prefixWord ++ tailWord_1608117) baseStart_1608117 baseEnd_1608117 := by
    simpa [prefixWord, tailWord_1608117, baseEnd_1608117] using wordTrace_append hprefix tailTrace_1608117
  have hstable : (prefixWord ++ tailWord_1608117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608117).length < 2 ^ (prefixWord ++ tailWord_1608117).sum := by decide
  have hdescent : baseEnd_1608117 < baseStart_1608117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608132 : List Nat := [2, 3, 3, 2, 2, 1, 9]
def baseStart_1608132 : Nat := 118140960795 + 1608132 * 2 ^ 59
def prefixEnd_1608132 : Nat := 4983230072969 + 3 ^ 40 * 1608132 * 2
def baseEnd_1608132 : Nat := 20388757330276726169243

theorem tailTrace_1608132 : CollatzResearch.WordTrace tailWord_1608132 prefixEnd_1608132 20388757330276726169243 := by
  unfold tailWord_1608132
  simp only [CollatzResearch.WordTrace]
  refine ⟨29326696305009942962469325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39102261740013257283292433 29326696305009942962469325)
  ·
    refine ⟨10997511114378728610925997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29326696305009942962469325 10997511114378728610925997)
    ·
      refine ⟨4124066667892023229097249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10997511114378728610925997 4124066667892023229097249)
      ·
        refine ⟨3093050000919017421822937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4124066667892023229097249 3093050000919017421822937)
        ·
          refine ⟨2319787500689263066367203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093050000919017421822937 2319787500689263066367203)
          ·
            refine ⟨3479681251033894599550805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319787500689263066367203 3479681251033894599550805)
            ·
              refine ⟨20388757330276726169243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3479681251033894599550805 20388757330276726169243)
              ·
                rfl

theorem cell22_1608132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 9].length) (baseStart_1608132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608132 prefixEnd_1608132 := by exact prefixLift 1608132
  have htrace : WordTrace (prefixWord ++ tailWord_1608132) baseStart_1608132 baseEnd_1608132 := by
    simpa [prefixWord, tailWord_1608132, baseEnd_1608132] using wordTrace_append hprefix tailTrace_1608132
  have hstable : (prefixWord ++ tailWord_1608132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608132).length < 2 ^ (prefixWord ++ tailWord_1608132).sum := by decide
  have hdescent : baseEnd_1608132 < baseStart_1608132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608224 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_1608224 : Nat := 118140960795 + 1608224 * 2 ^ 59
def prefixEnd_1608224 : Nat := 4983230072969 + 3 ^ 40 * 1608224 * 2
def baseEnd_1608224 : Nat := 550527941397614033269279

theorem tailTrace_1608224 : CollatzResearch.WordTrace tailWord_1608224 prefixEnd_1608224 550527941397614033269279 := by
  unfold tailWord_1608224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29328374062843292818643863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39104498750457723758191817 29328374062843292818643863)
  ·
    refine ⟨43992561094264939227965795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29328374062843292818643863 43992561094264939227965795)
    ·
      refine ⟨65988841641397408841948693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43992561094264939227965795 65988841641397408841948693)
      ·
        refine ⟨3093226951940503539466345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65988841641397408841948693 3093226951940503539466345)
        ·
          refine ⟨2319920213955377654599759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093226951940503539466345 2319920213955377654599759)
          ·
            refine ⟨3479880320933066481899639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319920213955377654599759 3479880320933066481899639)
            ·
              refine ⟨5219820481399599722849459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479880320933066481899639 5219820481399599722849459)
              ·
                refine ⟨7829730722099399584274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219820481399599722849459 7829730722099399584274189)
                ·
                  refine ⟨2936149020787274844102821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7829730722099399584274189 2936149020787274844102821)
                  ·
                    refine ⟨550527941397614033269279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2936149020787274844102821 550527941397614033269279)
                    ·
                      rfl

theorem cell22_1608224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_1608224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608224 prefixEnd_1608224 := by exact prefixLift 1608224
  have htrace : WordTrace (prefixWord ++ tailWord_1608224) baseStart_1608224 baseEnd_1608224 := by
    simpa [prefixWord, tailWord_1608224, baseEnd_1608224] using wordTrace_append hprefix tailTrace_1608224
  have hstable : (prefixWord ++ tailWord_1608224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608224).length < 2 ^ (prefixWord ++ tailWord_1608224).sum := by decide
  have hdescent : baseEnd_1608224 < baseStart_1608224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608235 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_1608235 : Nat := 118140960795 + 1608235 * 2 ^ 59
def prefixEnd_1608235 : Nat := 4983230072969 + 3 ^ 40 * 1608235 * 2
def baseEnd_1608235 : Nat := 550531706922413671244245

theorem tailTrace_1608235 : CollatzResearch.WordTrace tailWord_1608235 prefixEnd_1608235 550531706922413671244245 := by
  unfold tailWord_1608235
  simp only [CollatzResearch.WordTrace]
  refine ⟨58657149328646734515938159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39104766219097823010625439 58657149328646734515938159)
  ·
    refine ⟨87985723992970101773907239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58657149328646734515938159 87985723992970101773907239)
    ·
      refine ⟨131978585989455152660860859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87985723992970101773907239 131978585989455152660860859)
      ·
        refine ⟨197967878984182728991291289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131978585989455152660860859 197967878984182728991291289)
        ·
          refine ⟨148475909238137046743468467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197967878984182728991291289 148475909238137046743468467)
          ·
            refine ⟨222713863857205570115202701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148475909238137046743468467 222713863857205570115202701)
            ·
              refine ⟨83517698946452088793201013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222713863857205570115202701 83517698946452088793201013)
              ·
                refine ⟨7829784276229883324362595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83517698946452088793201013 7829784276229883324362595)
                ·
                  refine ⟨11744676414344824986543893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829784276229883324362595 11744676414344824986543893)
                  ·
                    refine ⟨550531706922413671244245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11744676414344824986543893 550531706922413671244245)
                    ·
                      rfl

theorem cell22_1608235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_1608235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608235 prefixEnd_1608235 := by exact prefixLift 1608235
  have htrace : WordTrace (prefixWord ++ tailWord_1608235) baseStart_1608235 baseEnd_1608235 := by
    simpa [prefixWord, tailWord_1608235, baseEnd_1608235] using wordTrace_append hprefix tailTrace_1608235
  have hstable : (prefixWord ++ tailWord_1608235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608235).length < 2 ^ (prefixWord ++ tailWord_1608235).sum := by decide
  have hdescent : baseEnd_1608235 < baseStart_1608235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608250 : List Nat := [3, 1, 1, 1, 3, 13]
def baseStart_1608250 : Nat := 118140960795 + 1608250 * 2 ^ 59
def prefixEnd_1608250 : Nat := 4983230072969 + 3 ^ 40 * 1608250 * 2
def baseEnd_1608250 : Nat := 6796751132456279408879

theorem tailTrace_1608250 : CollatzResearch.WordTrace tailWord_1608250 prefixEnd_1608250 6796751132456279408879 := by
  unfold tailWord_1608250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664424105898098019433551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39105130949061594718489469 14664424105898098019433551)
  ·
    refine ⟨21996636158847147029150327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14664424105898098019433551 21996636158847147029150327)
    ·
      refine ⟨32994954238270720543725491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21996636158847147029150327 32994954238270720543725491)
      ·
        refine ⟨49492431357406080815588237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32994954238270720543725491 49492431357406080815588237)
        ·
          refine ⟨18559661759027280305845589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49492431357406080815588237 18559661759027280305845589)
          ·
            refine ⟨6796751132456279408879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 18559661759027280305845589 6796751132456279408879)
            ·
              rfl

theorem cell22_1608250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 13].length) (baseStart_1608250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608250 prefixEnd_1608250 := by exact prefixLift 1608250
  have htrace : WordTrace (prefixWord ++ tailWord_1608250) baseStart_1608250 baseEnd_1608250 := by
    simpa [prefixWord, tailWord_1608250, baseEnd_1608250] using wordTrace_append hprefix tailTrace_1608250
  have hstable : (prefixWord ++ tailWord_1608250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608250).length < 2 ^ (prefixWord ++ tailWord_1608250).sum := by decide
  have hdescent : baseEnd_1608250 < baseStart_1608250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608265 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1608265 : Nat := 118140960795 + 1608265 * 2 ^ 59
def prefixEnd_1608265 : Nat := 4983230072969 + 3 ^ 40 * 1608265 * 2
def baseEnd_1608265 : Nat := 550541976535503592994153

theorem tailTrace_1608265 : CollatzResearch.WordTrace tailWord_1608265 prefixEnd_1608265 550541976535503592994153 := by
  unfold tailWord_1608265
  simp only [CollatzResearch.WordTrace]
  refine ⟨58658243518538049639530249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39105495679025366426353499 58658243518538049639530249)
  ·
    refine ⟨43993682638903537229647687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58658243518538049639530249 43993682638903537229647687)
    ·
      refine ⟨65990523958355305844471531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43993682638903537229647687 65990523958355305844471531)
      ·
        refine ⟨98985785937532958766707297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65990523958355305844471531 98985785937532958766707297)
        ·
          refine ⟨74239339453149719075030473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98985785937532958766707297 74239339453149719075030473)
          ·
            refine ⟨55679504589862289306272855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74239339453149719075030473 55679504589862289306272855)
            ·
              refine ⟨83519256884793433959409283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55679504589862289306272855 83519256884793433959409283)
              ·
                refine ⟨125278885327190150939113925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83519256884793433959409283 125278885327190150939113925)
                ·
                  refine ⟨23489790998848153301083861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125278885327190150939113925 23489790998848153301083861)
                  ·
                    refine ⟨550541976535503592994153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23489790998848153301083861 550541976535503592994153)
                    ·
                      rfl

theorem cell22_1608265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1608265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608265 prefixEnd_1608265 := by exact prefixLift 1608265
  have htrace : WordTrace (prefixWord ++ tailWord_1608265) baseStart_1608265 baseEnd_1608265 := by
    simpa [prefixWord, tailWord_1608265, baseEnd_1608265] using wordTrace_append hprefix tailTrace_1608265
  have hstable : (prefixWord ++ tailWord_1608265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608265).length < 2 ^ (prefixWord ++ tailWord_1608265).sum := by decide
  have hdescent : baseEnd_1608265 < baseStart_1608265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608316 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_1608316 : Nat := 118140960795 + 1608316 * 2 ^ 59
def prefixEnd_1608316 : Nat := 4983230072969 + 3 ^ 40 * 1608316 * 2
def baseEnd_1608316 : Nat := 550559434877756459968997

theorem tailTrace_1608316 : CollatzResearch.WordTrace tailWord_1608316 prefixEnd_1608316 550559434877756459968997 := by
  unfold tailWord_1608316
  simp only [CollatzResearch.WordTrace]
  refine ⟨29330051820676642674818401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39106735760902190233091201 29330051820676642674818401)
  ·
    refine ⟨21997538865507482006113801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29330051820676642674818401 21997538865507482006113801)
    ·
      refine ⟨16498154149130611504585351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21997538865507482006113801 16498154149130611504585351)
      ·
        refine ⟨24747231223695917256878027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16498154149130611504585351 24747231223695917256878027)
        ·
          refine ⟨37120846835543875885317041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24747231223695917256878027 37120846835543875885317041)
          ·
            refine ⟨27840635126657906913987781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37120846835543875885317041 27840635126657906913987781)
            ·
              refine ⟨5220119086248357546372709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27840635126657906913987781 5220119086248357546372709)
              ·
                refine ⟨978772328671567039944883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5220119086248357546372709 978772328671567039944883)
                ·
                  refine ⟨1468158493007350559917325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978772328671567039944883 1468158493007350559917325)
                  ·
                    refine ⟨550559434877756459968997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468158493007350559917325 550559434877756459968997)
                    ·
                      rfl

theorem cell22_1608316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_1608316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608316 prefixEnd_1608316 := by exact prefixLift 1608316
  have htrace : WordTrace (prefixWord ++ tailWord_1608316) baseStart_1608316 baseEnd_1608316 := by
    simpa [prefixWord, tailWord_1608316, baseEnd_1608316] using wordTrace_append hprefix tailTrace_1608316
  have hstable : (prefixWord ++ tailWord_1608316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608316).length < 2 ^ (prefixWord ++ tailWord_1608316).sum := by decide
  have hdescent : baseEnd_1608316 < baseStart_1608316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608322 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1608322 : Nat := 118140960795 + 1608322 * 2 ^ 59
def prefixEnd_1608322 : Nat := 4983230072969 + 3 ^ 40 * 1608322 * 2
def baseEnd_1608322 : Nat := 550561488800374444318979

theorem tailTrace_1608322 : CollatzResearch.WordTrace tailWord_1608322 prefixEnd_1608322 550561488800374444318979 := by
  unfold tailWord_1608322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14665080619832887093588805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39106881652887698916236813 14665080619832887093588805)
  ·
    refine ⟨2749702616218666330047901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14665080619832887093588805 2749702616218666330047901)
    ·
      refine ⟨1031138481081999873767963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2749702616218666330047901 1031138481081999873767963)
      ·
        refine ⟨1546707721622999810651945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031138481081999873767963 1546707721622999810651945)
        ·
          refine ⟨1160030791217249857988959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546707721622999810651945 1160030791217249857988959)
          ·
            refine ⟨1740046186825874786983439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160030791217249857988959 1740046186825874786983439)
            ·
              refine ⟨2610069280238812180475159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740046186825874786983439 2610069280238812180475159)
              ·
                refine ⟨3915103920358218270712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610069280238812180475159 3915103920358218270712739)
                ·
                  refine ⟨5872655880537327406069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915103920358218270712739 5872655880537327406069109)
                  ·
                    refine ⟨550561488800374444318979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5872655880537327406069109 550561488800374444318979)
                    ·
                      rfl

theorem cell22_1608322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1608322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608322 prefixEnd_1608322 := by exact prefixLift 1608322
  have htrace : WordTrace (prefixWord ++ tailWord_1608322) baseStart_1608322 baseEnd_1608322 := by
    simpa [prefixWord, tailWord_1608322, baseEnd_1608322] using wordTrace_append hprefix tailTrace_1608322
  have hstable : (prefixWord ++ tailWord_1608322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608322).length < 2 ^ (prefixWord ++ tailWord_1608322).sum := by decide
  have hdescent : baseEnd_1608322 < baseStart_1608322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608327 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1608327 : Nat := 118140960795 + 1608327 * 2 ^ 59
def prefixEnd_1608327 : Nat := 4983230072969 + 3 ^ 40 * 1608327 * 2
def baseEnd_1608327 : Nat := 550563200402556097943963

theorem tailTrace_1608327 : CollatzResearch.WordTrace tailWord_1608327 prefixEnd_1608327 550563200402556097943963 := by
  unfold tailWord_1608327
  simp only [CollatzResearch.WordTrace]
  refine ⟨58660504844313434228287235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39107003229542289485524823 58660504844313434228287235)
  ·
    refine ⟨87990757266470151342430853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58660504844313434228287235 87990757266470151342430853)
    ·
      refine ⟨16498266987463153376705785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87990757266470151342430853 16498266987463153376705785)
      ·
        refine ⟨12373700240597365032529339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16498266987463153376705785 12373700240597365032529339)
        ·
          refine ⟨18560550360896047548794009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12373700240597365032529339 18560550360896047548794009)
          ·
            refine ⟨13920412770672035661595507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18560550360896047548794009 13920412770672035661595507)
            ·
              refine ⟨20880619156008053492393261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13920412770672035661595507 20880619156008053492393261)
              ·
                refine ⟨7830232183503020059647473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20880619156008053492393261 7830232183503020059647473)
                ·
                  refine ⟨5872674137627265044735605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7830232183503020059647473 5872674137627265044735605)
                  ·
                    refine ⟨550563200402556097943963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5872674137627265044735605 550563200402556097943963)
                    ·
                      rfl

theorem cell22_1608327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1608327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608327 prefixEnd_1608327 := by exact prefixLift 1608327
  have htrace : WordTrace (prefixWord ++ tailWord_1608327) baseStart_1608327 baseEnd_1608327 := by
    simpa [prefixWord, tailWord_1608327, baseEnd_1608327] using wordTrace_append hprefix tailTrace_1608327
  have hstable : (prefixWord ++ tailWord_1608327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608327).length < 2 ^ (prefixWord ++ tailWord_1608327).sum := by decide
  have hdescent : baseEnd_1608327 < baseStart_1608327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608432 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_1608432 : Nat := 118140960795 + 1608432 * 2 ^ 59
def prefixEnd_1608432 : Nat := 4983230072969 + 3 ^ 40 * 1608432 * 2
def baseEnd_1608432 : Nat := 550599144048370824068641

theorem tailTrace_1608432 : CollatzResearch.WordTrace tailWord_1608432 prefixEnd_1608432 550599144048370824068641 := by
  unfold tailWord_1608432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29332167254466518580429775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39109556339288691440573033 29332167254466518580429775)
  ·
    refine ⟨43998250881699777870644663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29332167254466518580429775 43998250881699777870644663)
    ·
      refine ⟨65997376322549666805966995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43998250881699777870644663 65997376322549666805966995)
      ·
        refine ⟨98996064483824500208950493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65997376322549666805966995 98996064483824500208950493)
        ·
          refine ⟨37123524181434187578356435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98996064483824500208950493 37123524181434187578356435)
          ·
            refine ⟨55685286272151281367534653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37123524181434187578356435 55685286272151281367534653)
            ·
              refine ⟨20881982352056730512825495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55685286272151281367534653 20881982352056730512825495)
              ·
                refine ⟨31322973528085095769238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20881982352056730512825495 31322973528085095769238243)
                ·
                  refine ⟨46984460292127643653857365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31322973528085095769238243 46984460292127643653857365)
                  ·
                    refine ⟨550599144048370824068641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46984460292127643653857365 550599144048370824068641)
                    ·
                      rfl

theorem cell22_1608432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_1608432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608432 prefixEnd_1608432 := by exact prefixLift 1608432
  have htrace : WordTrace (prefixWord ++ tailWord_1608432) baseStart_1608432 baseEnd_1608432 := by
    simpa [prefixWord, tailWord_1608432, baseEnd_1608432] using wordTrace_append hprefix tailTrace_1608432
  have hstable : (prefixWord ++ tailWord_1608432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608432).length < 2 ^ (prefixWord ++ tailWord_1608432).sum := by decide
  have hdescent : baseEnd_1608432 < baseStart_1608432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608447 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 9]
def baseStart_1608447 : Nat := 118140960795 + 1608447 * 2 ^ 59
def prefixEnd_1608447 : Nat := 4983230072969 + 3 ^ 40 * 1608447 * 2
def baseEnd_1608447 : Nat := 183534759618305261647865

theorem tailTrace_1608447 : CollatzResearch.WordTrace tailWord_1608447 prefixEnd_1608447 183534759618305261647865 := by
  unfold tailWord_1608447
  simp only [CollatzResearch.WordTrace]
  refine ⟨58664881603878694722655595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39109921069252463148437063 58664881603878694722655595)
  ·
    refine ⟨87997322405818042083983393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58664881603878694722655595 87997322405818042083983393)
    ·
      refine ⟨65997991804363531562987545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87997322405818042083983393 65997991804363531562987545)
      ·
        refine ⟨49498493853272648672240659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65997991804363531562987545 49498493853272648672240659)
        ·
          refine ⟨74247740779908973008360989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49498493853272648672240659 74247740779908973008360989)
          ·
            refine ⟨27842902792465864878135371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74247740779908973008360989 27842902792465864878135371)
            ·
              refine ⟨41764354188698797317203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27842902792465864878135371 41764354188698797317203057)
              ·
                refine ⟨31323265641524097987902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41764354188698797317203057 31323265641524097987902293)
                ·
                  refine ⟨183534759618305261647865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31323265641524097987902293 183534759618305261647865)
                  ·
                    rfl

theorem cell22_1608447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_1608447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608447 prefixEnd_1608447 := by exact prefixLift 1608447
  have htrace : WordTrace (prefixWord ++ tailWord_1608447) baseStart_1608447 baseEnd_1608447 := by
    simpa [prefixWord, tailWord_1608447, baseEnd_1608447] using wordTrace_append hprefix tailTrace_1608447
  have hstable : (prefixWord ++ tailWord_1608447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608447).length < 2 ^ (prefixWord ++ tailWord_1608447).sum := by decide
  have hdescent : baseEnd_1608447 < baseStart_1608447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608479 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1608479 : Nat := 118140960795 + 1608479 * 2 ^ 59
def prefixEnd_1608479 : Nat := 4983230072969 + 3 ^ 40 * 1608479 * 2
def baseEnd_1608479 : Nat := 550615233108878368143497

theorem tailTrace_1608479 : CollatzResearch.WordTrace tailWord_1608479 prefixEnd_1608479 550615233108878368143497 := by
  unfold tailWord_1608479
  simp only [CollatzResearch.WordTrace]
  refine ⟨58666048739762764187820491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39110699159841842791880327 58666048739762764187820491)
  ·
    refine ⟨87999073109644146281730737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58666048739762764187820491 87999073109644146281730737)
    ·
      refine ⟨65999304832233109711298053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87999073109644146281730737 65999304832233109711298053)
      ·
        refine ⟨12374869656043708070868385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65999304832233109711298053 12374869656043708070868385)
        ·
          refine ⟨9281152242032781053151289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12374869656043708070868385 9281152242032781053151289)
          ·
            refine ⟨6960864181524585789863467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9281152242032781053151289 6960864181524585789863467)
            ·
              refine ⟨10441296272286878684795201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960864181524585789863467 10441296272286878684795201)
              ·
                refine ⟨7830972204215159013596401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10441296272286878684795201 7830972204215159013596401)
                ·
                  refine ⟨5873229153161369260197301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7830972204215159013596401 5873229153161369260197301)
                  ·
                    refine ⟨550615233108878368143497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5873229153161369260197301 550615233108878368143497)
                    ·
                      rfl

theorem cell22_1608479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1608479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608479 prefixEnd_1608479 := by exact prefixLift 1608479
  have htrace : WordTrace (prefixWord ++ tailWord_1608479) baseStart_1608479 baseEnd_1608479 := by
    simpa [prefixWord, tailWord_1608479, baseEnd_1608479] using wordTrace_append hprefix tailTrace_1608479
  have hstable : (prefixWord ++ tailWord_1608479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608479).length < 2 ^ (prefixWord ++ tailWord_1608479).sum := by decide
  have hdescent : baseEnd_1608479 < baseStart_1608479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608511 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 1, 4]
def baseStart_1608511 : Nat := 118140960795 + 1608511 * 2 ^ 59
def prefixEnd_1608511 : Nat := 4983230072969 + 3 ^ 40 * 1608511 * 2
def baseEnd_1608511 : Nat := 550626187362840951343399

theorem tailTrace_1608511 : CollatzResearch.WordTrace tailWord_1608511 prefixEnd_1608511 550626187362840951343399 := by
  unfold tailWord_1608511
  simp only [CollatzResearch.WordTrace]
  refine ⟨58667215875646833652985387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39111477250431222435323591 58667215875646833652985387)
  ·
    refine ⟨88000823813470250479478081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58667215875646833652985387 88000823813470250479478081)
    ·
      refine ⟨66000617860102687859608561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88000823813470250479478081 66000617860102687859608561)
      ·
        refine ⟨49500463395077015894706421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66000617860102687859608561 49500463395077015894706421)
        ·
          refine ⟨4640668443288470240128727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49500463395077015894706421 4640668443288470240128727)
          ·
            refine ⟨6961002664932705360193091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640668443288470240128727 6961002664932705360193091)
            ·
              refine ⟨10441503997399058040289637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961002664932705360193091 10441503997399058040289637)
              ·
                refine ⟨1957781999512323382554307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10441503997399058040289637 1957781999512323382554307)
                ·
                  refine ⟨2936672999268485073831461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957781999512323382554307 2936672999268485073831461)
                  ·
                    refine ⟨550626187362840951343399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2936672999268485073831461 550626187362840951343399)
                    ·
                      rfl

theorem cell22_1608511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_1608511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608511 prefixEnd_1608511 := by exact prefixLift 1608511
  have htrace : WordTrace (prefixWord ++ tailWord_1608511) baseStart_1608511 baseEnd_1608511 := by
    simpa [prefixWord, tailWord_1608511, baseEnd_1608511] using wordTrace_append hprefix tailTrace_1608511
  have hstable : (prefixWord ++ tailWord_1608511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608511).length < 2 ^ (prefixWord ++ tailWord_1608511).sum := by decide
  have hdescent : baseEnd_1608511 < baseStart_1608511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608543 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 4]
def baseStart_1608543 : Nat := 118140960795 + 1608543 * 2 ^ 59
def prefixEnd_1608543 : Nat := 4983230072969 + 3 ^ 40 * 1608543 * 2
def baseEnd_1608543 : Nat := 183545713872267844847767

theorem tailTrace_1608543 : CollatzResearch.WordTrace tailWord_1608543 prefixEnd_1608543 183545713872267844847767 := by
  unfold tailWord_1608543
  simp only [CollatzResearch.WordTrace]
  refine ⟨58668383011530903118150283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39112255341020602078766855 58668383011530903118150283)
  ·
    refine ⟨88002574517296354677225425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58668383011530903118150283 88002574517296354677225425)
    ·
      refine ⟨66001930887972266007919069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88002574517296354677225425 66001930887972266007919069)
      ·
        refine ⟨24750724082989599752969651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66001930887972266007919069 24750724082989599752969651)
        ·
          refine ⟨37126086124484399629454477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24750724082989599752969651 37126086124484399629454477)
          ·
            refine ⟨13922282296681649861045429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37126086124484399629454477 13922282296681649861045429)
            ·
              refine ⟨1305213965313904674473009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13922282296681649861045429 1305213965313904674473009)
              ·
                refine ⟨978910473985428505854757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305213965313904674473009 978910473985428505854757)
                ·
                  refine ⟨183545713872267844847767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978910473985428505854757 183545713872267844847767)
                  ·
                    rfl

theorem cell22_1608543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 4].length) (baseStart_1608543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608543 prefixEnd_1608543 := by exact prefixLift 1608543
  have htrace : WordTrace (prefixWord ++ tailWord_1608543) baseStart_1608543 baseEnd_1608543 := by
    simpa [prefixWord, tailWord_1608543, baseEnd_1608543] using wordTrace_append hprefix tailTrace_1608543
  have hstable : (prefixWord ++ tailWord_1608543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608543).length < 2 ^ (prefixWord ++ tailWord_1608543).sum := by decide
  have hdescent : baseEnd_1608543 < baseStart_1608543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608594 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_1608594 : Nat := 118140960795 + 1608594 * 2 ^ 59
def prefixEnd_1608594 : Nat := 4983230072969 + 3 ^ 40 * 1608594 * 2
def baseEnd_1608594 : Nat := 183551533319685467172715

theorem tailTrace_1608594 : CollatzResearch.WordTrace tailWord_1608594 prefixEnd_1608594 183551533319685467172715 := by
  unfold tailWord_1608594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667560783586534707064209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39113495422897425885504557 14667560783586534707064209)
  ·
    refine ⟨11000670587689901030298157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14667560783586534707064209 11000670587689901030298157)
    ·
      refine ⟨4125251470383712886361809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11000670587689901030298157 4125251470383712886361809)
      ·
        refine ⟨3093938602787784664771357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125251470383712886361809 3093938602787784664771357)
        ·
          refine ⟨1160226976045419249289259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3093938602787784664771357 1160226976045419249289259)
          ·
            refine ⟨1740340464068128873933889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160226976045419249289259 1740340464068128873933889)
            ·
              refine ⟨1305255348051096655450417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740340464068128873933889 1305255348051096655450417)
              ·
                refine ⟨978941511038322491587813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305255348051096655450417 978941511038322491587813)
                ·
                  refine ⟨183551533319685467172715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978941511038322491587813 183551533319685467172715)
                  ·
                    rfl

theorem cell22_1608594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_1608594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608594 prefixEnd_1608594 := by exact prefixLift 1608594
  have htrace : WordTrace (prefixWord ++ tailWord_1608594) baseStart_1608594 baseEnd_1608594 := by
    simpa [prefixWord, tailWord_1608594, baseEnd_1608594] using wordTrace_append hprefix tailTrace_1608594
  have hstable : (prefixWord ++ tailWord_1608594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608594).length < 2 ^ (prefixWord ++ tailWord_1608594).sum := by decide
  have hdescent : baseEnd_1608594 < baseStart_1608594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608637 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_1608637 : Nat := 118140960795 + 1608637 * 2 ^ 59
def prefixEnd_1608637 : Nat := 4983230072969 + 3 ^ 40 * 1608637 * 2
def baseEnd_1608637 : Nat := 550669319737818622693013

theorem tailTrace_1608637 : CollatzResearch.WordTrace tailWord_1608637 prefixEnd_1608637 550669319737818622693013 := by
  unfold tailWord_1608637
  simp only [CollatzResearch.WordTrace]
  refine ⟨58671811473190357172072165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39114540982126904781381443 58671811473190357172072165)
  ·
    refine ⟨11000964651223191969763531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58671811473190357172072165 11000964651223191969763531)
    ·
      refine ⟨16501446976834787954645297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11000964651223191969763531 16501446976834787954645297)
      ·
        refine ⟨12376085232626090965983973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16501446976834787954645297 12376085232626090965983973)
        ·
          refine ⟨2320515981117392056121995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12376085232626090965983973 2320515981117392056121995)
          ·
            refine ⟨3480773971676088084182993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320515981117392056121995 3480773971676088084182993)
            ·
              refine ⟨2610580478757066063137245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480773971676088084182993 2610580478757066063137245)
              ·
                refine ⟨978967679533899773676467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2610580478757066063137245 978967679533899773676467)
                ·
                  refine ⟨1468451519300849660514701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978967679533899773676467 1468451519300849660514701)
                  ·
                    refine ⟨550669319737818622693013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468451519300849660514701 550669319737818622693013)
                    ·
                      rfl

theorem cell22_1608637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_1608637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608637 prefixEnd_1608637 := by exact prefixLift 1608637
  have htrace : WordTrace (prefixWord ++ tailWord_1608637) baseStart_1608637 baseEnd_1608637 := by
    simpa [prefixWord, tailWord_1608637, baseEnd_1608637] using wordTrace_append hprefix tailTrace_1608637
  have hstable : (prefixWord ++ tailWord_1608637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608637).length < 2 ^ (prefixWord ++ tailWord_1608637).sum := by decide
  have hdescent : baseEnd_1608637 < baseStart_1608637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608676 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1608676 : Nat := 118140960795 + 1608676 * 2 ^ 59
def prefixEnd_1608676 : Nat := 4983230072969 + 3 ^ 40 * 1608676 * 2
def baseEnd_1608676 : Nat := 550682670234835520967893

theorem tailTrace_1608676 : CollatzResearch.WordTrace tailWord_1608676 prefixEnd_1608676 550682670234835520967893 := by
  unfold tailWord_1608676
  simp only [CollatzResearch.WordTrace]
  refine ⟨29336616960024533416370941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39115489280032711221827921 29336616960024533416370941)
  ·
    refine ⟨11001231360009200031139103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29336616960024533416370941 11001231360009200031139103)
    ·
      refine ⟨16501847040013800046708655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11001231360009200031139103 16501847040013800046708655)
      ·
        refine ⟨24752770560020700070062983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501847040013800046708655 24752770560020700070062983)
        ·
          refine ⟨37129155840031050105094475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24752770560020700070062983 37129155840031050105094475)
          ·
            refine ⟨55693733760046575157641713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37129155840031050105094475 55693733760046575157641713)
            ·
              refine ⟨41770300320034931368231285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55693733760046575157641713 41770300320034931368231285)
              ·
                refine ⟨3915965655003274815771683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41770300320034931368231285 3915965655003274815771683)
                ·
                  refine ⟨5873948482504912223657525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915965655003274815771683 5873948482504912223657525)
                  ·
                    refine ⟨550682670234835520967893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5873948482504912223657525 550682670234835520967893)
                    ·
                      rfl

theorem cell22_1608676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1608676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608676 prefixEnd_1608676 := by exact prefixLift 1608676
  have htrace : WordTrace (prefixWord ++ tailWord_1608676) baseStart_1608676 baseEnd_1608676 := by
    simpa [prefixWord, tailWord_1608676, baseEnd_1608676] using wordTrace_append hprefix tailTrace_1608676
  have hstable : (prefixWord ++ tailWord_1608676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608676).length < 2 ^ (prefixWord ++ tailWord_1608676).sum := by decide
  have hdescent : baseEnd_1608676 < baseStart_1608676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608727 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 2, 3]
def baseStart_1608727 : Nat := 118140960795 + 1608727 * 2 ^ 59
def prefixEnd_1608727 : Nat := 4983230072969 + 3 ^ 40 * 1608727 * 2
def baseEnd_1608727 : Nat := 550700128577088387942737

theorem tailTrace_1608727 : CollatzResearch.WordTrace tailWord_1608727 prefixEnd_1608727 550700128577088387942737 := by
  unfold tailWord_1608727
  simp only [CollatzResearch.WordTrace]
  refine ⟨58675094042864302542848435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39116729361909535028565623 58675094042864302542848435)
  ·
    refine ⟨88012641064296453814272653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58675094042864302542848435 88012641064296453814272653)
    ·
      refine ⟨33004740399111170180352245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88012641064296453814272653 33004740399111170180352245)
      ·
        refine ⟨3094194412416672204408023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33004740399111170180352245 3094194412416672204408023)
        ·
          refine ⟨4641291618625008306612035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094194412416672204408023 4641291618625008306612035)
          ·
            refine ⟨6961937427937512459918053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641291618625008306612035 6961937427937512459918053)
            ·
              refine ⟨1305363267738283586234635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6961937427937512459918053 1305363267738283586234635)
              ·
                refine ⟨1958044901607425379351953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305363267738283586234635 1958044901607425379351953)
                ·
                  refine ⟨1468533676205569034513965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958044901607425379351953 1468533676205569034513965)
                  ·
                    refine ⟨550700128577088387942737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468533676205569034513965 550700128577088387942737)
                    ·
                      rfl

theorem cell22_1608727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_1608727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608727 prefixEnd_1608727 := by exact prefixLift 1608727
  have htrace : WordTrace (prefixWord ++ tailWord_1608727) baseStart_1608727 baseEnd_1608727 := by
    simpa [prefixWord, tailWord_1608727, baseEnd_1608727] using wordTrace_append hprefix tailTrace_1608727
  have hstable : (prefixWord ++ tailWord_1608727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608727).length < 2 ^ (prefixWord ++ tailWord_1608727).sum := by decide
  have hdescent : baseEnd_1608727 < baseStart_1608727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608755 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 1, 3]
def baseStart_1608755 : Nat := 118140960795 + 1608755 * 2 ^ 59
def prefixEnd_1608755 : Nat := 4983230072969 + 3 ^ 40 * 1608755 * 2
def baseEnd_1608755 : Nat := 550709713549305648242651

theorem tailTrace_1608755 : CollatzResearch.WordTrace tailWord_1608755 prefixEnd_1608755 550709713549305648242651 := by
  unfold tailWord_1608755
  simp only [CollatzResearch.WordTrace]
  refine ⟨58676115286762863324867719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39117410191175242216578479 58676115286762863324867719)
  ·
    refine ⟨88014172930144294987301579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58676115286762863324867719 88014172930144294987301579)
    ·
      refine ⟨132021259395216442480952369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88014172930144294987301579 132021259395216442480952369)
      ·
        refine ⟨99015944546412331860714277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132021259395216442480952369 99015944546412331860714277)
        ·
          refine ⟨18565489602452312223883927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99015944546412331860714277 18565489602452312223883927)
          ·
            refine ⟨27848234403678468335825891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18565489602452312223883927 27848234403678468335825891)
            ·
              refine ⟨41772351605517702503738837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27848234403678468335825891 41772351605517702503738837)
              ·
                refine ⟨979039490754321152431379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41772351605517702503738837 979039490754321152431379)
                ·
                  refine ⟨1468559236131481728647069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979039490754321152431379 1468559236131481728647069)
                  ·
                    refine ⟨550709713549305648242651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468559236131481728647069 550709713549305648242651)
                    ·
                      rfl

theorem cell22_1608755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 3].length) (baseStart_1608755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608755 prefixEnd_1608755 := by exact prefixLift 1608755
  have htrace : WordTrace (prefixWord ++ tailWord_1608755) baseStart_1608755 baseEnd_1608755 := by
    simpa [prefixWord, tailWord_1608755, baseEnd_1608755] using wordTrace_append hprefix tailTrace_1608755
  have hstable : (prefixWord ++ tailWord_1608755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608755).length < 2 ^ (prefixWord ++ tailWord_1608755).sum := by decide
  have hdescent : baseEnd_1608755 < baseStart_1608755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608768 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_1608768 : Nat := 118140960795 + 1608768 * 2 ^ 59
def prefixEnd_1608768 : Nat := 4983230072969 + 3 ^ 40 * 1608768 * 2
def baseEnd_1608768 : Nat := 183571387904992649222537

theorem tailTrace_1608768 : CollatzResearch.WordTrace tailWord_1608768 prefixEnd_1608768 183571387904992649222537 := by
  unfold tailWord_1608768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29338294717857883272545479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39117726290477177696727305 29338294717857883272545479)
  ·
    refine ⟨44007442076786824908818219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29338294717857883272545479 44007442076786824908818219)
    ·
      refine ⟨66011163115180237363227329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44007442076786824908818219 66011163115180237363227329)
      ·
        refine ⟨49508372336385178022420497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66011163115180237363227329 49508372336385178022420497)
        ·
          refine ⟨37131279252288883516815373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49508372336385178022420497 37131279252288883516815373)
          ·
            refine ⟨13924229719608331318805765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37131279252288883516815373 13924229719608331318805765)
            ·
              refine ⟨2610793072426562122276081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13924229719608331318805765 2610793072426562122276081)
              ·
                refine ⟨1958094804319921591707061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610793072426562122276081 1958094804319921591707061)
                ·
                  refine ⟨183571387904992649222537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958094804319921591707061 183571387904992649222537)
                  ·
                    rfl

theorem cell22_1608768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_1608768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608768 prefixEnd_1608768 := by exact prefixLift 1608768
  have htrace : WordTrace (prefixWord ++ tailWord_1608768) baseStart_1608768 baseEnd_1608768 := by
    simpa [prefixWord, tailWord_1608768, baseEnd_1608768] using wordTrace_append hprefix tailTrace_1608768
  have hstable : (prefixWord ++ tailWord_1608768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608768).length < 2 ^ (prefixWord ++ tailWord_1608768).sum := by decide
  have hdescent : baseEnd_1608768 < baseStart_1608768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608862 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1608862 : Nat := 118140960795 + 1608862 * 2 ^ 59
def prefixEnd_1608862 : Nat := 4983230072969 + 3 ^ 40 * 1608862 * 2
def baseEnd_1608862 : Nat := 550746341835993035817323

theorem tailTrace_1608862 : CollatzResearch.WordTrace tailWord_1608862 prefixEnd_1608862 550746341835993035817323 := by
  unfold tailWord_1608862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335002237171902574876605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39120011931583480399341893 7335002237171902574876605)
  ·
    refine ⟨2750625838939463465578727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7335002237171902574876605 2750625838939463465578727)
    ·
      refine ⟨4125938758409195198368091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750625838939463465578727 4125938758409195198368091)
      ·
        refine ⟨6188908137613792797552137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125938758409195198368091 6188908137613792797552137)
        ·
          refine ⟨4641681103210344598164103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6188908137613792797552137 4641681103210344598164103)
          ·
            refine ⟨6962521654815516897246155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641681103210344598164103 6962521654815516897246155)
            ·
              refine ⟨10443782482223275345869233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962521654815516897246155 10443782482223275345869233)
              ·
                refine ⟨7832836861667456509401925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10443782482223275345869233 7832836861667456509401925)
                ·
                  refine ⟨1468656911562648095512861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7832836861667456509401925 1468656911562648095512861)
                  ·
                    refine ⟨550746341835993035817323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468656911562648095512861 550746341835993035817323)
                    ·
                      rfl

theorem cell22_1608862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1608862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608862 prefixEnd_1608862 := by exact prefixLift 1608862
  have htrace : WordTrace (prefixWord ++ tailWord_1608862) baseStart_1608862 baseEnd_1608862 := by
    simpa [prefixWord, tailWord_1608862, baseEnd_1608862] using wordTrace_append hprefix tailTrace_1608862
  have hstable : (prefixWord ++ tailWord_1608862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608862).length < 2 ^ (prefixWord ++ tailWord_1608862).sum := by decide
  have hdescent : baseEnd_1608862 < baseStart_1608862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608877 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1608877 : Nat := 118140960795 + 1608877 * 2 ^ 59
def prefixEnd_1608877 : Nat := 4983230072969 + 3 ^ 40 * 1608877 * 2
def baseEnd_1608877 : Nat := 550751476642537996692277

theorem tailTrace_1608877 : CollatzResearch.WordTrace tailWord_1608877 prefixEnd_1608877 550751476642537996692277 := by
  unfold tailWord_1608877
  simp only [CollatzResearch.WordTrace]
  refine ⟨58680564992320878160808885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39120376661547252107205923 58680564992320878160808885)
  ·
    refine ⟨5501302968030082327575833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58680564992320878160808885 5501302968030082327575833)
    ·
      refine ⟨4125977226022561745681875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5501302968030082327575833 4125977226022561745681875)
      ·
        refine ⟨6188965839033842618522813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125977226022561745681875 6188965839033842618522813)
        ·
          refine ⟨2320862189637690981946055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6188965839033842618522813 2320862189637690981946055)
          ·
            refine ⟨3481293284456536472919083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320862189637690981946055 3481293284456536472919083)
            ·
              refine ⟨5221939926684804709378625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481293284456536472919083 5221939926684804709378625)
              ·
                refine ⟨3916454945013603532033969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5221939926684804709378625 3916454945013603532033969)
                ·
                  refine ⟨2937341208760202649025477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916454945013603532033969 2937341208760202649025477)
                  ·
                    refine ⟨550751476642537996692277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2937341208760202649025477 550751476642537996692277)
                    ·
                      rfl

theorem cell22_1608877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1608877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608877 prefixEnd_1608877 := by exact prefixLift 1608877
  have htrace : WordTrace (prefixWord ++ tailWord_1608877) baseStart_1608877 baseEnd_1608877 := by
    simpa [prefixWord, tailWord_1608877, baseEnd_1608877] using wordTrace_append hprefix tailTrace_1608877
  have hstable : (prefixWord ++ tailWord_1608877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608877).length < 2 ^ (prefixWord ++ tailWord_1608877).sum := by decide
  have hdescent : baseEnd_1608877 < baseStart_1608877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608896 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_1608896 : Nat := 118140960795 + 1608896 * 2 ^ 59
def prefixEnd_1608896 : Nat := 4983230072969 + 3 ^ 40 * 1608896 * 2
def baseEnd_1608896 : Nat := 550757980730828280467219

theorem tailTrace_1608896 : CollatzResearch.WordTrace tailWord_1608896 prefixEnd_1608896 550757980730828280467219 := by
  unfold tailWord_1608896
  simp only [CollatzResearch.WordTrace]
  refine ⟨29340628989626022202875271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39120838652834696270500361 29340628989626022202875271)
  ·
    refine ⟨44010943484439033304312907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29340628989626022202875271 44010943484439033304312907)
    ·
      refine ⟨66016415226658549956469361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44010943484439033304312907 66016415226658549956469361)
      ·
        refine ⟨49512311419993912467352021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66016415226658549956469361 49512311419993912467352021)
        ·
          refine ⟨1160444798906107323453563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49512311419993912467352021 1160444798906107323453563)
          ·
            refine ⟨1740667198359160985180345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160444798906107323453563 1740667198359160985180345)
            ·
              refine ⟨1305500398769370738885259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740667198359160985180345 1305500398769370738885259)
              ·
                refine ⟨1958250598154056108327889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305500398769370738885259 1958250598154056108327889)
                ·
                  refine ⟨1468687948615542081245917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958250598154056108327889 1468687948615542081245917)
                  ·
                    refine ⟨550757980730828280467219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468687948615542081245917 550757980730828280467219)
                    ·
                      rfl

theorem cell22_1608896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_1608896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608896 prefixEnd_1608896 := by exact prefixLift 1608896
  have htrace : WordTrace (prefixWord ++ tailWord_1608896) baseStart_1608896 baseEnd_1608896 := by
    simpa [prefixWord, tailWord_1608896, baseEnd_1608896] using wordTrace_append hprefix tailTrace_1608896
  have hstable : (prefixWord ++ tailWord_1608896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608896).length < 2 ^ (prefixWord ++ tailWord_1608896).sum := by decide
  have hdescent : baseEnd_1608896 < baseStart_1608896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608941 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_1608941 : Nat := 118140960795 + 1608941 * 2 ^ 59
def prefixEnd_1608941 : Nat := 4983230072969 + 3 ^ 40 * 1608941 * 2
def baseEnd_1608941 : Nat := 550773385150463163092081

theorem tailTrace_1608941 : CollatzResearch.WordTrace tailWord_1608941 prefixEnd_1608941 550773385150463163092081 := by
  unfold tailWord_1608941
  simp only [CollatzResearch.WordTrace]
  refine ⟨58682899264089017091138677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39121932842726011394092451 58682899264089017091138677)
  ·
    refine ⟨5501521806008345352294251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58682899264089017091138677 5501521806008345352294251)
    ·
      refine ⟨8252282709012518028441377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5501521806008345352294251 8252282709012518028441377)
      ·
        refine ⟨6189212031759388521331033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8252282709012518028441377 6189212031759388521331033)
        ·
          refine ⟨4641909023819541390998275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6189212031759388521331033 4641909023819541390998275)
          ·
            refine ⟨6962863535729312086497413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641909023819541390998275 6962863535729312086497413)
            ·
              refine ⟨1305536912949246016218265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6962863535729312086497413 1305536912949246016218265)
              ·
                refine ⟨979152684711934512163699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305536912949246016218265 979152684711934512163699)
                ·
                  refine ⟨1468729027067901768245549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979152684711934512163699 1468729027067901768245549)
                  ·
                    refine ⟨550773385150463163092081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468729027067901768245549 550773385150463163092081)
                    ·
                      rfl

theorem cell22_1608941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_1608941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608941 prefixEnd_1608941 := by exact prefixLift 1608941
  have htrace : WordTrace (prefixWord ++ tailWord_1608941) baseStart_1608941 baseEnd_1608941 := by
    simpa [prefixWord, tailWord_1608941, baseEnd_1608941] using wordTrace_append hprefix tailTrace_1608941
  have hstable : (prefixWord ++ tailWord_1608941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608941).length < 2 ^ (prefixWord ++ tailWord_1608941).sum := by decide
  have hdescent : baseEnd_1608941 < baseStart_1608941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608984 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_1608984 : Nat := 118140960795 + 1608984 * 2 ^ 59
def prefixEnd_1608984 : Nat := 4983230072969 + 3 ^ 40 * 1608984 * 2
def baseEnd_1608984 : Nat := 550788104929225384266949

theorem tailTrace_1608984 : CollatzResearch.WordTrace tailWord_1608984 prefixEnd_1608984 550788104929225384266949 := by
  unfold tailWord_1608984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342233801466617717477003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39122978401955490289969337 29342233801466617717477003)
  ·
    refine ⟨44013350702199926576215505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29342233801466617717477003 44013350702199926576215505)
    ·
      refine ⟨33010013026649944932161629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44013350702199926576215505 33010013026649944932161629)
      ·
        refine ⟨12378754884993729349560611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33010013026649944932161629 12378754884993729349560611)
        ·
          refine ⟨18568132327490594024340917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378754884993729349560611 18568132327490594024340917)
          ·
            refine ⟨1740762405702243189781961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18568132327490594024340917 1740762405702243189781961)
            ·
              refine ⟨1305571804276682392336471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740762405702243189781961 1305571804276682392336471)
              ·
                refine ⟨1958357706415023588504707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305571804276682392336471 1958357706415023588504707)
                ·
                  refine ⟨2937536559622535382757061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958357706415023588504707 2937536559622535382757061)
                  ·
                    refine ⟨550788104929225384266949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2937536559622535382757061 550788104929225384266949)
                    ·
                      rfl

theorem cell22_1608984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_1608984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608984 prefixEnd_1608984 := by exact prefixLift 1608984
  have htrace : WordTrace (prefixWord ++ tailWord_1608984) baseStart_1608984 baseEnd_1608984 := by
    simpa [prefixWord, tailWord_1608984, baseEnd_1608984] using wordTrace_append hprefix tailTrace_1608984
  have hstable : (prefixWord ++ tailWord_1608984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608984).length < 2 ^ (prefixWord ++ tailWord_1608984).sum := by decide
  have hdescent : baseEnd_1608984 < baseStart_1608984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608997 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_1608997 : Nat := 118140960795 + 1608997 * 2 ^ 59
def prefixEnd_1608997 : Nat := 4983230072969 + 3 ^ 40 * 1608997 * 2
def baseEnd_1608997 : Nat := 550792555094897683691909

theorem tailTrace_1608997 : CollatzResearch.WordTrace tailWord_1608997 prefixEnd_1608997 550792555094897683691909 := by
  unfold tailWord_1608997
  simp only [CollatzResearch.WordTrace]
  refine ⟨58684941751886138655177245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39123294501257425770118163 58684941751886138655177245)
  ·
    refine ⟨22006853156957301995691467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58684941751886138655177245 22006853156957301995691467)
    ·
      refine ⟨33010279735435952993537201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22006853156957301995691467 33010279735435952993537201)
      ·
        refine ⟨24757709801576964745152901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33010279735435952993537201 24757709801576964745152901)
        ·
          refine ⟨4642070587795680889716169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24757709801576964745152901 4642070587795680889716169)
          ·
            refine ⟨3481552940846760667287127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4642070587795680889716169 3481552940846760667287127)
            ·
              refine ⟨5222329411270141000930691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481552940846760667287127 5222329411270141000930691)
              ·
                refine ⟨7833494116905211501396037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222329411270141000930691 7833494116905211501396037)
                ·
                  refine ⟨1468780146919727156511757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7833494116905211501396037 1468780146919727156511757)
                  ·
                    refine ⟨550792555094897683691909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468780146919727156511757 550792555094897683691909)
                    ·
                      rfl

theorem cell22_1608997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_1608997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1608997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1608997 prefixEnd_1608997 := by exact prefixLift 1608997
  have htrace : WordTrace (prefixWord ++ tailWord_1608997) baseStart_1608997 baseEnd_1608997 := by
    simpa [prefixWord, tailWord_1608997, baseEnd_1608997] using wordTrace_append hprefix tailTrace_1608997
  have hstable : (prefixWord ++ tailWord_1608997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608997).length < 2 ^ (prefixWord ++ tailWord_1608997).sum := by decide
  have hdescent : baseEnd_1608997 < baseStart_1608997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609055 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 5]
def baseStart_1609055 : Nat := 118140960795 + 1609055 * 2 ^ 59
def prefixEnd_1609055 : Nat := 4983230072969 + 3 ^ 40 * 1609055 * 2
def baseEnd_1609055 : Nat := 183604136560068288580577

theorem tailTrace_1609055 : CollatzResearch.WordTrace tailWord_1609055 prefixEnd_1609055 183604136560068288580577 := by
  unfold tailWord_1609055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58687057185676014560788619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39124704790450676373859079 58687057185676014560788619)
  ·
    refine ⟨88030585778514021841182929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58687057185676014560788619 88030585778514021841182929)
    ·
      refine ⟨66022939333885516380887197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88030585778514021841182929 66022939333885516380887197)
      ·
        refine ⟨24758602250207068642832699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66022939333885516380887197 24758602250207068642832699)
        ·
          refine ⟨37137903375310602964249049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24758602250207068642832699 37137903375310602964249049)
          ·
            refine ⟨27853427531482952223186787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37137903375310602964249049 27853427531482952223186787)
            ·
              refine ⟨41780141297224428334780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27853427531482952223186787 41780141297224428334780181)
              ·
                refine ⟨1958444123307395078192821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41780141297224428334780181 1958444123307395078192821)
                ·
                  refine ⟨183604136560068288580577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958444123307395078192821 183604136560068288580577)
                  ·
                    rfl

theorem cell22_1609055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 5].length) (baseStart_1609055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609055 prefixEnd_1609055 := by exact prefixLift 1609055
  have htrace : WordTrace (prefixWord ++ tailWord_1609055) baseStart_1609055 baseEnd_1609055 := by
    simpa [prefixWord, tailWord_1609055, baseEnd_1609055] using wordTrace_append hprefix tailTrace_1609055
  have hstable : (prefixWord ++ tailWord_1609055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609055).length < 2 ^ (prefixWord ++ tailWord_1609055).sum := by decide
  have hdescent : baseEnd_1609055 < baseStart_1609055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609059 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 3, 3]
def baseStart_1609059 : Nat := 118140960795 + 1609059 * 2 ^ 59
def prefixEnd_1609059 : Nat := 4983230072969 + 3 ^ 40 * 1609059 * 2
def baseEnd_1609059 : Nat := 550813778961950188641719

theorem tailTrace_1609059 : CollatzResearch.WordTrace tailWord_1609059 prefixEnd_1609059 550813778961950188641719 := by
  unfold tailWord_1609059
  simp only [CollatzResearch.WordTrace]
  refine ⟨58687203077661523243934231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39124802051774348829289487 58687203077661523243934231)
  ·
    refine ⟨88030804616492284865901347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58687203077661523243934231 88030804616492284865901347)
    ·
      refine ⟨132046206924738427298852021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88030804616492284865901347 132046206924738427298852021)
      ·
        refine ⟨12379331899194227559267377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132046206924738427298852021 12379331899194227559267377)
        ·
          refine ⟨9284498924395670669450533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12379331899194227559267377 9284498924395670669450533)
          ·
            refine ⟨1740843548324188250521975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9284498924395670669450533 1740843548324188250521975)
            ·
              refine ⟨2611265322486282375782963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740843548324188250521975 2611265322486282375782963)
              ·
                refine ⟨3916897983729423563674445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611265322486282375782963 3916897983729423563674445)
                ·
                  refine ⟨1468836743898533836377917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3916897983729423563674445 1468836743898533836377917)
                  ·
                    refine ⟨550813778961950188641719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468836743898533836377917 550813778961950188641719)
                    ·
                      rfl

theorem cell22_1609059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3].length) (baseStart_1609059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609059 prefixEnd_1609059 := by exact prefixLift 1609059
  have htrace : WordTrace (prefixWord ++ tailWord_1609059) baseStart_1609059 baseEnd_1609059 := by
    simpa [prefixWord, tailWord_1609059, baseEnd_1609059] using wordTrace_append hprefix tailTrace_1609059
  have hstable : (prefixWord ++ tailWord_1609059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609059).length < 2 ^ (prefixWord ++ tailWord_1609059).sum := by decide
  have hdescent : baseEnd_1609059 < baseStart_1609059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609106 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1609106 : Nat := 118140960795 + 1609106 * 2 ^ 59
def prefixEnd_1609106 : Nat := 4983230072969 + 3 ^ 40 * 1609106 * 2
def baseEnd_1609106 : Nat := 183609956007485910905525

theorem tailTrace_1609106 : CollatzResearch.WordTrace tailWord_1609106 prefixEnd_1609106 183609956007485910905525 := by
  unfold tailWord_1609106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672229327122812567723793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39125944872327500180596781 14672229327122812567723793)
  ·
    refine ⟨11004171995342109425792845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14672229327122812567723793 11004171995342109425792845)
    ·
      refine ⟨4126564498253291034672317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11004171995342109425792845 4126564498253291034672317)
      ·
        refine ⟨1547461686844984138002119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4126564498253291034672317 1547461686844984138002119)
        ·
          refine ⟨2321192530267476207003179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547461686844984138002119 2321192530267476207003179)
          ·
            refine ⟨3481788795401214310504769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321192530267476207003179 3481788795401214310504769)
            ·
              refine ⟨2611341596550910732878577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481788795401214310504769 2611341596550910732878577)
              ·
                refine ⟨1958506197413183049658933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611341596550910732878577 1958506197413183049658933)
                ·
                  refine ⟨183609956007485910905525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958506197413183049658933 183609956007485910905525)
                  ·
                    rfl

theorem cell22_1609106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1609106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609106 prefixEnd_1609106 := by exact prefixLift 1609106
  have htrace : WordTrace (prefixWord ++ tailWord_1609106) baseStart_1609106 baseEnd_1609106 := by
    simpa [prefixWord, tailWord_1609106, baseEnd_1609106] using wordTrace_append hprefix tailTrace_1609106
  have hstable : (prefixWord ++ tailWord_1609106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609106).length < 2 ^ (prefixWord ++ tailWord_1609106).sum := by decide
  have hdescent : baseEnd_1609106 < baseStart_1609106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609175 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1609175 : Nat := 118140960795 + 1609175 * 2 ^ 59
def prefixEnd_1609175 : Nat := 4983230072969 + 3 ^ 40 * 1609175 * 2
def baseEnd_1609175 : Nat := 550853488132564552741363

theorem tailTrace_1609175 : CollatzResearch.WordTrace tailWord_1609175 prefixEnd_1609175 550853488132564552741363 := by
  unfold tailWord_1609175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58691433945241275055156979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39127622630160850036771319 58691433945241275055156979)
  ·
    refine ⟨88037150917861912582735469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58691433945241275055156979 88037150917861912582735469)
    ·
      refine ⟨33013931594198217218525801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88037150917861912582735469 33013931594198217218525801)
      ·
        refine ⟨24760448695648662913894351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33013931594198217218525801 24760448695648662913894351)
        ·
          refine ⟨37140673043472994370841527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24760448695648662913894351 37140673043472994370841527)
          ·
            refine ⟨55711009565209491556262291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37140673043472994370841527 55711009565209491556262291)
            ·
              refine ⟨83566514347814237334393437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55711009565209491556262291 83566514347814237334393437)
              ·
                refine ⟨31337442880430339000397539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83566514347814237334393437 31337442880430339000397539)
                ·
                  refine ⟨47006164320645508500596309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31337442880430339000397539 47006164320645508500596309)
                  ·
                    refine ⟨550853488132564552741363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47006164320645508500596309 550853488132564552741363)
                    ·
                      rfl

theorem cell22_1609175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1609175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609175 prefixEnd_1609175 := by exact prefixLift 1609175
  have htrace : WordTrace (prefixWord ++ tailWord_1609175) baseStart_1609175 baseEnd_1609175 := by
    simpa [prefixWord, tailWord_1609175, baseEnd_1609175] using wordTrace_append hprefix tailTrace_1609175
  have hstable : (prefixWord ++ tailWord_1609175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609175).length < 2 ^ (prefixWord ++ tailWord_1609175).sum := by decide
  have hdescent : baseEnd_1609175 < baseStart_1609175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609228 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_1609228 : Nat := 118140960795 + 1609228 * 2 ^ 59
def prefixEnd_1609228 : Nat := 4983230072969 + 3 ^ 40 * 1609228 * 2
def baseEnd_1609228 : Nat := 550871631115690081166201

theorem tailTrace_1609228 : CollatzResearch.WordTrace tailWord_1609228 prefixEnd_1609228 550871631115690081166201 := by
  unfold tailWord_1609228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346683507024632553418169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39128911342699510071224225 29346683507024632553418169)
  ·
    refine ⟨22010012630268474415063627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29346683507024632553418169 22010012630268474415063627)
    ·
      refine ⟨33015018945402711622595441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22010012630268474415063627 33015018945402711622595441)
      ·
        refine ⟨24761264209052033716946581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33015018945402711622595441 24761264209052033716946581)
        ·
          refine ⟨1160684259799314080481871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24761264209052033716946581 1160684259799314080481871)
          ·
            refine ⟨1741026389698971120722807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160684259799314080481871 1741026389698971120722807)
            ·
              refine ⟨2611539584548456681084211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741026389698971120722807 2611539584548456681084211)
              ·
                refine ⟨3917309376822685021626317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611539584548456681084211 3917309376822685021626317)
                ·
                  refine ⟨1468991016308506883109869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3917309376822685021626317 1468991016308506883109869)
                  ·
                    refine ⟨550871631115690081166201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468991016308506883109869 550871631115690081166201)
                    ·
                      rfl

theorem cell22_1609228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_1609228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609228 prefixEnd_1609228 := by exact prefixLift 1609228
  have htrace : WordTrace (prefixWord ++ tailWord_1609228) baseStart_1609228 baseEnd_1609228 := by
    simpa [prefixWord, tailWord_1609228, baseEnd_1609228] using wordTrace_append hprefix tailTrace_1609228
  have hstable : (prefixWord ++ tailWord_1609228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609228).length < 2 ^ (prefixWord ++ tailWord_1609228).sum := by decide
  have hdescent : baseEnd_1609228 < baseStart_1609228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609267 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_1609267 : Nat := 118140960795 + 1609267 * 2 ^ 59
def prefixEnd_1609267 : Nat := 4983230072969 + 3 ^ 40 * 1609267 * 2
def baseEnd_1609267 : Nat := 550884981612706979441081

theorem tailTrace_1609267 : CollatzResearch.WordTrace tailWord_1609267 prefixEnd_1609267 550884981612706979441081 := by
  unfold tailWord_1609267
  simp only [CollatzResearch.WordTrace]
  refine ⟨58694789460907974767506055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39129859640605316511670703 58694789460907974767506055)
  ·
    refine ⟨88042184191361962151259083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58694789460907974767506055 88042184191361962151259083)
    ·
      refine ⟨132063276287042943226888625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88042184191361962151259083 132063276287042943226888625)
      ·
        refine ⟨99047457215282207420166469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132063276287042943226888625 99047457215282207420166469)
        ·
          refine ⟨18571398227865413891281213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99047457215282207420166469 18571398227865413891281213)
          ·
            refine ⟨6964274335449530209230455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18571398227865413891281213 6964274335449530209230455)
            ·
              refine ⟨10446411503174295313845683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964274335449530209230455 10446411503174295313845683)
              ·
                refine ⟨15669617254761442970768525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10446411503174295313845683 15669617254761442970768525)
                ·
                  refine ⟨5876106470535541114038197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15669617254761442970768525 5876106470535541114038197)
                  ·
                    refine ⟨550884981612706979441081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5876106470535541114038197 550884981612706979441081)
                    ·
                      rfl

theorem cell22_1609267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_1609267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609267 prefixEnd_1609267 := by exact prefixLift 1609267
  have htrace : WordTrace (prefixWord ++ tailWord_1609267) baseStart_1609267 baseEnd_1609267 := by
    simpa [prefixWord, tailWord_1609267, baseEnd_1609267] using wordTrace_append hprefix tailTrace_1609267
  have hstable : (prefixWord ++ tailWord_1609267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609267).length < 2 ^ (prefixWord ++ tailWord_1609267).sum := by decide
  have hdescent : baseEnd_1609267 < baseStart_1609267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609271 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 1, 4]
def baseStart_1609271 : Nat := 118140960795 + 1609271 * 2 ^ 59
def prefixEnd_1609271 : Nat := 4983230072969 + 3 ^ 40 * 1609271 * 2
def baseEnd_1609271 : Nat := 550886350894452302341069

theorem tailTrace_1609271 : CollatzResearch.WordTrace tailWord_1609271 prefixEnd_1609271 550886350894452302341069 := by
  unfold tailWord_1609271
  simp only [CollatzResearch.WordTrace]
  refine ⟨58694935352893483450651667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39129956901928988967101111 58694935352893483450651667)
  ·
    refine ⟨88042403029340225175977501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58694935352893483450651667 88042403029340225175977501)
    ·
      refine ⟨33015901136002584440991563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88042403029340225175977501 33015901136002584440991563)
      ·
        refine ⟨49523851704003876661487345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33015901136002584440991563 49523851704003876661487345)
        ·
          refine ⟨37142888778002907496115509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49523851704003876661487345 37142888778002907496115509)
          ·
            refine ⟨3482145822937772577760829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37142888778002907496115509 3482145822937772577760829)
            ·
              refine ⟨1305804683601664716660311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482145822937772577760829 1305804683601664716660311)
              ·
                refine ⟨1958707025402497074990467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305804683601664716660311 1958707025402497074990467)
                ·
                  refine ⟨2938060538103745612485701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958707025402497074990467 2938060538103745612485701)
                  ·
                    refine ⟨550886350894452302341069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938060538103745612485701 550886350894452302341069)
                    ·
                      rfl

theorem cell22_1609271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_1609271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609271 prefixEnd_1609271 := by exact prefixLift 1609271
  have htrace : WordTrace (prefixWord ++ tailWord_1609271) baseStart_1609271 baseEnd_1609271 := by
    simpa [prefixWord, tailWord_1609271, baseEnd_1609271] using wordTrace_append hprefix tailTrace_1609271
  have hstable : (prefixWord ++ tailWord_1609271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609271).length < 2 ^ (prefixWord ++ tailWord_1609271).sum := by decide
  have hdescent : baseEnd_1609271 < baseStart_1609271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609316 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1609316 : Nat := 118140960795 + 1609316 * 2 ^ 59
def prefixEnd_1609316 : Nat := 4983230072969 + 3 ^ 40 * 1609316 * 2
def baseEnd_1609316 : Nat := 550901755314087184965931

theorem tailTrace_1609316 : CollatzResearch.WordTrace tailWord_1609316 prefixEnd_1609316 550901755314087184965931 := by
  unfold tailWord_1609316
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348288318865228068019901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39131051091820304090693201 29348288318865228068019901)
  ·
    refine ⟨11005608119574460525507463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29348288318865228068019901 11005608119574460525507463)
    ·
      refine ⟨16508412179361690788261195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11005608119574460525507463 16508412179361690788261195)
      ·
        refine ⟨24762618269042536182391793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508412179361690788261195 24762618269042536182391793)
        ·
          refine ⟨18571963701781902136793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24762618269042536182391793 18571963701781902136793845)
          ·
            refine ⟨1741121597042053325324423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18571963701781902136793845 1741121597042053325324423)
            ·
              refine ⟨2611682395563079987986635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741121597042053325324423 2611682395563079987986635)
              ·
                refine ⟨3917523593344619981979953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611682395563079987986635 3917523593344619981979953)
                ·
                  refine ⟨2938142695008464986484965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917523593344619981979953 2938142695008464986484965)
                  ·
                    refine ⟨550901755314087184965931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938142695008464986484965 550901755314087184965931)
                    ·
                      rfl

theorem cell22_1609316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1609316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609316 prefixEnd_1609316 := by exact prefixLift 1609316
  have htrace : WordTrace (prefixWord ++ tailWord_1609316) baseStart_1609316 baseEnd_1609316 := by
    simpa [prefixWord, tailWord_1609316, baseEnd_1609316] using wordTrace_append hprefix tailTrace_1609316
  have hstable : (prefixWord ++ tailWord_1609316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609316).length < 2 ^ (prefixWord ++ tailWord_1609316).sum := by decide
  have hdescent : baseEnd_1609316 < baseStart_1609316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609380 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1609380 : Nat := 118140960795 + 1609380 * 2 ^ 59
def prefixEnd_1609380 : Nat := 4983230072969 + 3 ^ 40 * 1609380 * 2
def baseEnd_1609380 : Nat := 550923663822012351365735

theorem tailTrace_1609380 : CollatzResearch.WordTrace tailWord_1609380 prefixEnd_1609380 550923663822012351365735 := by
  unfold tailWord_1609380
  simp only [CollatzResearch.WordTrace]
  refine ⟨29349455454749297533184797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39132607272999063377579729 29349455454749297533184797)
  ·
    refine ⟨11006045795530986574944299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29349455454749297533184797 11006045795530986574944299)
    ·
      refine ⟨16509068693296479862416449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11006045795530986574944299 16509068693296479862416449)
      ·
        refine ⟨12381801519972359896812337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16509068693296479862416449 12381801519972359896812337)
        ·
          refine ⟨9286351139979269922609253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12381801519972359896812337 9286351139979269922609253)
          ·
            refine ⟨1741190838746113110489235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9286351139979269922609253 1741190838746113110489235)
            ·
              refine ⟨2611786258119169665733853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741190838746113110489235 2611786258119169665733853)
              ·
                refine ⟨979419846794688624650195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2611786258119169665733853 979419846794688624650195)
                ·
                  refine ⟨1469129770192032936975293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979419846794688624650195 1469129770192032936975293)
                  ·
                    refine ⟨550923663822012351365735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469129770192032936975293 550923663822012351365735)
                    ·
                      rfl

theorem cell22_1609380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1609380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609380 prefixEnd_1609380 := by exact prefixLift 1609380
  have htrace : WordTrace (prefixWord ++ tailWord_1609380) baseStart_1609380 baseEnd_1609380 := by
    simpa [prefixWord, tailWord_1609380, baseEnd_1609380] using wordTrace_append hprefix tailTrace_1609380
  have hstable : (prefixWord ++ tailWord_1609380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609380).length < 2 ^ (prefixWord ++ tailWord_1609380).sum := by decide
  have hdescent : baseEnd_1609380 < baseStart_1609380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609397 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1609397 : Nat := 118140960795 + 1609397 * 2 ^ 59
def prefixEnd_1609397 : Nat := 4983230072969 + 3 ^ 40 * 1609397 * 2
def baseEnd_1609397 : Nat := 550929483269429973690683

theorem tailTrace_1609397 : CollatzResearch.WordTrace tailWord_1609397 prefixEnd_1609397 550929483269429973690683 := by
  unfold tailWord_1609397
  simp only [CollatzResearch.WordTrace]
  refine ⟨58699530950437006969738445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39133020633624671313158963 58699530950437006969738445)
  ·
    refine ⟨22012324106413877613651917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58699530950437006969738445 22012324106413877613651917)
    ·
      refine ⟨8254621539905204105119469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22012324106413877613651917 8254621539905204105119469)
      ·
        refine ⟨3095483077464451539419801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8254621539905204105119469 3095483077464451539419801)
        ·
          refine ⟨2321612308098338654564851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095483077464451539419801 2321612308098338654564851)
          ·
            refine ⟨3482418462147507981847277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321612308098338654564851 3482418462147507981847277)
            ·
              refine ⟨1305906923305315493192729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482418462147507981847277 1305906923305315493192729)
              ·
                refine ⟨979430192478986619894547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305906923305315493192729 979430192478986619894547)
                ·
                  refine ⟨1469145288718479929841821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979430192478986619894547 1469145288718479929841821)
                  ·
                    refine ⟨550929483269429973690683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469145288718479929841821 550929483269429973690683)
                    ·
                      rfl

theorem cell22_1609397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1609397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609397 prefixEnd_1609397 := by exact prefixLift 1609397
  have htrace : WordTrace (prefixWord ++ tailWord_1609397) baseStart_1609397 baseEnd_1609397 := by
    simpa [prefixWord, tailWord_1609397, baseEnd_1609397] using wordTrace_append hprefix tailTrace_1609397
  have hstable : (prefixWord ++ tailWord_1609397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609397).length < 2 ^ (prefixWord ++ tailWord_1609397).sum := by decide
  have hdescent : baseEnd_1609397 < baseStart_1609397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609453 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1609453 : Nat := 118140960795 + 1609453 * 2 ^ 59
def prefixEnd_1609453 : Nat := 4983230072969 + 3 ^ 40 * 1609453 * 2
def baseEnd_1609453 : Nat := 550948653213864494290511

theorem tailTrace_1609453 : CollatzResearch.WordTrace tailWord_1609453 prefixEnd_1609453 550948653213864494290511 := by
  unfold tailWord_1609453
  simp only [CollatzResearch.WordTrace]
  refine ⟨58701573438234128533777013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39134382292156085689184675 58701573438234128533777013)
  ·
    refine ⟨5503272509834449550041595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58701573438234128533777013 5503272509834449550041595)
    ·
      refine ⟨8254908764751674325062393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503272509834449550041595 8254908764751674325062393)
      ·
        refine ⟨6191181573563755743796795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8254908764751674325062393 6191181573563755743796795)
        ·
          refine ⟨9286772360345633615695193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6191181573563755743796795 9286772360345633615695193)
          ·
            refine ⟨6965079270259225211771395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9286772360345633615695193 6965079270259225211771395)
            ·
              refine ⟨10447618905388837817657093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965079270259225211771395 10447618905388837817657093)
              ·
                refine ⟨1958928544760407090810705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10447618905388837817657093 1958928544760407090810705)
                ·
                  refine ⟨1469196408570305318108029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958928544760407090810705 1469196408570305318108029)
                  ·
                    refine ⟨550948653213864494290511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469196408570305318108029 550948653213864494290511)
                    ·
                      rfl

theorem cell22_1609453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1609453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609453 prefixEnd_1609453 := by exact prefixLift 1609453
  have htrace : WordTrace (prefixWord ++ tailWord_1609453) baseStart_1609453 baseEnd_1609453 := by
    simpa [prefixWord, tailWord_1609453, baseEnd_1609453] using wordTrace_append hprefix tailTrace_1609453
  have hstable : (prefixWord ++ tailWord_1609453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609453).length < 2 ^ (prefixWord ++ tailWord_1609453).sum := by decide
  have hdescent : baseEnd_1609453 < baseStart_1609453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609528 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_1609528 : Nat := 118140960795 + 1609528 * 2 ^ 59
def prefixEnd_1609528 : Nat := 4983230072969 + 3 ^ 40 * 1609528 * 2
def baseEnd_1609528 : Nat := 183658109082196432888427

theorem tailTrace_1609528 : CollatzResearch.WordTrace tailWord_1609528 prefixEnd_1609528 183658109082196432888427 := by
  unfold tailWord_1609528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352154456481208171378619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39136205941974944228504825 29352154456481208171378619)
  ·
    refine ⟨44028231684721812257067929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29352154456481208171378619 44028231684721812257067929)
    ·
      refine ⟨33021173763541359192800947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44028231684721812257067929 33021173763541359192800947)
      ·
        refine ⟨49531760645312038789201421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33021173763541359192800947 49531760645312038789201421)
        ·
          refine ⟨18574410241992014545950533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49531760645312038789201421 18574410241992014545950533)
          ·
            refine ⟨3482701920373502727365725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18574410241992014545950533 3482701920373502727365725)
            ·
              refine ⟨1306013220140063522762147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482701920373502727365725 1306013220140063522762147)
              ·
                refine ⟨1959019830210095284143221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306013220140063522762147 1959019830210095284143221)
                ·
                  refine ⟨183658109082196432888427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1959019830210095284143221 183658109082196432888427)
                  ·
                    rfl

theorem cell22_1609528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_1609528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609528 prefixEnd_1609528 := by exact prefixLift 1609528
  have htrace : WordTrace (prefixWord ++ tailWord_1609528) baseStart_1609528 baseEnd_1609528 := by
    simpa [prefixWord, tailWord_1609528, baseEnd_1609528] using wordTrace_append hprefix tailTrace_1609528
  have hstable : (prefixWord ++ tailWord_1609528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609528).length < 2 ^ (prefixWord ++ tailWord_1609528).sum := by decide
  have hdescent : baseEnd_1609528 < baseStart_1609528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609549 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1609549 : Nat := 118140960795 + 1609549 * 2 ^ 59
def prefixEnd_1609549 : Nat := 4983230072969 + 3 ^ 40 * 1609549 * 2
def baseEnd_1609549 : Nat := 550981515975752243890217

theorem tailTrace_1609549 : CollatzResearch.WordTrace tailWord_1609549 prefixEnd_1609549 550981515975752243890217 := by
  unfold tailWord_1609549
  simp only [CollatzResearch.WordTrace]
  refine ⟨58705074845886336929271701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39136716563924224619514467 58705074845886336929271701)
  ·
    refine ⟨2751800383400922043559611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58705074845886336929271701 2751800383400922043559611)
    ·
      refine ⟨4127700575101383065339417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2751800383400922043559611 4127700575101383065339417)
      ·
        refine ⟨3095775431326037299004563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4127700575101383065339417 3095775431326037299004563)
        ·
          refine ⟨4643663146989055948506845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095775431326037299004563 4643663146989055948506845)
          ·
            refine ⟨1741373680120895980690067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4643663146989055948506845 1741373680120895980690067)
            ·
              refine ⟨2612060520181343971035101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741373680120895980690067 2612060520181343971035101)
              ·
                refine ⟨979522695068003989138163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612060520181343971035101 979522695068003989138163)
                ·
                  refine ⟨1469284042602005983707245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979522695068003989138163 1469284042602005983707245)
                  ·
                    refine ⟨550981515975752243890217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469284042602005983707245 550981515975752243890217)
                    ·
                      rfl

theorem cell22_1609549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1609549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609549 prefixEnd_1609549 := by exact prefixLift 1609549
  have htrace : WordTrace (prefixWord ++ tailWord_1609549) baseStart_1609549 baseEnd_1609549 := by
    simpa [prefixWord, tailWord_1609549, baseEnd_1609549] using wordTrace_append hprefix tailTrace_1609549
  have hstable : (prefixWord ++ tailWord_1609549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609549).length < 2 ^ (prefixWord ++ tailWord_1609549).sum := by decide
  have hdescent : baseEnd_1609549 < baseStart_1609549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609586 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1609586 : Nat := 118140960795 + 1609586 * 2 ^ 59
def prefixEnd_1609586 : Nat := 4983230072969 + 3 ^ 40 * 1609586 * 2
def baseEnd_1609586 : Nat := 550994181831896480715103

theorem tailTrace_1609586 : CollatzResearch.WordTrace tailWord_1609586 prefixEnd_1609586 550994181831896480715103 := by
  unfold tailWord_1609586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676606086688073062092153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39137616231168194832245741 14676606086688073062092153)
  ·
    refine ⟨11007454565016054796569115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14676606086688073062092153 11007454565016054796569115)
    ·
      refine ⟨16511181847524082194853673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11007454565016054796569115 16511181847524082194853673)
      ·
        refine ⟨12383386385643061646140255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16511181847524082194853673 12383386385643061646140255)
        ·
          refine ⟨18575079578464592469210383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383386385643061646140255 18575079578464592469210383)
          ·
            refine ⟨27862619367696888703815575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18575079578464592469210383 27862619367696888703815575)
            ·
              refine ⟨41793929051545333055723363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27862619367696888703815575 41793929051545333055723363)
              ·
                refine ⟨62690893577317999583585045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41793929051545333055723363 62690893577317999583585045)
                ·
                  refine ⟨2938635636436781230480549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62690893577317999583585045 2938635636436781230480549)
                  ·
                    refine ⟨550994181831896480715103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938635636436781230480549 550994181831896480715103)
                    ·
                      rfl

theorem cell22_1609586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1609586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609586 prefixEnd_1609586 := by exact prefixLift 1609586
  have htrace : WordTrace (prefixWord ++ tailWord_1609586) baseStart_1609586 baseEnd_1609586 := by
    simpa [prefixWord, tailWord_1609586, baseEnd_1609586] using wordTrace_append hprefix tailTrace_1609586
  have hstable : (prefixWord ++ tailWord_1609586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609586).length < 2 ^ (prefixWord ++ tailWord_1609586).sum := by decide
  have hdescent : baseEnd_1609586 < baseStart_1609586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609603 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 2, 4]
def baseStart_1609603 : Nat := 118140960795 + 1609603 * 2 ^ 59
def prefixEnd_1609603 : Nat := 4983230072969 + 3 ^ 40 * 1609603 * 2
def baseEnd_1609603 : Nat := 551000001279314103040051

theorem tailTrace_1609603 : CollatzResearch.WordTrace tailWord_1609603 prefixEnd_1609603 551000001279314103040051 := by
  unfold tailWord_1609603
  simp only [CollatzResearch.WordTrace]
  refine ⟨58707044387690704151737463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39138029591793802767824975 58707044387690704151737463)
  ·
    refine ⟨88060566581536056227606195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58707044387690704151737463 88060566581536056227606195)
    ·
      refine ⟨132090849872304084341409293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88060566581536056227606195 132090849872304084341409293)
      ·
        refine ⟨49534068702114031628028485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132090849872304084341409293 49534068702114031628028485)
        ·
          refine ⟨9287637881646380930255341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49534068702114031628028485 9287637881646380930255341)
          ·
            refine ⟨3482864205617392848845753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9287637881646380930255341 3482864205617392848845753)
            ·
              refine ⟨2612148154213044636634315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482864205617392848845753 2612148154213044636634315)
              ·
                refine ⟨3918222231319566954951473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612148154213044636634315 3918222231319566954951473)
                ·
                  refine ⟨2938666673489675216213605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918222231319566954951473 2938666673489675216213605)
                  ·
                    refine ⟨551000001279314103040051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938666673489675216213605 551000001279314103040051)
                    ·
                      rfl

theorem cell22_1609603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_1609603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609603 prefixEnd_1609603 := by exact prefixLift 1609603
  have htrace : WordTrace (prefixWord ++ tailWord_1609603) baseStart_1609603 baseEnd_1609603 := by
    simpa [prefixWord, tailWord_1609603, baseEnd_1609603] using wordTrace_append hprefix tailTrace_1609603
  have hstable : (prefixWord ++ tailWord_1609603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609603).length < 2 ^ (prefixWord ++ tailWord_1609603).sum := by decide
  have hdescent : baseEnd_1609603 < baseStart_1609603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609624 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_1609624 : Nat := 118140960795 + 1609624 * 2 ^ 59
def prefixEnd_1609624 : Nat := 4983230072969 + 3 ^ 40 * 1609624 * 2
def baseEnd_1609624 : Nat := 183669063336159016088329

theorem tailTrace_1609624 : CollatzResearch.WordTrace tailWord_1609624 prefixEnd_1609624 183669063336159016088329 := by
  unfold tailWord_1609624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29353905160307312369125963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39138540213743083158834617 29353905160307312369125963)
  ·
    refine ⟨44030857740460968553688945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29353905160307312369125963 44030857740460968553688945)
    ·
      refine ⟨33023143305345726415266709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44030857740460968553688945 33023143305345726415266709)
      ·
        refine ⟨1547959842438080925715627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33023143305345726415266709 1547959842438080925715627)
        ·
          refine ⟨2321939763657121388573441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547959842438080925715627 2321939763657121388573441)
          ·
            refine ⟨1741454822742841041430081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2321939763657121388573441 1741454822742841041430081)
            ·
              refine ⟨1306091117057130781072561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741454822742841041430081 1306091117057130781072561)
              ·
                refine ⟨979568337792848085804421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306091117057130781072561 979568337792848085804421)
                ·
                  refine ⟨183669063336159016088329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979568337792848085804421 183669063336159016088329)
                  ·
                    rfl

theorem cell22_1609624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_1609624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609624 prefixEnd_1609624 := by exact prefixLift 1609624
  have htrace : WordTrace (prefixWord ++ tailWord_1609624) baseStart_1609624 baseEnd_1609624 := by
    simpa [prefixWord, tailWord_1609624, baseEnd_1609624] using wordTrace_append hprefix tailTrace_1609624
  have hstable : (prefixWord ++ tailWord_1609624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609624).length < 2 ^ (prefixWord ++ tailWord_1609624).sum := by decide
  have hdescent : baseEnd_1609624 < baseStart_1609624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609652 : List Nat := [2, 5, 2, 1, 2, 1, 3, 6]
def baseStart_1609652 : Nat := 118140960795 + 1609652 * 2 ^ 59
def prefixEnd_1609652 : Nat := 4983230072969 + 3 ^ 40 * 1609652 * 2
def baseEnd_1609652 : Nat := 61224086108966034284989

theorem tailTrace_1609652 : CollatzResearch.WordTrace tailWord_1609652 prefixEnd_1609652 61224086108966034284989 := by
  unfold tailWord_1609652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29354415782256592760135605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39139221043008790346847473 29354415782256592760135605)
  ·
    refine ⟨2751976479586555571262713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29354415782256592760135605 2751976479586555571262713)
    ·
      refine ⟨2063982359689916678447035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2751976479586555571262713 2063982359689916678447035)
      ·
        refine ⟨3095973539534875017670553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063982359689916678447035 3095973539534875017670553)
        ·
          refine ⟨2321980154651156263252915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095973539534875017670553 2321980154651156263252915)
          ·
            refine ⟨3482970231976734394879373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321980154651156263252915 3482970231976734394879373)
            ·
              refine ⟨1306113836991275398079765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482970231976734394879373 1306113836991275398079765)
              ·
                refine ⟨61224086108966034284989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1306113836991275398079765 61224086108966034284989)
                ·
                  rfl

theorem cell22_1609652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_1609652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609652 prefixEnd_1609652 := by exact prefixLift 1609652
  have htrace : WordTrace (prefixWord ++ tailWord_1609652) baseStart_1609652 baseEnd_1609652 := by
    simpa [prefixWord, tailWord_1609652, baseEnd_1609652] using wordTrace_append hprefix tailTrace_1609652
  have hstable : (prefixWord ++ tailWord_1609652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609652).length < 2 ^ (prefixWord ++ tailWord_1609652).sum := by decide
  have hdescent : baseEnd_1609652 < baseStart_1609652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609710 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1609710 : Nat := 118140960795 + 1609710 * 2 ^ 59
def prefixEnd_1609710 : Nat := 4983230072969 + 3 ^ 40 * 1609710 * 2
def baseEnd_1609710 : Nat := 551036629566001490614723

theorem tailTrace_1609710 : CollatzResearch.WordTrace tailWord_1609710 prefixEnd_1609710 551036629566001490614723 := by
  unfold tailWord_1609710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7338868374787882678235323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39140631332202040950588389 7338868374787882678235323)
  ·
    refine ⟨11008302562181824017352985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7338868374787882678235323 11008302562181824017352985)
    ·
      refine ⟨8256226921636368013014739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11008302562181824017352985 8256226921636368013014739)
      ·
        refine ⟨12384340382454552019522109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8256226921636368013014739 12384340382454552019522109)
        ·
          refine ⟨4644127643420457007320791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12384340382454552019522109 4644127643420457007320791)
          ·
            refine ⟨6966191465130685510981187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644127643420457007320791 6966191465130685510981187)
            ·
              refine ⟨10449287197696028266471781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966191465130685510981187 10449287197696028266471781)
              ·
                refine ⟨1959241349568005299963459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10449287197696028266471781 1959241349568005299963459)
                ·
                  refine ⟨2938862024352007949945189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959241349568005299963459 2938862024352007949945189)
                  ·
                    refine ⟨551036629566001490614723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938862024352007949945189 551036629566001490614723)
                    ·
                      rfl

theorem cell22_1609710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1609710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609710 prefixEnd_1609710 := by exact prefixLift 1609710
  have htrace : WordTrace (prefixWord ++ tailWord_1609710) baseStart_1609710 baseEnd_1609710 := by
    simpa [prefixWord, tailWord_1609710, baseEnd_1609710] using wordTrace_append hprefix tailTrace_1609710
  have hstable : (prefixWord ++ tailWord_1609710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609710).length < 2 ^ (prefixWord ++ tailWord_1609710).sum := by decide
  have hdescent : baseEnd_1609710 < baseStart_1609710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609723 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 4, 3]
def baseStart_1609723 : Nat := 118140960795 + 1609723 * 2 ^ 59
def prefixEnd_1609723 : Nat := 4983230072969 + 3 ^ 40 * 1609723 * 2
def baseEnd_1609723 : Nat := 551041079731673790039683

theorem tailTrace_1609723 : CollatzResearch.WordTrace tailWord_1609723 prefixEnd_1609723 551041079731673790039683 := by
  unfold tailWord_1609723
  simp only [CollatzResearch.WordTrace]
  refine ⟨58711421147255964646105823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39140947431503976430737215 58711421147255964646105823)
  ·
    refine ⟨88067131720883946969158735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58711421147255964646105823 88067131720883946969158735)
    ·
      refine ⟨132100697581325920453738103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88067131720883946969158735 132100697581325920453738103)
      ·
        refine ⟨198151046371988880680607155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132100697581325920453738103 198151046371988880680607155)
        ·
          refine ⟨297226569557983321020910733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198151046371988880680607155 297226569557983321020910733)
          ·
            refine ⟨111459963584243745382841525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297226569557983321020910733 111459963584243745382841525)
            ·
              refine ⟨10449371586022851129641393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111459963584243745382841525 10449371586022851129641393)
              ·
                refine ⟨7837028689517138347231045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10449371586022851129641393 7837028689517138347231045)
                ·
                  refine ⟨1469442879284463440105821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7837028689517138347231045 1469442879284463440105821)
                  ·
                    refine ⟨551041079731673790039683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469442879284463440105821 551041079731673790039683)
                    ·
                      rfl

theorem cell22_1609723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3].length) (baseStart_1609723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609723 prefixEnd_1609723 := by exact prefixLift 1609723
  have htrace : WordTrace (prefixWord ++ tailWord_1609723) baseStart_1609723 baseEnd_1609723 := by
    simpa [prefixWord, tailWord_1609723, baseEnd_1609723] using wordTrace_append hprefix tailTrace_1609723
  have hstable : (prefixWord ++ tailWord_1609723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609723).length < 2 ^ (prefixWord ++ tailWord_1609723).sum := by decide
  have hdescent : baseEnd_1609723 < baseStart_1609723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609725 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1609725 : Nat := 118140960795 + 1609725 * 2 ^ 59
def prefixEnd_1609725 : Nat := 4983230072969 + 3 ^ 40 * 1609725 * 2
def baseEnd_1609725 : Nat := 183680588124182150496559

theorem tailTrace_1609725 : CollatzResearch.WordTrace tailWord_1609725 prefixEnd_1609725 183680588124182150496559 := by
  unfold tailWord_1609725
  simp only [CollatzResearch.WordTrace]
  refine ⟨58711494093248718987678629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39140996062165812658452419 58711494093248718987678629)
  ·
    refine ⟨11008405142484134810189743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58711494093248718987678629 11008405142484134810189743)
    ·
      refine ⟨16512607713726202215284615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008405142484134810189743 16512607713726202215284615)
      ·
        refine ⟨24768911570589303322926923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16512607713726202215284615 24768911570589303322926923)
        ·
          refine ⟨37153367355883954984390385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24768911570589303322926923 37153367355883954984390385)
          ·
            refine ⟨27865025516912966238292789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37153367355883954984390385 27865025516912966238292789)
            ·
              refine ⟨2612346142210590584839949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27865025516912966238292789 2612346142210590584839949)
              ·
                refine ⟨979629803328971469314981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612346142210590584839949 979629803328971469314981)
                ·
                  refine ⟨183680588124182150496559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979629803328971469314981 183680588124182150496559)
                  ·
                    rfl

theorem cell22_1609725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1609725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609725 prefixEnd_1609725 := by exact prefixLift 1609725
  have htrace : WordTrace (prefixWord ++ tailWord_1609725) baseStart_1609725 baseEnd_1609725 := by
    simpa [prefixWord, tailWord_1609725, baseEnd_1609725] using wordTrace_append hprefix tailTrace_1609725
  have hstable : (prefixWord ++ tailWord_1609725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609725).length < 2 ^ (prefixWord ++ tailWord_1609725).sum := by decide
  have hdescent : baseEnd_1609725 < baseStart_1609725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609740 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1609740 : Nat := 118140960795 + 1609740 * 2 ^ 59
def prefixEnd_1609740 : Nat := 4983230072969 + 3 ^ 40 * 1609740 * 2
def baseEnd_1609740 : Nat := 551046899179091412364631

theorem tailTrace_1609740 : CollatzResearch.WordTrace tailWord_1609740 prefixEnd_1609740 551046899179091412364631 := by
  unfold tailWord_1609740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29356020594097188274737337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39141360792129584366316449 29356020594097188274737337)
  ·
    refine ⟨22017015445572891206053003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29356020594097188274737337 22017015445572891206053003)
    ·
      refine ⟨33025523168359336809079505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22017015445572891206053003 33025523168359336809079505)
      ·
        refine ⟨24769142376269502606809629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33025523168359336809079505 24769142376269502606809629)
        ·
          refine ⟨9288428391101063477553611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24769142376269502606809629 9288428391101063477553611)
          ·
            refine ⟨13932642586651595216330417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288428391101063477553611 13932642586651595216330417)
            ·
              refine ⟨10449481939988696412247813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13932642586651595216330417 10449481939988696412247813)
              ·
                refine ⟨1959277863747880577296465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10449481939988696412247813 1959277863747880577296465)
                ·
                  refine ⟨1469458397810910432972349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959277863747880577296465 1469458397810910432972349)
                  ·
                    refine ⟨551046899179091412364631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469458397810910432972349 551046899179091412364631)
                    ·
                      rfl

theorem cell22_1609740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1609740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609740 prefixEnd_1609740 := by exact prefixLift 1609740
  have htrace : WordTrace (prefixWord ++ tailWord_1609740) baseStart_1609740 baseEnd_1609740 := by
    simpa [prefixWord, tailWord_1609740, baseEnd_1609740] using wordTrace_append hprefix tailTrace_1609740
  have hstable : (prefixWord ++ tailWord_1609740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609740).length < 2 ^ (prefixWord ++ tailWord_1609740).sum := by decide
  have hdescent : baseEnd_1609740 < baseStart_1609740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609742 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_1609742 : Nat := 118140960795 + 1609742 * 2 ^ 59
def prefixEnd_1609742 : Nat := 4983230072969 + 3 ^ 40 * 1609742 * 2
def baseEnd_1609742 : Nat := 183682527939988024604875

theorem tailTrace_1609742 : CollatzResearch.WordTrace tailWord_1609742 prefixEnd_1609742 183682527939988024604875 := by
  unfold tailWord_1609742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339014266773391361380935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39141409422791420594031653 7339014266773391361380935)
  ·
    refine ⟨11008521400160087042071403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7339014266773391361380935 11008521400160087042071403)
    ·
      refine ⟨16512782100240130563107105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008521400160087042071403 16512782100240130563107105)
      ·
        refine ⟨12384586575180097922330329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16512782100240130563107105 12384586575180097922330329)
        ·
          refine ⟨9288439931385073441747747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12384586575180097922330329 9288439931385073441747747)
          ·
            refine ⟨13932659897077610162621621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288439931385073441747747 13932659897077610162621621)
            ·
              refine ⟨1306186865351025952745777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13932659897077610162621621 1306186865351025952745777)
              ·
                refine ⟨979640149013269464559333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306186865351025952745777 979640149013269464559333)
                ·
                  refine ⟨183682527939988024604875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979640149013269464559333 183682527939988024604875)
                  ·
                    rfl

theorem cell22_1609742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_1609742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609742 prefixEnd_1609742 := by exact prefixLift 1609742
  have htrace : WordTrace (prefixWord ++ tailWord_1609742) baseStart_1609742 baseEnd_1609742 := by
    simpa [prefixWord, tailWord_1609742, baseEnd_1609742] using wordTrace_append hprefix tailTrace_1609742
  have hstable : (prefixWord ++ tailWord_1609742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609742).length < 2 ^ (prefixWord ++ tailWord_1609742).sum := by decide
  have hdescent : baseEnd_1609742 < baseStart_1609742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609757 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1609757 : Nat := 118140960795 + 1609757 * 2 ^ 59
def prefixEnd_1609757 : Nat := 4983230072969 + 3 ^ 40 * 1609757 * 2
def baseEnd_1609757 : Nat := 551052718626509034689579

theorem tailTrace_1609757 : CollatzResearch.WordTrace tailWord_1609757 prefixEnd_1609757 551052718626509034689579 := by
  unfold tailWord_1609757
  simp only [CollatzResearch.WordTrace]
  refine ⟨58712661229132788452843525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39141774152755192301895683 58712661229132788452843525)
  ·
    refine ⟨11008623980462397834908161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58712661229132788452843525 11008623980462397834908161)
    ·
      refine ⟨8256467985346798376181121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11008623980462397834908161 8256467985346798376181121)
      ·
        refine ⟨6192350989010098782135841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8256467985346798376181121 6192350989010098782135841)
        ·
          refine ⟨4644263241757574086601881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6192350989010098782135841 4644263241757574086601881)
          ·
            refine ⟨3483197431318180564951411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4644263241757574086601881 3483197431318180564951411)
            ·
              refine ⟨5224796146977270847427117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483197431318180564951411 5224796146977270847427117)
              ·
                refine ⟨1959298555116476567785169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5224796146977270847427117 1959298555116476567785169)
                ·
                  refine ⟨1469473916337357425838877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959298555116476567785169 1469473916337357425838877)
                  ·
                    refine ⟨551052718626509034689579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469473916337357425838877 551052718626509034689579)
                    ·
                      rfl

theorem cell22_1609757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1609757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609757 prefixEnd_1609757 := by exact prefixLift 1609757
  have htrace : WordTrace (prefixWord ++ tailWord_1609757) baseStart_1609757 baseEnd_1609757 := by
    simpa [prefixWord, tailWord_1609757, baseEnd_1609757] using wordTrace_append hprefix tailTrace_1609757
  have hstable : (prefixWord ++ tailWord_1609757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609757).length < 2 ^ (prefixWord ++ tailWord_1609757).sum := by decide
  have hdescent : baseEnd_1609757 < baseStart_1609757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609813 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1609813 : Nat := 118140960795 + 1609813 * 2 ^ 59
def prefixEnd_1609813 : Nat := 4983230072969 + 3 ^ 40 * 1609813 * 2
def baseEnd_1609813 : Nat := 551071888570943555289407

theorem tailTrace_1609813 : CollatzResearch.WordTrace tailWord_1609813 prefixEnd_1609813 551071888570943555289407 := by
  unfold tailWord_1609813
  simp only [CollatzResearch.WordTrace]
  refine ⟨58714703716929910016882093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39143135811286606677921395 58714703716929910016882093)
  ·
    refine ⟨22018013893848716256330785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58714703716929910016882093 22018013893848716256330785)
    ·
      refine ⟨16513510420386537192248089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22018013893848716256330785 16513510420386537192248089)
      ·
        refine ⟨12385132815289902894186067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16513510420386537192248089 12385132815289902894186067)
        ·
          refine ⟨18577699222934854341279101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385132815289902894186067 18577699222934854341279101)
          ·
            refine ⟨6966637208600570377979663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18577699222934854341279101 6966637208600570377979663)
            ·
              refine ⟨10449955812900855566969495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966637208600570377979663 10449955812900855566969495)
              ·
                refine ⟨15674933719351283350454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10449955812900855566969495 15674933719351283350454243)
                ·
                  refine ⟨23512400579026925025681365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15674933719351283350454243 23512400579026925025681365)
                  ·
                    refine ⟨551071888570943555289407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23512400579026925025681365 551071888570943555289407)
                    ·
                      rfl

theorem cell22_1609813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1609813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609813 prefixEnd_1609813 := by exact prefixLift 1609813
  have htrace : WordTrace (prefixWord ++ tailWord_1609813) baseStart_1609813 baseEnd_1609813 := by
    simpa [prefixWord, tailWord_1609813, baseEnd_1609813] using wordTrace_append hprefix tailTrace_1609813
  have hstable : (prefixWord ++ tailWord_1609813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609813).length < 2 ^ (prefixWord ++ tailWord_1609813).sum := by decide
  have hdescent : baseEnd_1609813 < baseStart_1609813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609860 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_1609860 : Nat := 118140960795 + 1609860 * 2 ^ 59
def prefixEnd_1609860 : Nat := 4983230072969 + 3 ^ 40 * 1609860 * 2
def baseEnd_1609860 : Nat := 183695992543817033121421

theorem tailTrace_1609860 : CollatzResearch.WordTrace tailWord_1609860 prefixEnd_1609860 183695992543817033121421 := by
  unfold tailWord_1609860
  simp only [CollatzResearch.WordTrace]
  refine ⟨29358208973879818521921517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39144278631839758029228689 29358208973879818521921517)
  ·
    refine ⟨11009328365204931945720569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29358208973879818521921517 11009328365204931945720569)
    ·
      refine ⟨8256996273903698959290427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11009328365204931945720569 8256996273903698959290427)
      ·
        refine ⟨12385494410855548438935641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8256996273903698959290427 12385494410855548438935641)
        ·
          refine ⟨9289120808141661329201731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12385494410855548438935641 9289120808141661329201731)
          ·
            refine ⟨13933681212212491993802597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289120808141661329201731 13933681212212491993802597)
            ·
              refine ⟨2612565227289842248837987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13933681212212491993802597 2612565227289842248837987)
              ·
                refine ⟨3918847840934763373256981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612565227289842248837987 3918847840934763373256981)
                ·
                  refine ⟨183695992543817033121421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3918847840934763373256981 183695992543817033121421)
                  ·
                    rfl

theorem cell22_1609860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_1609860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609860 prefixEnd_1609860 := by exact prefixLift 1609860
  have htrace : WordTrace (prefixWord ++ tailWord_1609860) baseStart_1609860 baseEnd_1609860 := by
    simpa [prefixWord, tailWord_1609860, baseEnd_1609860] using wordTrace_append hprefix tailTrace_1609860
  have hstable : (prefixWord ++ tailWord_1609860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609860).length < 2 ^ (prefixWord ++ tailWord_1609860).sum := by decide
  have hdescent : baseEnd_1609860 < baseStart_1609860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609967 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 5]
def baseStart_1609967 : Nat := 118140960795 + 1609967 * 2 ^ 59
def prefixEnd_1609967 : Nat := 4983230072969 + 3 ^ 40 * 1609967 * 2
def baseEnd_1609967 : Nat := 183708201972712828979645

theorem tailTrace_1609967 : CollatzResearch.WordTrace tailWord_1609967 prefixEnd_1609967 183708201972712828979645 := by
  unfold tailWord_1609967
  simp only [CollatzResearch.WordTrace]
  refine ⟨58720320558371994317988155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39146880372247996211992103 58720320558371994317988155)
  ·
    refine ⟨88080480837557991476982233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58720320558371994317988155 88080480837557991476982233)
    ·
      refine ⟨66060360628168493607736675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88080480837557991476982233 66060360628168493607736675)
      ·
        refine ⟨99090540942252740411605013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66060360628168493607736675 99090540942252740411605013)
        ·
          refine ⟨4644869106668097206793985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99090540942252740411605013 4644869106668097206793985)
          ·
            refine ⟨3483651830001072905095489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4644869106668097206793985 3483651830001072905095489)
            ·
              refine ⟨2612738872500804678821617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483651830001072905095489 2612738872500804678821617)
              ·
                refine ⟨1959554154375603509116213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612738872500804678821617 1959554154375603509116213)
                ·
                  refine ⟨183708201972712828979645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1959554154375603509116213 183708201972712828979645)
                  ·
                    rfl

theorem cell22_1609967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 5].length) (baseStart_1609967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609967 prefixEnd_1609967 := by exact prefixLift 1609967
  have htrace : WordTrace (prefixWord ++ tailWord_1609967) baseStart_1609967 baseEnd_1609967 := by
    simpa [prefixWord, tailWord_1609967, baseEnd_1609967] using wordTrace_append hprefix tailTrace_1609967
  have hstable : (prefixWord ++ tailWord_1609967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609967).length < 2 ^ (prefixWord ++ tailWord_1609967).sum := by decide
  have hdescent : baseEnd_1609967 < baseStart_1609967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609982 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1609982 : Nat := 118140960795 + 1609982 * 2 ^ 59
def prefixEnd_1609982 : Nat := 4983230072969 + 3 ^ 40 * 1609982 * 2
def baseEnd_1609982 : Nat := 551129740724683447813889

theorem tailTrace_1609982 : CollatzResearch.WordTrace tailWord_1609982 prefixEnd_1609982 551129740724683447813889 := by
  unfold tailWord_1609982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340108456664706484973025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39147245102211767919856133 7340108456664706484973025)
  ·
    refine ⟨5505081342498529863729769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7340108456664706484973025 5505081342498529863729769)
    ·
      refine ⟨4128811006873897397797327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505081342498529863729769 4128811006873897397797327)
      ·
        refine ⟨6193216510310846096695991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128811006873897397797327 6193216510310846096695991)
        ·
          refine ⟨9289824765466269145043987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193216510310846096695991 9289824765466269145043987)
          ·
            refine ⟨13934737148199403717565981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289824765466269145043987 13934737148199403717565981)
            ·
              refine ⟨5225526430574776394087243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13934737148199403717565981 5225526430574776394087243)
              ·
                refine ⟨7838289645862164591130865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225526430574776394087243 7838289645862164591130865)
                ·
                  refine ⟨5878717234396623443348149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7838289645862164591130865 5878717234396623443348149)
                  ·
                    refine ⟨551129740724683447813889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5878717234396623443348149 551129740724683447813889)
                    ·
                      rfl

theorem cell22_1609982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1609982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609982 prefixEnd_1609982 := by exact prefixLift 1609982
  have htrace : WordTrace (prefixWord ++ tailWord_1609982) baseStart_1609982 baseEnd_1609982 := by
    simpa [prefixWord, tailWord_1609982, baseEnd_1609982] using wordTrace_append hprefix tailTrace_1609982
  have hstable : (prefixWord ++ tailWord_1609982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609982).length < 2 ^ (prefixWord ++ tailWord_1609982).sum := by decide
  have hdescent : baseEnd_1609982 < baseStart_1609982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609995 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 6]
def baseStart_1609995 : Nat := 118140960795 + 1609995 * 2 ^ 59
def prefixEnd_1609995 : Nat := 4983230072969 + 3 ^ 40 * 1609995 * 2
def baseEnd_1609995 : Nat := 183711396963451915746283

theorem tailTrace_1609995 : CollatzResearch.WordTrace tailWord_1609995 prefixEnd_1609995 183711396963451915746283 := by
  unfold tailWord_1609995
  simp only [CollatzResearch.WordTrace]
  refine ⟨58721341802270555100007439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39147561201513703400004959 58721341802270555100007439)
  ·
    refine ⟨88082012703405832650011159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58721341802270555100007439 88082012703405832650011159)
    ·
      refine ⟨132123019055108748975016739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88082012703405832650011159 132123019055108748975016739)
      ·
        refine ⟨198184528582663123462525109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132123019055108748975016739 198184528582663123462525109)
        ·
          refine ⟨18579799554624667824611729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198184528582663123462525109 18579799554624667824611729)
          ·
            refine ⟨13934849665968500868458797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18579799554624667824611729 13934849665968500868458797)
            ·
              refine ⟨5225568624738187825672049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13934849665968500868458797 5225568624738187825672049)
              ·
                refine ⟨3919176468553640869254037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225568624738187825672049 3919176468553640869254037)
                ·
                  refine ⟨183711396963451915746283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3919176468553640869254037 183711396963451915746283)
                  ·
                    rfl

theorem cell22_1609995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_1609995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1609995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1609995 prefixEnd_1609995 := by exact prefixLift 1609995
  have htrace : WordTrace (prefixWord ++ tailWord_1609995) baseStart_1609995 baseEnd_1609995 := by
    simpa [prefixWord, tailWord_1609995, baseEnd_1609995] using wordTrace_append hprefix tailTrace_1609995
  have hstable : (prefixWord ++ tailWord_1609995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609995).length < 2 ^ (prefixWord ++ tailWord_1609995).sum := by decide
  have hdescent : baseEnd_1609995 < baseStart_1609995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610055 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1610055 : Nat := 118140960795 + 1610055 * 2 ^ 59
def prefixEnd_1610055 : Nat := 4983230072969 + 3 ^ 40 * 1610055 * 2
def baseEnd_1610055 : Nat := 551154730116535590738665

theorem tailTrace_1610055 : CollatzResearch.WordTrace tailWord_1610055 prefixEnd_1610055 551154730116535590738665 := by
  unfold tailWord_1610055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58723530182053185347191619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39149020121368790231461079 58723530182053185347191619)
  ·
    refine ⟨88085295273079778020787429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58723530182053185347191619 88085295273079778020787429)
    ·
      refine ⟨16515992863702458378897643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88085295273079778020787429 16515992863702458378897643)
      ·
        refine ⟨24773989295553687568346465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16515992863702458378897643 24773989295553687568346465)
        ·
          refine ⟨18580491971665265676259849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24773989295553687568346465 18580491971665265676259849)
          ·
            refine ⟨13935368978748949257194887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18580491971665265676259849 13935368978748949257194887)
            ·
              refine ⟨20903053468123423885792331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13935368978748949257194887 20903053468123423885792331)
              ·
                refine ⟨31354580202185135828688497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20903053468123423885792331 31354580202185135828688497)
                ·
                  refine ⟨23515935151638851871516373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31354580202185135828688497 23515935151638851871516373)
                  ·
                    refine ⟨551154730116535590738665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23515935151638851871516373 551154730116535590738665)
                    ·
                      rfl

theorem cell22_1610055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1610055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610055 prefixEnd_1610055 := by exact prefixLift 1610055
  have htrace : WordTrace (prefixWord ++ tailWord_1610055) baseStart_1610055 baseEnd_1610055 := by
    simpa [prefixWord, tailWord_1610055, baseEnd_1610055] using wordTrace_append hprefix tailTrace_1610055
  have hstable : (prefixWord ++ tailWord_1610055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610055).length < 2 ^ (prefixWord ++ tailWord_1610055).sum := by decide
  have hdescent : baseEnd_1610055 < baseStart_1610055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610076 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1610076 : Nat := 118140960795 + 1610076 * 2 ^ 59
def prefixEnd_1610076 : Nat := 4983230072969 + 3 ^ 40 * 1610076 * 2
def baseEnd_1610076 : Nat := 551161918845698535963601

theorem tailTrace_1610076 : CollatzResearch.WordTrace tailWord_1610076 prefixEnd_1610076 551161918845698535963601 := by
  unfold tailWord_1610076
  simp only [CollatzResearch.WordTrace]
  refine ⟨29362148057488552966853041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39149530743318070622470721 29362148057488552966853041)
  ·
    refine ⟨22021611043116414725139781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29362148057488552966853041 22021611043116414725139781)
    ·
      refine ⟨4129052070584327760963709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22021611043116414725139781 4129052070584327760963709)
      ·
        refine ⟨1548394526469122910361391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4129052070584327760963709 1548394526469122910361391)
        ·
          refine ⟨2322591789703684365542087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548394526469122910361391 2322591789703684365542087)
          ·
            refine ⟨3483887684555526548313131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322591789703684365542087 3483887684555526548313131)
            ·
              refine ⟨5225831526833289822469697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483887684555526548313131 5225831526833289822469697)
              ·
                refine ⟨3919373645124967366852273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225831526833289822469697 3919373645124967366852273)
                ·
                  refine ⟨2939530233843725525139205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3919373645124967366852273 2939530233843725525139205)
                  ·
                    refine ⟨551161918845698535963601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2939530233843725525139205 551161918845698535963601)
                    ·
                      rfl

theorem cell22_1610076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1610076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610076 prefixEnd_1610076 := by exact prefixLift 1610076
  have htrace : WordTrace (prefixWord ++ tailWord_1610076) baseStart_1610076 baseEnd_1610076 := by
    simpa [prefixWord, tailWord_1610076, baseEnd_1610076] using wordTrace_append hprefix tailTrace_1610076
  have hstable : (prefixWord ++ tailWord_1610076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610076).length < 2 ^ (prefixWord ++ tailWord_1610076).sum := by decide
  have hdescent : baseEnd_1610076 < baseStart_1610076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610196 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1610196 : Nat := 118140960795 + 1610196 * 2 ^ 59
def prefixEnd_1610196 : Nat := 4983230072969 + 3 ^ 40 * 1610196 * 2
def baseEnd_1610196 : Nat := 551202997298058222963233

theorem tailTrace_1610196 : CollatzResearch.WordTrace tailWord_1610196 prefixEnd_1610196 551202997298058222963233 := by
  unfold tailWord_1610196
  simp only [CollatzResearch.WordTrace]
  refine ⟨29364336437271183214037221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39152448583028244285382961 29364336437271183214037221)
  ·
    refine ⟨5505813081988346852631979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29364336437271183214037221 5505813081988346852631979)
    ·
      refine ⟨8258719622982520278947969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5505813081988346852631979 8258719622982520278947969)
      ·
        refine ⟨6194039717236890209210977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8258719622982520278947969 6194039717236890209210977)
        ·
          refine ⟨4645529787927667656908233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194039717236890209210977 4645529787927667656908233)
          ·
            refine ⟨3484147340945750742681175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4645529787927667656908233 3484147340945750742681175)
            ·
              refine ⟨5226221011418626114021763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484147340945750742681175 5226221011418626114021763)
              ·
                refine ⟨7839331517127939171032645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226221011418626114021763 7839331517127939171032645)
                ·
                  refine ⟨1469874659461488594568621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7839331517127939171032645 1469874659461488594568621)
                  ·
                    refine ⟨551202997298058222963233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469874659461488594568621 551202997298058222963233)
                    ·
                      rfl

theorem cell22_1610196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1610196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610196 prefixEnd_1610196 := by exact prefixLift 1610196
  have htrace : WordTrace (prefixWord ++ tailWord_1610196) baseStart_1610196 baseEnd_1610196 := by
    simpa [prefixWord, tailWord_1610196, baseEnd_1610196] using wordTrace_append hprefix tailTrace_1610196
  have hstable : (prefixWord ++ tailWord_1610196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610196).length < 2 ^ (prefixWord ++ tailWord_1610196).sum := by decide
  have hdescent : baseEnd_1610196 < baseStart_1610196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610213 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_1610213 : Nat := 118140960795 + 1610213 * 2 ^ 59
def prefixEnd_1610213 : Nat := 4983230072969 + 3 ^ 40 * 1610213 * 2
def baseEnd_1610213 : Nat := 551208816745475845288181

theorem tailTrace_1610213 : CollatzResearch.WordTrace tailWord_1610213 prefixEnd_1610213 551208816745475845288181 := by
  unfold tailWord_1610213
  simp only [CollatzResearch.WordTrace]
  refine ⟨58729292915480778331443293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39152861943653852220962195 58729292915480778331443293)
  ·
    refine ⟨22023484843305291874291235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58729292915480778331443293 22023484843305291874291235)
    ·
      refine ⟨33035227264957937811436853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023484843305291874291235 33035227264957937811436853)
      ·
        refine ⟨3097052556089806669822205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33035227264957937811436853 3097052556089806669822205)
        ·
          refine ⟨1161394708533677501183327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3097052556089806669822205 1161394708533677501183327)
          ·
            refine ⟨1742092062800516251774991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161394708533677501183327 1742092062800516251774991)
            ·
              refine ⟨2613138094200774377662487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742092062800516251774991 2613138094200774377662487)
              ·
                refine ⟨3919707141301161566493731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613138094200774377662487 3919707141301161566493731)
                ·
                  refine ⟨5879560711951742349740597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919707141301161566493731 5879560711951742349740597)
                  ·
                    refine ⟨551208816745475845288181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5879560711951742349740597 551208816745475845288181)
                    ·
                      rfl

theorem cell22_1610213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_1610213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610213 prefixEnd_1610213 := by exact prefixLift 1610213
  have htrace : WordTrace (prefixWord ++ tailWord_1610213) baseStart_1610213 baseEnd_1610213 := by
    simpa [prefixWord, tailWord_1610213, baseEnd_1610213] using wordTrace_append hprefix tailTrace_1610213
  have hstable : (prefixWord ++ tailWord_1610213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610213).length < 2 ^ (prefixWord ++ tailWord_1610213).sum := by decide
  have hdescent : baseEnd_1610213 < baseStart_1610213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610224 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_1610224 : Nat := 118140960795 + 1610224 * 2 ^ 59
def prefixEnd_1610224 : Nat := 4983230072969 + 3 ^ 40 * 1610224 * 2
def baseEnd_1610224 : Nat := 551212582270275483263147

theorem tailTrace_1610224 : CollatzResearch.WordTrace tailWord_1610224 prefixEnd_1610224 551212582270275483263147 := by
  unfold tailWord_1610224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29364847059220463605046863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39153129412293951473395817 29364847059220463605046863)
  ·
    refine ⟨44047270588830695407570295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29364847059220463605046863 44047270588830695407570295)
    ·
      refine ⟨66070905883246043111355443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44047270588830695407570295 66070905883246043111355443)
      ·
        refine ⟨99106358824869064667033165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66070905883246043111355443 99106358824869064667033165)
        ·
          refine ⟨37164884559325899250137437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99106358824869064667033165 37164884559325899250137437)
          ·
            refine ⟨13936831709747212218801539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37164884559325899250137437 13936831709747212218801539)
            ·
              refine ⟨20905247564620818328202309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936831709747212218801539 20905247564620818328202309)
              ·
                refine ⟨3919733918366403436537933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20905247564620818328202309 3919733918366403436537933)
                ·
                  refine ⟨1469900219387401288701725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3919733918366403436537933 1469900219387401288701725)
                  ·
                    refine ⟨551212582270275483263147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469900219387401288701725 551212582270275483263147)
                    ·
                      rfl

theorem cell22_1610224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_1610224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610224 prefixEnd_1610224 := by exact prefixLift 1610224
  have htrace : WordTrace (prefixWord ++ tailWord_1610224) baseStart_1610224 baseEnd_1610224 := by
    simpa [prefixWord, tailWord_1610224, baseEnd_1610224] using wordTrace_append hprefix tailTrace_1610224
  have hstable : (prefixWord ++ tailWord_1610224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610224).length < 2 ^ (prefixWord ++ tailWord_1610224).sum := by decide
  have hdescent : baseEnd_1610224 < baseStart_1610224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610237 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 9]
def baseStart_1610237 : Nat := 118140960795 + 1610237 * 2 ^ 59
def prefixEnd_1610237 : Nat := 4983230072969 + 3 ^ 40 * 1610237 * 2
def baseEnd_1610237 : Nat := 183739010811982594229369

theorem tailTrace_1610237 : CollatzResearch.WordTrace tailWord_1610237 prefixEnd_1610237 183739010811982594229369 := by
  unfold tailWord_1610237
  simp only [CollatzResearch.WordTrace]
  refine ⟨58730168267393830430316965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39153445511595886953544643 58730168267393830430316965)
  ·
    refine ⟨11011906550136343205684431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58730168267393830430316965 11011906550136343205684431)
    ·
      refine ⟨16517859825204514808526647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11011906550136343205684431 16517859825204514808526647)
      ·
        refine ⟨24776789737806772212789971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16517859825204514808526647 24776789737806772212789971)
        ·
          refine ⟨37165184606710158319184957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24776789737806772212789971 37165184606710158319184957)
          ·
            refine ⟨13936944227516309369694359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37165184606710158319184957 13936944227516309369694359)
            ·
              refine ⟨20905416341274464054541539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936944227516309369694359 20905416341274464054541539)
              ·
                refine ⟨31358124511911696081812309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20905416341274464054541539 31358124511911696081812309)
                ·
                  refine ⟨183739010811982594229369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31358124511911696081812309 183739010811982594229369)
                  ·
                    rfl

theorem cell22_1610237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_1610237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610237 prefixEnd_1610237 := by exact prefixLift 1610237
  have htrace : WordTrace (prefixWord ++ tailWord_1610237) baseStart_1610237 baseEnd_1610237 := by
    simpa [prefixWord, tailWord_1610237, baseEnd_1610237] using wordTrace_append hprefix tailTrace_1610237
  have hstable : (prefixWord ++ tailWord_1610237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610237).length < 2 ^ (prefixWord ++ tailWord_1610237).sum := by decide
  have hdescent : baseEnd_1610237 < baseStart_1610237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610254 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1610254 : Nat := 118140960795 + 1610254 * 2 ^ 59
def prefixEnd_1610254 : Nat := 4983230072969 + 3 ^ 40 * 1610254 * 2
def baseEnd_1610254 : Nat := 183740950627788468337685

theorem tailTrace_1610254 : CollatzResearch.WordTrace tailWord_1610254 prefixEnd_1610254 183740950627788468337685 := by
  unfold tailWord_1610254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341348538541530291710727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39153858872221494889123877 7341348538541530291710727)
  ·
    refine ⟨11012022807812295437566091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7341348538541530291710727 11012022807812295437566091)
    ·
      refine ⟨16518034211718443156349137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012022807812295437566091 16518034211718443156349137)
      ·
        refine ⟨12388525658788832367261853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16518034211718443156349137 12388525658788832367261853)
        ·
          refine ⟨4645697122045812137723195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12388525658788832367261853 4645697122045812137723195)
          ·
            refine ⟨6968545683068718206584793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645697122045812137723195 6968545683068718206584793)
            ·
              refine ⟨5226409262301538654938595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6968545683068718206584793 5226409262301538654938595)
              ·
                refine ⟨7839613893452307982407893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226409262301538654938595 7839613893452307982407893)
                ·
                  refine ⟨183740950627788468337685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7839613893452307982407893 183740950627788468337685)
                  ·
                    rfl

theorem cell22_1610254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1610254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610254 prefixEnd_1610254 := by exact prefixLift 1610254
  have htrace : WordTrace (prefixWord ++ tailWord_1610254) baseStart_1610254 baseEnd_1610254 := by
    simpa [prefixWord, tailWord_1610254, baseEnd_1610254] using wordTrace_append hprefix tailTrace_1610254
  have hstable : (prefixWord ++ tailWord_1610254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610254).length < 2 ^ (prefixWord ++ tailWord_1610254).sum := by decide
  have hdescent : baseEnd_1610254 < baseStart_1610254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610316 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_1610316 : Nat := 118140960795 + 1610316 * 2 ^ 59
def prefixEnd_1610316 : Nat := 4983230072969 + 3 ^ 40 * 1610316 * 2
def baseEnd_1610316 : Nat := 183748025250139303320955

theorem tailTrace_1610316 : CollatzResearch.WordTrace tailWord_1610316 prefixEnd_1610316 183748025250139303320955 := by
  unfold tailWord_1610316
  simp only [CollatzResearch.WordTrace]
  refine ⟨29366524817053813461221401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39155366422738417948295201 29366524817053813461221401)
  ·
    refine ⟨22024893612790360095916051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29366524817053813461221401 22024893612790360095916051)
    ·
      refine ⟨33037340419185540143874077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22024893612790360095916051 33037340419185540143874077)
      ·
        refine ⟨12389002657194577553952779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33037340419185540143874077 12389002657194577553952779)
        ·
          refine ⟨18583503985791866330929169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12389002657194577553952779 18583503985791866330929169)
          ·
            refine ⟨13937627989343899748196877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18583503985791866330929169 13937627989343899748196877)
            ·
              refine ⟨5226610496003962405573829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13937627989343899748196877 5226610496003962405573829)
              ·
                refine ⟨979989468000742951045093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5226610496003962405573829 979989468000742951045093)
                ·
                  refine ⟨183748025250139303320955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979989468000742951045093 183748025250139303320955)
                  ·
                    rfl

theorem cell22_1610316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_1610316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610316 prefixEnd_1610316 := by exact prefixLift 1610316
  have htrace : WordTrace (prefixWord ++ tailWord_1610316) baseStart_1610316 baseEnd_1610316 := by
    simpa [prefixWord, tailWord_1610316, baseEnd_1610316] using wordTrace_append hprefix tailTrace_1610316
  have hstable : (prefixWord ++ tailWord_1610316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610316).length < 2 ^ (prefixWord ++ tailWord_1610316).sum := by decide
  have hdescent : baseEnd_1610316 < baseStart_1610316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610365 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_1610365 : Nat := 118140960795 + 1610365 * 2 ^ 59
def prefixEnd_1610365 : Nat := 4983230072969 + 3 ^ 40 * 1610365 * 2
def baseEnd_1610365 : Nat := 551260849451798115487715

theorem tailTrace_1610365 : CollatzResearch.WordTrace tailWord_1610365 prefixEnd_1610365 551260849451798115487715 := by
  unfold tailWord_1610365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58734836810930108290976549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39156557873953405527317699 58734836810930108290976549)
  ·
    refine ⟨11012781902049395304558103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58734836810930108290976549 11012781902049395304558103)
    ·
      refine ⟨16519172853074092956837155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012781902049395304558103 16519172853074092956837155)
      ·
        refine ⟨24778759279611139435255733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16519172853074092956837155 24778759279611139435255733)
        ·
          refine ⟨2323008682463544322055225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24778759279611139435255733 2323008682463544322055225)
          ·
            refine ⟨1742256511847658241541419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323008682463544322055225 1742256511847658241541419)
            ·
              refine ⟨2613384767771487362312129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742256511847658241541419 2613384767771487362312129)
              ·
                refine ⟨1960038575828615521734097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2613384767771487362312129 1960038575828615521734097)
                ·
                  refine ⟨1470028931871461641300573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960038575828615521734097 1470028931871461641300573)
                  ·
                    refine ⟨551260849451798115487715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470028931871461641300573 551260849451798115487715)
                    ·
                      rfl

theorem cell22_1610365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_1610365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610365 prefixEnd_1610365 := by exact prefixLift 1610365
  have htrace : WordTrace (prefixWord ++ tailWord_1610365) baseStart_1610365 baseEnd_1610365 := by
    simpa [prefixWord, tailWord_1610365, baseEnd_1610365] using wordTrace_append hprefix tailTrace_1610365
  have hstable : (prefixWord ++ tailWord_1610365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610365).length < 2 ^ (prefixWord ++ tailWord_1610365).sum := by decide
  have hdescent : baseEnd_1610365 < baseStart_1610365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610479 : List Nat := [1, 1, 2, 1, 5, 12]
def baseStart_1610479 : Nat := 118140960795 + 1610479 * 2 ^ 59
def prefixEnd_1610479 : Nat := 4983230072969 + 3 ^ 40 * 1610479 * 2
def baseEnd_1610479 : Nat := 6806171283722713804165

theorem tailTrace_1610479 : CollatzResearch.WordTrace tailWord_1610479 prefixEnd_1610479 6806171283722713804165 := by
  unfold tailWord_1610479
  simp only [CollatzResearch.WordTrace]
  refine ⟨58738994732517105760626491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39159329821678070507084327 58738994732517105760626491)
  ·
    refine ⟨88108492098775658640939737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58738994732517105760626491 88108492098775658640939737)
    ·
      refine ⟨66081369074081743980704803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88108492098775658640939737 66081369074081743980704803)
      ·
        refine ⟨99122053611122615971057205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66081369074081743980704803 99122053611122615971057205)
        ·
          refine ⟨9292692526042745247286613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99122053611122615971057205 9292692526042745247286613)
          ·
            refine ⟨6806171283722713804165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9292692526042745247286613 6806171283722713804165)
            ·
              rfl

theorem cell22_1610479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 12].length) (baseStart_1610479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610479 prefixEnd_1610479 := by exact prefixLift 1610479
  have htrace : WordTrace (prefixWord ++ tailWord_1610479) baseStart_1610479 baseEnd_1610479 := by
    simpa [prefixWord, tailWord_1610479, baseEnd_1610479] using wordTrace_append hprefix tailTrace_1610479
  have hstable : (prefixWord ++ tailWord_1610479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610479).length < 2 ^ (prefixWord ++ tailWord_1610479).sum := by decide
  have hdescent : baseEnd_1610479 < baseStart_1610479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610481 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1610481 : Nat := 118140960795 + 1610481 * 2 ^ 59
def prefixEnd_1610481 : Nat := 4983230072969 + 3 ^ 40 * 1610481 * 2
def baseEnd_1610481 : Nat := 551300558622412479587359

theorem tailTrace_1610481 : CollatzResearch.WordTrace tailWord_1610481 prefixEnd_1610481 551300558622412479587359 := by
  unfold tailWord_1610481
  simp only [CollatzResearch.WordTrace]
  refine ⟨58739067678509860102199297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39159378452339906734799531 58739067678509860102199297)
  ·
    refine ⟨44054300758882395076649473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58739067678509860102199297 44054300758882395076649473)
    ·
      refine ⟨33040725569161796307487105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44054300758882395076649473 33040725569161796307487105)
      ·
        refine ⟨24780544176871347230615329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33040725569161796307487105 24780544176871347230615329)
        ·
          refine ⟨18585408132653510422961497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24780544176871347230615329 18585408132653510422961497)
          ·
            refine ⟨13939056099490132817221123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18585408132653510422961497 13939056099490132817221123)
            ·
              refine ⟨20908584149235199225831685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13939056099490132817221123 20908584149235199225831685)
              ·
                refine ⟨3920359527981599854843441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20908584149235199225831685 3920359527981599854843441)
                ·
                  refine ⟨2940269645986199891132581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920359527981599854843441 2940269645986199891132581)
                  ·
                    refine ⟨551300558622412479587359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2940269645986199891132581 551300558622412479587359)
                    ·
                      rfl

theorem cell22_1610481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1610481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610481 prefixEnd_1610481 := by exact prefixLift 1610481
  have htrace : WordTrace (prefixWord ++ tailWord_1610481) baseStart_1610481 baseEnd_1610481 := by
    simpa [prefixWord, tailWord_1610481, baseEnd_1610481] using wordTrace_append hprefix tailTrace_1610481
  have hstable : (prefixWord ++ tailWord_1610481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610481).length < 2 ^ (prefixWord ++ tailWord_1610481).sum := by decide
  have hdescent : baseEnd_1610481 < baseStart_1610481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610545 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 1, 3]
def baseStart_1610545 : Nat := 118140960795 + 1610545 * 2 ^ 59
def prefixEnd_1610545 : Nat := 4983230072969 + 3 ^ 40 * 1610545 * 2
def baseEnd_1610545 : Nat := 551322467130337645987163

theorem tailTrace_1610545 : CollatzResearch.WordTrace tailWord_1610545 prefixEnd_1610545 551322467130337645987163 := by
  unfold tailWord_1610545
  simp only [CollatzResearch.WordTrace]
  refine ⟨58741401950277999032529089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39160934633518666021686059 58741401950277999032529089)
  ·
    refine ⟨44056051462708499274396817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58741401950277999032529089 44056051462708499274396817)
    ·
      refine ⟨33042038597031374455797613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44056051462708499274396817 33042038597031374455797613)
      ·
        refine ⟨12390764473886765420924105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33042038597031374455797613 12390764473886765420924105)
        ·
          refine ⟨9293073355415074065693079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12390764473886765420924105 9293073355415074065693079)
          ·
            refine ⟨13939610033122611098539619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293073355415074065693079 13939610033122611098539619)
            ·
              refine ⟨20909415049683916647809429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13939610033122611098539619 20909415049683916647809429)
              ·
                refine ⟨980128830453933592866067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20909415049683916647809429 980128830453933592866067)
                ·
                  refine ⟨1470193245680900389299101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980128830453933592866067 1470193245680900389299101)
                  ·
                    refine ⟨551322467130337645987163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470193245680900389299101 551322467130337645987163)
                    ·
                      rfl

theorem cell22_1610545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_1610545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610545 prefixEnd_1610545 := by exact prefixLift 1610545
  have htrace : WordTrace (prefixWord ++ tailWord_1610545) baseStart_1610545 baseEnd_1610545 := by
    simpa [prefixWord, tailWord_1610545, baseEnd_1610545] using wordTrace_append hprefix tailTrace_1610545
  have hstable : (prefixWord ++ tailWord_1610545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610545).length < 2 ^ (prefixWord ++ tailWord_1610545).sum := by decide
  have hdescent : baseEnd_1610545 < baseStart_1610545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610564 : List Nat := [2, 3, 4, 2, 2, 1, 2, 6]
def baseStart_1610564 : Nat := 118140960795 + 1610564 * 2 ^ 59
def prefixEnd_1610564 : Nat := 4983230072969 + 3 ^ 40 * 1610564 * 2
def baseEnd_1610564 : Nat := 61258774579847547751345

theorem tailTrace_1610564 : CollatzResearch.WordTrace tailWord_1610564 prefixEnd_1610564 61258774579847547751345 := by
  unfold tailWord_1610564
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371047468604582638735373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39161396624806110184980497 29371047468604582638735373)
  ·
    refine ⟨11014142800726718489525765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29371047468604582638735373 11014142800726718489525765)
    ·
      refine ⟨2065151775136259716786081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11014142800726718489525765 2065151775136259716786081)
      ·
        refine ⟨1548863831352194787589561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065151775136259716786081 1548863831352194787589561)
        ·
          refine ⟨1161647873514146090692171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548863831352194787589561 1161647873514146090692171)
          ·
            refine ⟨1742471810271219136038257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161647873514146090692171 1742471810271219136038257)
            ·
              refine ⟨1306853857703414352028693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742471810271219136038257 1306853857703414352028693)
              ·
                refine ⟨61258774579847547751345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1306853857703414352028693 61258774579847547751345)
                ·
                  rfl

theorem cell22_1610564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_1610564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610564 prefixEnd_1610564 := by exact prefixLift 1610564
  have htrace : WordTrace (prefixWord ++ tailWord_1610564) baseStart_1610564 baseEnd_1610564 := by
    simpa [prefixWord, tailWord_1610564, baseEnd_1610564] using wordTrace_append hprefix tailTrace_1610564
  have hstable : (prefixWord ++ tailWord_1610564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610564).length < 2 ^ (prefixWord ++ tailWord_1610564).sum := by decide
  have hdescent : baseEnd_1610564 < baseStart_1610564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610603 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 4]
def baseStart_1610603 : Nat := 118140960795 + 1610603 * 2 ^ 59
def prefixEnd_1610603 : Nat := 4983230072969 + 3 ^ 40 * 1610603 * 2
def baseEnd_1610603 : Nat := 183780773905214942678995

theorem tailTrace_1610603 : CollatzResearch.WordTrace tailWord_1610603 prefixEnd_1610603 183780773905214942678995 := by
  unfold tailWord_1610603
  simp only [CollatzResearch.WordTrace]
  refine ⟨58743517384067874938140463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39162344922711916625426975 58743517384067874938140463)
  ·
    refine ⟨88115276076101812407210695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58743517384067874938140463 88115276076101812407210695)
    ·
      refine ⟨132172914114152718610816043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88115276076101812407210695 132172914114152718610816043)
      ·
        refine ⟨198259371171229077916224065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132172914114152718610816043 198259371171229077916224065)
        ·
          refine ⟨148694528378421808437168049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198259371171229077916224065 148694528378421808437168049)
          ·
            refine ⟨111520896283816356327876037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148694528378421808437168049 111520896283816356327876037)
            ·
              refine ⟨20910168053215566811476757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111520896283816356327876037 20910168053215566811476757)
              ·
                refine ⟨980164127494479694287973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20910168053215566811476757 980164127494479694287973)
                ·
                  refine ⟨183780773905214942678995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980164127494479694287973 183780773905214942678995)
                  ·
                    rfl

theorem cell22_1610603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 4].length) (baseStart_1610603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610603 prefixEnd_1610603 := by exact prefixLift 1610603
  have htrace : WordTrace (prefixWord ++ tailWord_1610603) baseStart_1610603 baseEnd_1610603 := by
    simpa [prefixWord, tailWord_1610603, baseEnd_1610603] using wordTrace_append hprefix tailTrace_1610603
  have hstable : (prefixWord ++ tailWord_1610603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610603).length < 2 ^ (prefixWord ++ tailWord_1610603).sum := by decide
  have hdescent : baseEnd_1610603 < baseStart_1610603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610616 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_1610616 : Nat := 118140960795 + 1610616 * 2 ^ 59
def prefixEnd_1610616 : Nat := 4983230072969 + 3 ^ 40 * 1610616 * 2
def baseEnd_1610616 : Nat := 551346771881317127461945

theorem tailTrace_1610616 : CollatzResearch.WordTrace tailWord_1610616 prefixEnd_1610616 551346771881317127461945 := by
  unfold tailWord_1610616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371995766510389079181851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39162661022013852105575801 29371995766510389079181851)
  ·
    refine ⟨44057993649765583618772777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29371995766510389079181851 44057993649765583618772777)
    ·
      refine ⟨33043495237324187714079583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44057993649765583618772777 33043495237324187714079583)
      ·
        refine ⟨49565242855986281571119375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33043495237324187714079583 49565242855986281571119375)
        ·
          refine ⟨74347864283979422356679063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49565242855986281571119375 74347864283979422356679063)
          ·
            refine ⟨111521796425969133535018595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74347864283979422356679063 111521796425969133535018595)
            ·
              refine ⟨167282694638953700302527893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111521796425969133535018595 167282694638953700302527893)
              ·
                refine ⟨7841376311200954701680995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167282694638953700302527893 7841376311200954701680995)
                ·
                  refine ⟨11762064466801432052521493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7841376311200954701680995 11762064466801432052521493)
                  ·
                    refine ⟨551346771881317127461945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11762064466801432052521493 551346771881317127461945)
                    ·
                      rfl

theorem cell22_1610616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_1610616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610616 prefixEnd_1610616 := by exact prefixLift 1610616
  have htrace : WordTrace (prefixWord ++ tailWord_1610616) baseStart_1610616 baseEnd_1610616 := by
    simpa [prefixWord, tailWord_1610616, baseEnd_1610616] using wordTrace_append hprefix tailTrace_1610616
  have hstable : (prefixWord ++ tailWord_1610616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610616).length < 2 ^ (prefixWord ++ tailWord_1610616).sum := by decide
  have hdescent : baseEnd_1610616 < baseStart_1610616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610622 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1610622 : Nat := 118140960795 + 1610622 * 2 ^ 59
def prefixEnd_1610622 : Nat := 4983230072969 + 3 ^ 40 * 1610622 * 2
def baseEnd_1610622 : Nat := 551348825803935111811927

theorem tailTrace_1610622 : CollatzResearch.WordTrace tailWord_1610622 prefixEnd_1610622 551348825803935111811927 := by
  unfold tailWord_1610622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343026296374880147885265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39162806913999360788721413 7343026296374880147885265)
  ·
    refine ⟨5507269722281160110913949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7343026296374880147885265 5507269722281160110913949)
    ·
      refine ⟨2065226145855435041592731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5507269722281160110913949 2065226145855435041592731)
      ·
        refine ⟨3097839218783152562389097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065226145855435041592731 3097839218783152562389097)
        ·
          refine ⟨2323379414087364421791823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3097839218783152562389097 2323379414087364421791823)
          ·
            refine ⟨3485069121131046632687735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323379414087364421791823 3485069121131046632687735)
            ·
              refine ⟨5227603681696569949031603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485069121131046632687735 5227603681696569949031603)
              ·
                refine ⟨7841405522544854923547405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227603681696569949031603 7841405522544854923547405)
                ·
                  refine ⟨2940527070954320596330277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7841405522544854923547405 2940527070954320596330277)
                  ·
                    refine ⟨551348825803935111811927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2940527070954320596330277 551348825803935111811927)
                    ·
                      rfl

theorem cell22_1610622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1610622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610622 prefixEnd_1610622 := by exact prefixLift 1610622
  have htrace : WordTrace (prefixWord ++ tailWord_1610622) baseStart_1610622 baseEnd_1610622 := by
    simpa [prefixWord, tailWord_1610622, baseEnd_1610622] using wordTrace_append hprefix tailTrace_1610622
  have hstable : (prefixWord ++ tailWord_1610622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610622).length < 2 ^ (prefixWord ++ tailWord_1610622).sum := by decide
  have hdescent : baseEnd_1610622 < baseStart_1610622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610633 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_1610633 : Nat := 118140960795 + 1610633 * 2 ^ 59
def prefixEnd_1610633 : Nat := 4983230072969 + 3 ^ 40 * 1610633 * 2
def baseEnd_1610633 : Nat := 551352591328734749786893

theorem tailTrace_1610633 : CollatzResearch.WordTrace tailWord_1610633 prefixEnd_1610633 551352591328734749786893 := by
  unfold tailWord_1610633
  simp only [CollatzResearch.WordTrace]
  refine ⟨58744611573959190061732553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39163074382639460041155035 58744611573959190061732553)
  ·
    refine ⟨44058458680469392546299415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58744611573959190061732553 44058458680469392546299415)
    ·
      refine ⟨66087688020704088819449123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44058458680469392546299415 66087688020704088819449123)
      ·
        refine ⟨99131532031056133229173685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66087688020704088819449123 99131532031056133229173685)
        ·
          refine ⟨9293581127911512490235033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99131532031056133229173685 9293581127911512490235033)
          ·
            refine ⟨6970185845933634367676275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293581127911512490235033 6970185845933634367676275)
            ·
              refine ⟨10455278768900451551514413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970185845933634367676275 10455278768900451551514413)
              ·
                refine ⟨3920729538337669331817905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10455278768900451551514413 3920729538337669331817905)
                ·
                  refine ⟨2940547153753251998863429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920729538337669331817905 2940547153753251998863429)
                  ·
                    refine ⟨551352591328734749786893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2940547153753251998863429 551352591328734749786893)
                    ·
                      rfl

theorem cell22_1610633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_1610633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610633 prefixEnd_1610633 := by exact prefixLift 1610633
  have htrace : WordTrace (prefixWord ++ tailWord_1610633) baseStart_1610633 baseEnd_1610633 := by
    simpa [prefixWord, tailWord_1610633, baseEnd_1610633] using wordTrace_append hprefix tailTrace_1610633
  have hstable : (prefixWord ++ tailWord_1610633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610633).length < 2 ^ (prefixWord ++ tailWord_1610633).sum := by decide
  have hdescent : baseEnd_1610633 < baseStart_1610633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610680 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_1610680 : Nat := 118140960795 + 1610680 * 2 ^ 59
def prefixEnd_1610680 : Nat := 4983230072969 + 3 ^ 40 * 1610680 * 2
def baseEnd_1610680 : Nat := 551368680389242293861749

theorem tailTrace_1610680 : CollatzResearch.WordTrace tailWord_1610680 prefixEnd_1610680 551368680389242293861749 := by
  unfold tailWord_1610680
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373162902394458544346747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39164217203192611392462329 29373162902394458544346747)
  ·
    refine ⟨44059744353591687816520121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29373162902394458544346747 44059744353591687816520121)
    ·
      refine ⟨33044808265193765862390091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44059744353591687816520121 33044808265193765862390091)
      ·
        refine ⟨49567212397790648793585137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33044808265193765862390091 49567212397790648793585137)
        ·
          refine ⟨37175409298342986595188853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49567212397790648793585137 37175409298342986595188853)
          ·
            refine ⟨3485194621719654993298955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37175409298342986595188853 3485194621719654993298955)
            ·
              refine ⟨5227791932579482489948433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485194621719654993298955 5227791932579482489948433)
              ·
                refine ⟨3920843949434611867461325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5227791932579482489948433 3920843949434611867461325)
                ·
                  refine ⟨1470316481037979450297997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3920843949434611867461325 1470316481037979450297997)
                  ·
                    refine ⟨551368680389242293861749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470316481037979450297997 551368680389242293861749)
                    ·
                      rfl

theorem cell22_1610680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_1610680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610680 prefixEnd_1610680 := by exact prefixLift 1610680
  have htrace : WordTrace (prefixWord ++ tailWord_1610680) baseStart_1610680 baseEnd_1610680 := by
    simpa [prefixWord, tailWord_1610680, baseEnd_1610680] using wordTrace_append hprefix tailTrace_1610680
  have hstable : (prefixWord ++ tailWord_1610680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610680).length < 2 ^ (prefixWord ++ tailWord_1610680).sum := by decide
  have hdescent : baseEnd_1610680 < baseStart_1610680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610727 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 5]
def baseStart_1610727 : Nat := 118140960795 + 1610727 * 2 ^ 59
def prefixEnd_1610727 : Nat := 4983230072969 + 3 ^ 40 * 1610727 * 2
def baseEnd_1610727 : Nat := 183794923149916612645535

theorem tailTrace_1610727 : CollatzResearch.WordTrace tailWord_1610727 prefixEnd_1610727 183794923149916612645535 := by
  unfold tailWord_1610727
  simp only [CollatzResearch.WordTrace]
  refine ⟨58748040035618644115654435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39165360023745762743769623 58748040035618644115654435)
  ·
    refine ⟨88122060053427966173481653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58748040035618644115654435 88122060053427966173481653)
    ·
      refine ⟨8261443130008871828763905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88122060053427966173481653 8261443130008871828763905)
      ·
        refine ⟨6196082347506653871572929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8261443130008871828763905 6196082347506653871572929)
        ·
          refine ⟨4647061760629990403679697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6196082347506653871572929 4647061760629990403679697)
          ·
            refine ⟨3485296320472492802759773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647061760629990403679697 3485296320472492802759773)
            ·
              refine ⟨1306986120177184801034915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3485296320472492802759773 1306986120177184801034915)
              ·
                refine ⟨1960479180265777201552373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306986120177184801034915 1960479180265777201552373)
                ·
                  refine ⟨183794923149916612645535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1960479180265777201552373 183794923149916612645535)
                  ·
                    rfl

theorem cell22_1610727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 5].length) (baseStart_1610727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610727 prefixEnd_1610727 := by exact prefixLift 1610727
  have htrace : WordTrace (prefixWord ++ tailWord_1610727) baseStart_1610727 baseEnd_1610727 := by
    simpa [prefixWord, tailWord_1610727, baseEnd_1610727] using wordTrace_append hprefix tailTrace_1610727
  have hstable : (prefixWord ++ tailWord_1610727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610727).length < 2 ^ (prefixWord ++ tailWord_1610727).sum := by decide
  have hdescent : baseEnd_1610727 < baseStart_1610727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610783 : List Nat := [1, 1, 2, 4, 1, 3, 1, 9]
def baseStart_1610783 : Nat := 118140960795 + 1610783 * 2 ^ 59
def prefixEnd_1610783 : Nat := 4983230072969 + 3 ^ 40 * 1610783 * 2
def baseEnd_1610783 : Nat := 61267104377131595392937

theorem tailTrace_1610783 : CollatzResearch.WordTrace tailWord_1610783 prefixEnd_1610783 61267104377131595392937 := by
  unfold tailWord_1610783
  simp only [CollatzResearch.WordTrace]
  refine ⟨58750082523415765679693003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39166721682277177119795335 58750082523415765679693003)
  ·
    refine ⟨88125123785123648519539505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58750082523415765679693003 88125123785123648519539505)
    ·
      refine ⟨66093842838842736389654629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88125123785123648519539505 66093842838842736389654629)
      ·
        refine ⟨12392595532283013073060243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66093842838842736389654629 12392595532283013073060243)
        ·
          refine ⟨18588893298424519609590365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12392595532283013073060243 18588893298424519609590365)
          ·
            refine ⟨6970834986909194853596387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18588893298424519609590365 6970834986909194853596387)
            ·
              refine ⟨10456252480363792280394581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970834986909194853596387 10456252480363792280394581)
              ·
                refine ⟨61267104377131595392937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10456252480363792280394581 61267104377131595392937)
                ·
                  rfl

theorem cell22_1610783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 9].length) (baseStart_1610783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610783 prefixEnd_1610783 := by exact prefixLift 1610783
  have htrace : WordTrace (prefixWord ++ tailWord_1610783) baseStart_1610783 baseEnd_1610783 := by
    simpa [prefixWord, tailWord_1610783, baseEnd_1610783] using wordTrace_append hprefix tailTrace_1610783
  have hstable : (prefixWord ++ tailWord_1610783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610783).length < 2 ^ (prefixWord ++ tailWord_1610783).sum := by decide
  have hdescent : baseEnd_1610783 < baseStart_1610783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610787 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 2, 3]
def baseStart_1610787 : Nat := 118140960795 + 1610787 * 2 ^ 59
def prefixEnd_1610787 : Nat := 4983230072969 + 3 ^ 40 * 1610787 * 2
def baseEnd_1610787 : Nat := 551405308675929681436421

theorem tailTrace_1610787 : CollatzResearch.WordTrace tailWord_1610787 prefixEnd_1610787 551405308675929681436421 := by
  unfold tailWord_1610787
  simp only [CollatzResearch.WordTrace]
  refine ⟨58750228415401274362838615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39166818943600849575225743 58750228415401274362838615)
  ·
    refine ⟨88125342623101911544257923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58750228415401274362838615 88125342623101911544257923)
    ·
      refine ⟨132188013934652867316386885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88125342623101911544257923 132188013934652867316386885)
      ·
        refine ⟨24785252612747412621822541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132188013934652867316386885 24785252612747412621822541)
        ·
          refine ⟨9294469729780279733183453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24785252612747412621822541 9294469729780279733183453)
          ·
            refine ⟨3485426148667604899943795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9294469729780279733183453 3485426148667604899943795)
            ·
              refine ⟨5228139223001407349915693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485426148667604899943795 5228139223001407349915693)
              ·
                refine ⟨1960552208625527756218385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5228139223001407349915693 1960552208625527756218385)
                ·
                  refine ⟨1470414156469145817163789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960552208625527756218385 1470414156469145817163789)
                  ·
                    refine ⟨551405308675929681436421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470414156469145817163789 551405308675929681436421)
                    ·
                      rfl

theorem cell22_1610787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3].length) (baseStart_1610787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610787 prefixEnd_1610787 := by exact prefixLift 1610787
  have htrace : WordTrace (prefixWord ++ tailWord_1610787) baseStart_1610787 baseEnd_1610787 := by
    simpa [prefixWord, tailWord_1610787, baseEnd_1610787] using wordTrace_append hprefix tailTrace_1610787
  have hstable : (prefixWord ++ tailWord_1610787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610787).length < 2 ^ (prefixWord ++ tailWord_1610787).sum := by decide
  have hdescent : baseEnd_1610787 < baseStart_1610787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610937 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_1610937 : Nat := 118140960795 + 1610937 * 2 ^ 59
def prefixEnd_1610937 : Nat := 4983230072969 + 3 ^ 40 * 1610937 * 2
def baseEnd_1610937 : Nat := 551456656741379290185961

theorem tailTrace_1610937 : CollatzResearch.WordTrace tailWord_1610937 prefixEnd_1610937 551456656741379290185961 := by
  unfold tailWord_1610937
  simp only [CollatzResearch.WordTrace]
  refine ⟨58755699364857849980799065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39170466243238566653866043 58755699364857849980799065)
  ·
    refine ⟨44066774523643387485599299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58755699364857849980799065 44066774523643387485599299)
    ·
      refine ⟨66100161785465081228398949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44066774523643387485599299 66100161785465081228398949)
      ·
        refine ⟨12393780334774702730324803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66100161785465081228398949 12393780334774702730324803)
        ·
          refine ⟨18590670502162054095487205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12393780334774702730324803 18590670502162054095487205)
          ·
            refine ⟨3485750719155385142903851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18590670502162054095487205 3485750719155385142903851)
            ·
              refine ⟨5228626078733077714355777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485750719155385142903851 5228626078733077714355777)
              ·
                refine ⟨3921469559049808285766833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228626078733077714355777 3921469559049808285766833)
                ·
                  refine ⟨2941102169287356214325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921469559049808285766833 2941102169287356214325125)
                  ·
                    refine ⟨551456656741379290185961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2941102169287356214325125 551456656741379290185961)
                    ·
                      rfl

theorem cell22_1610937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_1610937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610937 prefixEnd_1610937 := by exact prefixLift 1610937
  have htrace : WordTrace (prefixWord ++ tailWord_1610937) baseStart_1610937 baseEnd_1610937 := by
    simpa [prefixWord, tailWord_1610937, baseEnd_1610937] using wordTrace_append hprefix tailTrace_1610937
  have hstable : (prefixWord ++ tailWord_1610937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610937).length < 2 ^ (prefixWord ++ tailWord_1610937).sum := by decide
  have hdescent : baseEnd_1610937 < baseStart_1610937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610967 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 3, 3]
def baseStart_1610967 : Nat := 118140960795 + 1610967 * 2 ^ 59
def prefixEnd_1610967 : Nat := 4983230072969 + 3 ^ 40 * 1610967 * 2
def baseEnd_1610967 : Nat := 551466926354469211935869

theorem tailTrace_1610967 : CollatzResearch.WordTrace tailWord_1610967 prefixEnd_1610967 551466926354469211935869 := by
  unfold tailWord_1610967
  simp only [CollatzResearch.WordTrace]
  refine ⟨58756793554749165104391155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39171195703166110069594103 58756793554749165104391155)
  ·
    refine ⟨88135190332123747656586733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58756793554749165104391155 88135190332123747656586733)
    ·
      refine ⟨33050696374546405371220025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88135190332123747656586733 33050696374546405371220025)
      ·
        refine ⟨24788022280909804028415019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33050696374546405371220025 24788022280909804028415019)
        ·
          refine ⟨37182033421364706042622529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788022280909804028415019 37182033421364706042622529)
          ·
            refine ⟨27886525066023529531966897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37182033421364706042622529 27886525066023529531966897)
            ·
              refine ⟨20914893799517647148975173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27886525066023529531966897 20914893799517647148975173)
              ·
                refine ⟨3921542587409558840432845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20914893799517647148975173 3921542587409558840432845)
                ·
                  refine ⟨1470578470278584565162317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3921542587409558840432845 1470578470278584565162317)
                  ·
                    refine ⟨551466926354469211935869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470578470278584565162317 551466926354469211935869)
                    ·
                      rfl

theorem cell22_1610967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_1610967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610967 prefixEnd_1610967 := by exact prefixLift 1610967
  have htrace : WordTrace (prefixWord ++ tailWord_1610967) baseStart_1610967 baseEnd_1610967 := by
    simpa [prefixWord, tailWord_1610967, baseEnd_1610967] using wordTrace_append hprefix tailTrace_1610967
  have hstable : (prefixWord ++ tailWord_1610967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610967).length < 2 ^ (prefixWord ++ tailWord_1610967).sum := by decide
  have hdescent : baseEnd_1610967 < baseStart_1610967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610980 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1610980 : Nat := 118140960795 + 1610980 * 2 ^ 59
def prefixEnd_1610980 : Nat := 4983230072969 + 3 ^ 40 * 1610980 * 2
def baseEnd_1610980 : Nat := 183823792173380503786943

theorem tailTrace_1610980 : CollatzResearch.WordTrace tailWord_1610980 prefixEnd_1610980 183823792173380503786943 := by
  unfold tailWord_1610980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29378633851851034162307197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39171511802468045549742929 29378633851851034162307197)
  ·
    refine ⟨11016987694444137810865199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29378633851851034162307197 11016987694444137810865199)
    ·
      refine ⟨16525481541666206716297799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11016987694444137810865199 16525481541666206716297799)
      ·
        refine ⟨24788222312499310074446699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16525481541666206716297799 24788222312499310074446699)
        ·
          refine ⟨37182333468748965111670049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788222312499310074446699 37182333468748965111670049)
          ·
            refine ⟨27886750101561723833752537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37182333468748965111670049 27886750101561723833752537)
            ·
              refine ⟨20915062576171292875314403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27886750101561723833752537 20915062576171292875314403)
              ·
                refine ⟨31372593864256939312971605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20915062576171292875314403 31372593864256939312971605)
                ·
                  refine ⟨183823792173380503786943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31372593864256939312971605 183823792173380503786943)
                  ·
                    rfl

theorem cell22_1610980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1610980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1610980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1610980 prefixEnd_1610980 := by exact prefixLift 1610980
  have htrace : WordTrace (prefixWord ++ tailWord_1610980) baseStart_1610980 baseEnd_1610980 := by
    simpa [prefixWord, tailWord_1610980, baseEnd_1610980] using wordTrace_append hprefix tailTrace_1610980
  have hstable : (prefixWord ++ tailWord_1610980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610980).length < 2 ^ (prefixWord ++ tailWord_1610980).sum := by decide
  have hdescent : baseEnd_1610980 < baseStart_1610980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611012 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1611012 : Nat := 118140960795 + 1611012 * 2 ^ 59
def prefixEnd_1611012 : Nat := 4983230072969 + 3 ^ 40 * 1611012 * 2
def baseEnd_1611012 : Nat := 551482330774104094560731

theorem tailTrace_1611012 : CollatzResearch.WordTrace tailWord_1611012 prefixEnd_1611012 551482330774104094560731 := by
  unfold tailWord_1611012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29379217419793068894889645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39172289893057425193186193 29379217419793068894889645)
  ·
    refine ⟨11017206532422400835583617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29379217419793068894889645 11017206532422400835583617)
    ·
      refine ⟨8262904899316800626687713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11017206532422400835583617 8262904899316800626687713)
      ·
        refine ⟨6197178674487600470015785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262904899316800626687713 6197178674487600470015785)
        ·
          refine ⟨4647884005865700352511839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6197178674487600470015785 4647884005865700352511839)
          ·
            refine ⟨6971826008798550528767759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647884005865700352511839 6971826008798550528767759)
            ·
              refine ⟨10457739013197825793151639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971826008798550528767759 10457739013197825793151639)
              ·
                refine ⟨15686608519796738689727459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10457739013197825793151639 15686608519796738689727459)
                ·
                  refine ⟨23529912779695108034591189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15686608519796738689727459 23529912779695108034591189)
                  ·
                    refine ⟨551482330774104094560731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23529912779695108034591189 551482330774104094560731)
                    ·
                      rfl

theorem cell22_1611012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1611012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611012 prefixEnd_1611012 := by exact prefixLift 1611012
  have htrace : WordTrace (prefixWord ++ tailWord_1611012) baseStart_1611012 baseEnd_1611012 := by
    simpa [prefixWord, tailWord_1611012, baseEnd_1611012] using wordTrace_append hprefix tailTrace_1611012
  have hstable : (prefixWord ++ tailWord_1611012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611012).length < 2 ^ (prefixWord ++ tailWord_1611012).sum := by decide
  have hdescent : baseEnd_1611012 < baseStart_1611012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611044 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1611044 : Nat := 118140960795 + 1611044 * 2 ^ 59
def prefixEnd_1611044 : Nat := 4983230072969 + 3 ^ 40 * 1611044 * 2
def baseEnd_1611044 : Nat := 551493285028066677760633

theorem tailTrace_1611044 : CollatzResearch.WordTrace tailWord_1611044 prefixEnd_1611044 551493285028066677760633 := by
  unfold tailWord_1611044
  simp only [CollatzResearch.WordTrace]
  refine ⟨29379800987735103627472093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39173067983646804836629457 29379800987735103627472093)
  ·
    refine ⟨11017425370400663860302035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29379800987735103627472093 11017425370400663860302035)
    ·
      refine ⟨16526138055600995790453053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11017425370400663860302035 16526138055600995790453053)
      ·
        refine ⟨6197301770850373421419895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16526138055600995790453053 6197301770850373421419895)
        ·
          refine ⟨9295952656275560132129843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197301770850373421419895 9295952656275560132129843)
          ·
            refine ⟨13943928984413340198194765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295952656275560132129843 13943928984413340198194765)
            ·
              refine ⟨5228973369155002574323037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13943928984413340198194765 5228973369155002574323037)
              ·
                refine ⟨1960865013433125965371139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5228973369155002574323037 1960865013433125965371139)
                ·
                  refine ⟨2941297520149688948056709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960865013433125965371139 2941297520149688948056709)
                  ·
                    refine ⟨551493285028066677760633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2941297520149688948056709 551493285028066677760633)
                    ·
                      rfl

theorem cell22_1611044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1611044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611044 prefixEnd_1611044 := by exact prefixLift 1611044
  have htrace : WordTrace (prefixWord ++ tailWord_1611044) baseStart_1611044 baseEnd_1611044 := by
    simpa [prefixWord, tailWord_1611044, baseEnd_1611044] using wordTrace_append hprefix tailTrace_1611044
  have hstable : (prefixWord ++ tailWord_1611044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611044).length < 2 ^ (prefixWord ++ tailWord_1611044).sum := by decide
  have hdescent : baseEnd_1611044 < baseStart_1611044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611059 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 4]
def baseStart_1611059 : Nat := 118140960795 + 1611059 * 2 ^ 59
def prefixEnd_1611059 : Nat := 4983230072969 + 3 ^ 40 * 1611059 * 2
def baseEnd_1611059 : Nat := 183832806611537212878529

theorem tailTrace_1611059 : CollatzResearch.WordTrace tailWord_1611059 prefixEnd_1611059 183832806611537212878529 := by
  unfold tailWord_1611059
  simp only [CollatzResearch.WordTrace]
  refine ⟨58760149070415864816740231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39173432713610576544493487 58760149070415864816740231)
  ·
    refine ⟨88140223605623797225110347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58760149070415864816740231 88140223605623797225110347)
    ·
      refine ⟨132210335408435695837665521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88140223605623797225110347 132210335408435695837665521)
      ·
        refine ⟨99157751556326771878249141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132210335408435695837665521 99157751556326771878249141)
        ·
          refine ⟨9296039208405634863585857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99157751556326771878249141 9296039208405634863585857)
          ·
            refine ⟨6972029406304226147689393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296039208405634863585857 6972029406304226147689393)
            ·
              refine ⟨5229022054728169610767045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6972029406304226147689393 5229022054728169610767045)
              ·
                refine ⟨980441635261531802018821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5229022054728169610767045 980441635261531802018821)
                ·
                  refine ⟨183832806611537212878529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980441635261531802018821 183832806611537212878529)
                  ·
                    rfl

theorem cell22_1611059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 4].length) (baseStart_1611059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611059 prefixEnd_1611059 := by exact prefixLift 1611059
  have htrace : WordTrace (prefixWord ++ tailWord_1611059) baseStart_1611059 baseEnd_1611059 := by
    simpa [prefixWord, tailWord_1611059, baseEnd_1611059] using wordTrace_append hprefix tailTrace_1611059
  have hstable : (prefixWord ++ tailWord_1611059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611059).length < 2 ^ (prefixWord ++ tailWord_1611059).sum := by decide
  have hdescent : baseEnd_1611059 < baseStart_1611059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611125 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1611125 : Nat := 118140960795 + 1611125 * 2 ^ 59
def prefixEnd_1611125 : Nat := 4983230072969 + 3 ^ 40 * 1611125 * 2
def baseEnd_1611125 : Nat := 551521012983409466485385

theorem tailTrace_1611125 : CollatzResearch.WordTrace tailWord_1611125 prefixEnd_1611125 551521012983409466485385 := by
  unfold tailWord_1611125
  simp only [CollatzResearch.WordTrace]
  refine ⟨58762556288176758088642829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39175037525451172059095219 58762556288176758088642829)
  ·
    refine ⟨22035958608066284283241061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58762556288176758088642829 22035958608066284283241061)
    ·
      refine ⟨4131742239012428303107699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22035958608066284283241061 4131742239012428303107699)
      ·
        refine ⟨6197613358518642454661549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4131742239012428303107699 6197613358518642454661549)
        ·
          refine ⟨2324105009444490920498081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6197613358518642454661549 2324105009444490920498081)
          ·
            refine ⟨1743078757083368190373561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324105009444490920498081 1743078757083368190373561)
            ·
              refine ⟨1307309067812526142780171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743078757083368190373561 1307309067812526142780171)
              ·
                refine ⟨1960963601718789214170257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307309067812526142780171 1960963601718789214170257)
                ·
                  refine ⟨1470722701289091910627693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960963601718789214170257 1470722701289091910627693)
                  ·
                    refine ⟨551521012983409466485385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470722701289091910627693 551521012983409466485385)
                    ·
                      rfl

theorem cell22_1611125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1611125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611125 prefixEnd_1611125 := by exact prefixLift 1611125
  have htrace : WordTrace (prefixWord ++ tailWord_1611125) baseStart_1611125 baseEnd_1611125 := by
    simpa [prefixWord, tailWord_1611125, baseEnd_1611125] using wordTrace_append hprefix tailTrace_1611125
  have hstable : (prefixWord ++ tailWord_1611125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611125).length < 2 ^ (prefixWord ++ tailWord_1611125).sum := by decide
  have hdescent : baseEnd_1611125 < baseStart_1611125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611170 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1611170 : Nat := 118140960795 + 1611170 * 2 ^ 59
def prefixEnd_1611170 : Nat := 4983230072969 + 3 ^ 40 * 1611170 * 2
def baseEnd_1611170 : Nat := 551536417403044349110247

theorem tailTrace_1611170 : CollatzResearch.WordTrace tailWord_1611170 prefixEnd_1611170 551536417403044349110247 := by
  unfold tailWord_1611170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691049393253432693507741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39176131715342487182687309 14691049393253432693507741)
  ·
    refine ⟨5509143522470037260065403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14691049393253432693507741 5509143522470037260065403)
    ·
      refine ⟨8263715283705055890098105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509143522470037260065403 8263715283705055890098105)
      ·
        refine ⟨6197786462778791917573579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8263715283705055890098105 6197786462778791917573579)
        ·
          refine ⟨9296679694168187876360369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197786462778791917573579 9296679694168187876360369)
          ·
            refine ⟨6972509770626140907270277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296679694168187876360369 6972509770626140907270277)
            ·
              refine ⟨1307345581992401420113177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6972509770626140907270277 1307345581992401420113177)
              ·
                refine ⟨980509186494301065084883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307345581992401420113177 980509186494301065084883)
                ·
                  refine ⟨1470763779741451597627325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980509186494301065084883 1470763779741451597627325)
                  ·
                    refine ⟨551536417403044349110247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470763779741451597627325 551536417403044349110247)
                    ·
                      rfl

theorem cell22_1611170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1611170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611170 prefixEnd_1611170 := by exact prefixLift 1611170
  have htrace : WordTrace (prefixWord ++ tailWord_1611170) baseStart_1611170 baseEnd_1611170 := by
    simpa [prefixWord, tailWord_1611170, baseEnd_1611170] using wordTrace_append hprefix tailTrace_1611170
  have hstable : (prefixWord ++ tailWord_1611170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611170).length < 2 ^ (prefixWord ++ tailWord_1611170).sum := by decide
  have hdescent : baseEnd_1611170 < baseStart_1611170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611181 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1611181 : Nat := 118140960795 + 1611181 * 2 ^ 59
def prefixEnd_1611181 : Nat := 4983230072969 + 3 ^ 40 * 1611181 * 2
def baseEnd_1611181 : Nat := 551540182927843987085213

theorem tailTrace_1611181 : CollatzResearch.WordTrace tailWord_1611181 prefixEnd_1611181 551540182927843987085213 := by
  unfold tailWord_1611181
  simp only [CollatzResearch.WordTrace]
  refine ⟨58764598775973879652681397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39176399183982586435120931 58764598775973879652681397)
  ·
    refine ⟨5509181135247551217438881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58764598775973879652681397 5509181135247551217438881)
    ·
      refine ⟨4131885851435663413079161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509181135247551217438881 4131885851435663413079161)
      ·
        refine ⟨3098914388576747559809371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131885851435663413079161 3098914388576747559809371)
        ·
          refine ⟨4648371582865121339714057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098914388576747559809371 4648371582865121339714057)
          ·
            refine ⟨3486278687148841004785543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4648371582865121339714057 3486278687148841004785543)
            ·
              refine ⟨5229418030723261507178315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486278687148841004785543 5229418030723261507178315)
              ·
                refine ⟨7844127046084892260767473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229418030723261507178315 7844127046084892260767473)
                ·
                  refine ⟨5883095284563669195575605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7844127046084892260767473 5883095284563669195575605)
                  ·
                    refine ⟨551540182927843987085213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5883095284563669195575605 551540182927843987085213)
                    ·
                      rfl

theorem cell22_1611181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1611181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611181 prefixEnd_1611181 := by exact prefixLift 1611181
  have htrace : WordTrace (prefixWord ++ tailWord_1611181) baseStart_1611181 baseEnd_1611181 := by
    simpa [prefixWord, tailWord_1611181, baseEnd_1611181] using wordTrace_append hprefix tailTrace_1611181
  have hstable : (prefixWord ++ tailWord_1611181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611181).length < 2 ^ (prefixWord ++ tailWord_1611181).sum := by decide
  have hdescent : baseEnd_1611181 < baseStart_1611181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611209 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_1611209 : Nat := 118140960795 + 1611209 * 2 ^ 59
def prefixEnd_1611209 : Nat := 4983230072969 + 3 ^ 40 * 1611209 * 2
def baseEnd_1611209 : Nat := 551549767900061247385127

theorem tailTrace_1611209 : CollatzResearch.WordTrace tailWord_1611209 prefixEnd_1611209 551549767900061247385127 := by
  unfold tailWord_1611209
  simp only [CollatzResearch.WordTrace]
  refine ⟨58765620019872440434700681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39177080013248293623133787 58765620019872440434700681)
  ·
    refine ⟨44074215014904330326025511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58765620019872440434700681 44074215014904330326025511)
    ·
      refine ⟨66111322522356495489038267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44074215014904330326025511 66111322522356495489038267)
      ·
        refine ⟨99166983783534743233557401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66111322522356495489038267 99166983783534743233557401)
        ·
          refine ⟨74375237837651057425168051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99166983783534743233557401 74375237837651057425168051)
          ·
            refine ⟨111562856756476586137752077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74375237837651057425168051 111562856756476586137752077)
            ·
              refine ⟨41836071283678719801657029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111562856756476586137752077 41836071283678719801657029)
              ·
                refine ⟨7844263365689759962810693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41836071283678719801657029 7844263365689759962810693)
                ·
                  refine ⟨1470799381066829993027005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7844263365689759962810693 1470799381066829993027005)
                  ·
                    refine ⟨551549767900061247385127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470799381066829993027005 551549767900061247385127)
                    ·
                      rfl

theorem cell22_1611209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_1611209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611209 prefixEnd_1611209 := by exact prefixLift 1611209
  have htrace : WordTrace (prefixWord ++ tailWord_1611209) baseStart_1611209 baseEnd_1611209 := by
    simpa [prefixWord, tailWord_1611209, baseEnd_1611209] using wordTrace_append hprefix tailTrace_1611209
  have hstable : (prefixWord ++ tailWord_1611209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611209).length < 2 ^ (prefixWord ++ tailWord_1611209).sum := by decide
  have hdescent : baseEnd_1611209 < baseStart_1611209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611224 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_1611224 : Nat := 118140960795 + 1611224 * 2 ^ 59
def prefixEnd_1611224 : Nat := 4983230072969 + 3 ^ 40 * 1611224 * 2
def baseEnd_1611224 : Nat := 551554902706606208260081

theorem tailTrace_1611224 : CollatzResearch.WordTrace tailWord_1611224 prefixEnd_1611224 551554902706606208260081 := by
  unfold tailWord_1611224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29383083557409048998248363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39177444743212065330997817 29383083557409048998248363)
  ·
    refine ⟨44074625336113573497372545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29383083557409048998248363 44074625336113573497372545)
    ·
      refine ⟨33055969002085180123029409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44074625336113573497372545 33055969002085180123029409)
      ·
        refine ⟨24791976751563885092272057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33055969002085180123029409 24791976751563885092272057)
        ·
          refine ⟨18593982563672913819204043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24791976751563885092272057 18593982563672913819204043)
          ·
            refine ⟨27890973845509370728806065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18593982563672913819204043 27890973845509370728806065)
            ·
              refine ⟨20918230384132028046604549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27890973845509370728806065 20918230384132028046604549)
              ·
                refine ⟨3922168197024755258738353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20918230384132028046604549 3922168197024755258738353)
                ·
                  refine ⟨2941626147768566444053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3922168197024755258738353 2941626147768566444053765)
                  ·
                    refine ⟨551554902706606208260081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2941626147768566444053765 551554902706606208260081)
                    ·
                      rfl

theorem cell22_1611224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_1611224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611224 prefixEnd_1611224 := by exact prefixLift 1611224
  have htrace : WordTrace (prefixWord ++ tailWord_1611224) baseStart_1611224 baseEnd_1611224 := by
    simpa [prefixWord, tailWord_1611224, baseEnd_1611224] using wordTrace_append hprefix tailTrace_1611224
  have hstable : (prefixWord ++ tailWord_1611224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611224).length < 2 ^ (prefixWord ++ tailWord_1611224).sum := by decide
  have hdescent : baseEnd_1611224 < baseStart_1611224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611226 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_1611226 : Nat := 118140960795 + 1611226 * 2 ^ 59
def prefixEnd_1611226 : Nat := 4983230072969 + 3 ^ 40 * 1611226 * 2
def baseEnd_1611226 : Nat := 551555587347478869710075

theorem tailTrace_1611226 : CollatzResearch.WordTrace tailWord_1611226 prefixEnd_1611226 551555587347478869710075 := by
  unfold tailWord_1611226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691560015202713084517383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39177493373873901558713021 14691560015202713084517383)
  ·
    refine ⟨22037340022804069626776075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14691560015202713084517383 22037340022804069626776075)
    ·
      refine ⟨33056010034206104440164113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22037340022804069626776075 33056010034206104440164113)
      ·
        refine ⟨24792007525654578330123085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33056010034206104440164113 24792007525654578330123085)
        ·
          refine ⟨9297002822120466873796157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24792007525654578330123085 9297002822120466873796157)
          ·
            refine ⟨3486376058295175077673559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9297002822120466873796157 3486376058295175077673559)
            ·
              refine ⟨5229564087442762616510339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486376058295175077673559 5229564087442762616510339)
              ·
                refine ⟨7844346131164143924765509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229564087442762616510339 7844346131164143924765509)
                ·
                  refine ⟨1470814899593276985893533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7844346131164143924765509 1470814899593276985893533)
                  ·
                    refine ⟨551555587347478869710075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470814899593276985893533 551555587347478869710075)
                    ·
                      rfl

theorem cell22_1611226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_1611226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611226 prefixEnd_1611226 := by exact prefixLift 1611226
  have htrace : WordTrace (prefixWord ++ tailWord_1611226) baseStart_1611226 baseEnd_1611226 := by
    simpa [prefixWord, tailWord_1611226, baseEnd_1611226] using wordTrace_append hprefix tailTrace_1611226
  have hstable : (prefixWord ++ tailWord_1611226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611226).length < 2 ^ (prefixWord ++ tailWord_1611226).sum := by decide
  have hdescent : baseEnd_1611226 < baseStart_1611226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611256 : List Nat := [2, 1, 2, 1, 1, 7, 2, 6]
def baseStart_1611256 : Nat := 118140960795 + 1611256 * 2 ^ 59
def prefixEnd_1611256 : Nat := 4983230072969 + 3 ^ 40 * 1611256 * 2
def baseEnd_1611256 : Nat := 61285095217840976828887

theorem tailTrace_1611256 : CollatzResearch.WordTrace tailWord_1611256 prefixEnd_1611256 61285095217840976828887 := by
  unfold tailWord_1611256
  simp only [CollatzResearch.WordTrace]
  refine ⟨29383667125351083730830811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39178222833801444974441081 29383667125351083730830811)
  ·
    refine ⟨44075500688026625596246217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29383667125351083730830811 44075500688026625596246217)
    ·
      refine ⟨33056625516019969197184663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44075500688026625596246217 33056625516019969197184663)
      ·
        refine ⟨49584938274029953795776995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33056625516019969197184663 49584938274029953795776995)
        ·
          refine ⟨74377407411044930693665493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49584938274029953795776995 74377407411044930693665493)
          ·
            refine ⟨1743220486196365563132785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74377407411044930693665493 1743220486196365563132785)
            ·
              refine ⟨1307415364647274172349589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743220486196365563132785 1307415364647274172349589)
              ·
                refine ⟨61285095217840976828887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1307415364647274172349589 61285095217840976828887)
                ·
                  rfl

theorem cell22_1611256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_1611256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611256 prefixEnd_1611256 := by exact prefixLift 1611256
  have htrace : WordTrace (prefixWord ++ tailWord_1611256) baseStart_1611256 baseEnd_1611256 := by
    simpa [prefixWord, tailWord_1611256, baseEnd_1611256] using wordTrace_append hprefix tailTrace_1611256
  have hstable : (prefixWord ++ tailWord_1611256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611256).length < 2 ^ (prefixWord ++ tailWord_1611256).sum := by decide
  have hdescent : baseEnd_1611256 < baseStart_1611256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611262 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1611262 : Nat := 118140960795 + 1611262 * 2 ^ 59
def prefixEnd_1611262 : Nat := 4983230072969 + 3 ^ 40 * 1611262 * 2
def baseEnd_1611262 : Nat := 183855970294395591936655

theorem tailTrace_1611262 : CollatzResearch.WordTrace tailWord_1611262 prefixEnd_1611262 183855970294395591936655 := by
  unfold tailWord_1611262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7345944136085053810797505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39178368725786953657586693 7345944136085053810797505)
  ·
    refine ⟨5509458102063790358098129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7345944136085053810797505 5509458102063790358098129)
    ·
      refine ⟨4132093576547842768573597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509458102063790358098129 4132093576547842768573597)
      ·
        refine ⟨1549535091205441038215099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4132093576547842768573597 1549535091205441038215099)
        ·
          refine ⟨2324302636808161557322649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549535091205441038215099 2324302636808161557322649)
          ·
            refine ⟨1743226977606121167991987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324302636808161557322649 1743226977606121167991987)
            ·
              refine ⟨2614840466409181751987981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743226977606121167991987 2614840466409181751987981)
              ·
                refine ⟨980565174903443156995493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614840466409181751987981 980565174903443156995493)
                ·
                  refine ⟨183855970294395591936655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980565174903443156995493 183855970294395591936655)
                  ·
                    rfl

theorem cell22_1611262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1611262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611262 prefixEnd_1611262 := by exact prefixLift 1611262
  have htrace : WordTrace (prefixWord ++ tailWord_1611262) baseStart_1611262 baseEnd_1611262 := by
    simpa [prefixWord, tailWord_1611262, baseEnd_1611262] using wordTrace_append hprefix tailTrace_1611262
  have hstable : (prefixWord ++ tailWord_1611262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611262).length < 2 ^ (prefixWord ++ tailWord_1611262).sum := by decide
  have hdescent : baseEnd_1611262 < baseStart_1611262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611294 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1611294 : Nat := 118140960795 + 1611294 * 2 ^ 59
def prefixEnd_1611294 : Nat := 4983230072969 + 3 ^ 40 * 1611294 * 2
def baseEnd_1611294 : Nat := 551578865137149359009867

theorem tailTrace_1611294 : CollatzResearch.WordTrace tailWord_1611294 prefixEnd_1611294 551578865137149359009867 := by
  unfold tailWord_1611294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346090028070562493943117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39179146816376333301029957 7346090028070562493943117)
  ·
    refine ⟨2754783760526460935228669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7346090028070562493943117 2754783760526460935228669)
    ·
      refine ⟨1033043910197422850710751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2754783760526460935228669 1033043910197422850710751)
      ·
        refine ⟨1549565865296134276066127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033043910197422850710751 1549565865296134276066127)
        ·
          refine ⟨2324348797944201414099191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549565865296134276066127 2324348797944201414099191)
          ·
            refine ⟨3486523196916302121148787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324348797944201414099191 3486523196916302121148787)
            ·
              refine ⟨5229784795374453181723181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486523196916302121148787 5229784795374453181723181)
              ·
                refine ⟨1961169298265419943146193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5229784795374453181723181 1961169298265419943146193)
                ·
                  refine ⟨1470876973699064957359645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961169298265419943146193 1470876973699064957359645)
                  ·
                    refine ⟨551578865137149359009867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470876973699064957359645 551578865137149359009867)
                    ·
                      rfl

theorem cell22_1611294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1611294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611294 prefixEnd_1611294 := by exact prefixLift 1611294
  have htrace : WordTrace (prefixWord ++ tailWord_1611294) baseStart_1611294 baseEnd_1611294 := by
    simpa [prefixWord, tailWord_1611294, baseEnd_1611294] using wordTrace_append hprefix tailTrace_1611294
  have hstable : (prefixWord ++ tailWord_1611294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611294).length < 2 ^ (prefixWord ++ tailWord_1611294).sum := by decide
  have hdescent : baseEnd_1611294 < baseStart_1611294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611344 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_1611344 : Nat := 118140960795 + 1611344 * 2 ^ 59
def prefixEnd_1611344 : Nat := 4983230072969 + 3 ^ 40 * 1611344 * 2
def baseEnd_1611344 : Nat := 551595981158965895259713

theorem tailTrace_1611344 : CollatzResearch.WordTrace tailWord_1611344 prefixEnd_1611344 551595981158965895259713 := by
  unfold tailWord_1611344
  simp only [CollatzResearch.WordTrace]
  refine ⟨29385271937191679245432543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39180362582922238993910057 29385271937191679245432543)
  ·
    refine ⟨44077907905787518868148815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29385271937191679245432543 44077907905787518868148815)
    ·
      refine ⟨66116861858681278302223223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44077907905787518868148815 66116861858681278302223223)
      ·
        refine ⟨99175292788021917453334835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66116861858681278302223223 99175292788021917453334835)
        ·
          refine ⟨148762939182032876180002253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99175292788021917453334835 148762939182032876180002253)
          ·
            refine ⟨55786102193262328567500845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148762939182032876180002253 55786102193262328567500845)
            ·
              refine ⟨20919788322473373212812817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55786102193262328567500845 20919788322473373212812817)
              ·
                refine ⟨15689841241855029909609613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20919788322473373212812817 15689841241855029909609613)
                ·
                  refine ⟨5883690465695636216103605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689841241855029909609613 5883690465695636216103605)
                  ·
                    refine ⟨551595981158965895259713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5883690465695636216103605 551595981158965895259713)
                    ·
                      rfl

theorem cell22_1611344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_1611344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611344 prefixEnd_1611344 := by exact prefixLift 1611344
  have htrace : WordTrace (prefixWord ++ tailWord_1611344) baseStart_1611344 baseEnd_1611344 := by
    simpa [prefixWord, tailWord_1611344, baseEnd_1611344] using wordTrace_append hprefix tailTrace_1611344
  have hstable : (prefixWord ++ tailWord_1611344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611344).length < 2 ^ (prefixWord ++ tailWord_1611344).sum := by decide
  have hdescent : baseEnd_1611344 < baseStart_1611344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611361 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1611361 : Nat := 118140960795 + 1611361 * 2 ^ 59
def prefixEnd_1611361 : Nat := 4983230072969 + 3 ^ 40 * 1611361 * 2
def baseEnd_1611361 : Nat := 551601800606383517584661

theorem tailTrace_1611361 : CollatzResearch.WordTrace tailWord_1611361 prefixEnd_1611361 551601800606383517584661 := by
  unfold tailWord_1611361
  simp only [CollatzResearch.WordTrace]
  refine ⟨58771163915321770394233937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39180775943547846929489291 58771163915321770394233937)
  ·
    refine ⟨44078372936491327795675453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58771163915321770394233937 44078372936491327795675453)
    ·
      refine ⟨16529389851184247923378295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44078372936491327795675453 16529389851184247923378295)
      ·
        refine ⟨24794084776776371885067443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16529389851184247923378295 24794084776776371885067443)
        ·
          refine ⟨37191127165164557827601165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24794084776776371885067443 37191127165164557827601165)
          ·
            refine ⟨13946672686936709185350437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37191127165164557827601165 13946672686936709185350437)
            ·
              refine ⟨2615001128800632972253207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13946672686936709185350437 2615001128800632972253207)
              ·
                refine ⟨3922501693200949458379811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615001128800632972253207 3922501693200949458379811)
                ·
                  refine ⟨5883752539801424187569717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922501693200949458379811 5883752539801424187569717)
                  ·
                    refine ⟨551601800606383517584661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5883752539801424187569717 551601800606383517584661)
                    ·
                      rfl

theorem cell22_1611361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1611361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611361 prefixEnd_1611361 := by exact prefixLift 1611361
  have htrace : WordTrace (prefixWord ++ tailWord_1611361) baseStart_1611361 baseEnd_1611361 := by
    simpa [prefixWord, tailWord_1611361, baseEnd_1611361] using wordTrace_append hprefix tailTrace_1611361
  have hstable : (prefixWord ++ tailWord_1611361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611361).length < 2 ^ (prefixWord ++ tailWord_1611361).sum := by decide
  have hdescent : baseEnd_1611361 < baseStart_1611361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611376 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_1611376 : Nat := 118140960795 + 1611376 * 2 ^ 59
def prefixEnd_1611376 : Nat := 4983230072969 + 3 ^ 40 * 1611376 * 2
def baseEnd_1611376 : Nat := 551606935412928478459615

theorem tailTrace_1611376 : CollatzResearch.WordTrace tailWord_1611376 prefixEnd_1611376 551606935412928478459615 := by
  unfold tailWord_1611376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29385855505133713978014991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39181140673511618637353321 29385855505133713978014991)
  ·
    refine ⟨44078783257700570967022487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29385855505133713978014991 44078783257700570967022487)
    ·
      refine ⟨66118174886550856450533731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44078783257700570967022487 66118174886550856450533731)
      ·
        refine ⟨99177262329826284675800597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66118174886550856450533731 99177262329826284675800597)
        ·
          refine ⟨4648934171710607094178153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99177262329826284675800597 4648934171710607094178153)
          ·
            refine ⟨3486700628782955320633615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4648934171710607094178153 3486700628782955320633615)
            ·
              refine ⟨5230050943174432980950423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486700628782955320633615 5230050943174432980950423)
              ·
                refine ⟨7845076414761649471425635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230050943174432980950423 7845076414761649471425635)
                ·
                  refine ⟨11767614622142474207138453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7845076414761649471425635 11767614622142474207138453)
                  ·
                    refine ⟨551606935412928478459615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11767614622142474207138453 551606935412928478459615)
                    ·
                      rfl

theorem cell22_1611376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_1611376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611376 prefixEnd_1611376 := by exact prefixLift 1611376
  have htrace : WordTrace (prefixWord ++ tailWord_1611376) baseStart_1611376 baseEnd_1611376 := by
    simpa [prefixWord, tailWord_1611376, baseEnd_1611376] using wordTrace_append hprefix tailTrace_1611376
  have hstable : (prefixWord ++ tailWord_1611376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611376).length < 2 ^ (prefixWord ++ tailWord_1611376).sum := by decide
  have hdescent : baseEnd_1611376 < baseStart_1611376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611382 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1611382 : Nat := 118140960795 + 1611382 * 2 ^ 59
def prefixEnd_1611382 : Nat := 4983230072969 + 3 ^ 40 * 1611382 * 2
def baseEnd_1611382 : Nat := 551608989335546462809597

theorem tailTrace_1611382 : CollatzResearch.WordTrace tailWord_1611382 prefixEnd_1611382 551608989335546462809597 := by
  unfold tailWord_1611382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673245615515355686296775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39181286565497127320498933 3673245615515355686296775)
  ·
    refine ⟨5509868423273033529445163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673245615515355686296775 5509868423273033529445163)
    ·
      refine ⟨8264802634909550294167745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509868423273033529445163 8264802634909550294167745)
      ·
        refine ⟨6198601976182162720625809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264802634909550294167745 6198601976182162720625809)
        ·
          refine ⟨4648951482136622040469357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198601976182162720625809 4648951482136622040469357)
          ·
            refine ⟨1743356805801233265176009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4648951482136622040469357 1743356805801233265176009)
            ·
              refine ⟨1307517604350924948882007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743356805801233265176009 1307517604350924948882007)
              ·
                refine ⟨1961276406526387423323011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307517604350924948882007 1961276406526387423323011)
                ·
                  refine ⟨2941914609789581134984517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961276406526387423323011 2941914609789581134984517)
                  ·
                    refine ⟨551608989335546462809597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2941914609789581134984517 551608989335546462809597)
                    ·
                      rfl

theorem cell22_1611382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1611382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611382 prefixEnd_1611382 := by exact prefixLift 1611382
  have htrace : WordTrace (prefixWord ++ tailWord_1611382) baseStart_1611382 baseEnd_1611382 := by
    simpa [prefixWord, tailWord_1611382, baseEnd_1611382] using wordTrace_append hprefix tailTrace_1611382
  have hstable : (prefixWord ++ tailWord_1611382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611382).length < 2 ^ (prefixWord ++ tailWord_1611382).sum := by decide
  have hdescent : baseEnd_1611382 < baseStart_1611382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611412 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1611412 : Nat := 118140960795 + 1611412 * 2 ^ 59
def prefixEnd_1611412 : Nat := 4983230072969 + 3 ^ 40 * 1611412 * 2
def baseEnd_1611412 : Nat := 551619258948636384559505

theorem tailTrace_1611412 : CollatzResearch.WordTrace tailWord_1611412 prefixEnd_1611412 551619258948636384559505 := by
  unfold tailWord_1611412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386512019068503052170245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39182016025424670736226993 29386512019068503052170245)
  ·
    refine ⟨5509971003575344322281921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29386512019068503052170245 5509971003575344322281921)
    ·
      refine ⟨4132478252681508241711441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509971003575344322281921 4132478252681508241711441)
      ·
        refine ⟨3099358689511131181283581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4132478252681508241711441 3099358689511131181283581)
        ·
          refine ⟨1162259508566674192981343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3099358689511131181283581 1162259508566674192981343)
          ·
            refine ⟨1743389262850011289472015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162259508566674192981343 1743389262850011289472015)
            ·
              refine ⟨2615083894275016934208023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743389262850011289472015 2615083894275016934208023)
              ·
                refine ⟨3922625841412525401312035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615083894275016934208023 3922625841412525401312035)
                ·
                  refine ⟨5883938762118788101968053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922625841412525401312035 5883938762118788101968053)
                  ·
                    refine ⟨551619258948636384559505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5883938762118788101968053 551619258948636384559505)
                    ·
                      rfl

theorem cell22_1611412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1611412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611412 prefixEnd_1611412 := by exact prefixLift 1611412
  have htrace : WordTrace (prefixWord ++ tailWord_1611412) baseStart_1611412 baseEnd_1611412 := by
    simpa [prefixWord, tailWord_1611412, baseEnd_1611412] using wordTrace_append hprefix tailTrace_1611412
  have hstable : (prefixWord ++ tailWord_1611412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611412).length < 2 ^ (prefixWord ++ tailWord_1611412).sum := by decide
  have hdescent : baseEnd_1611412 < baseStart_1611412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611440 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 1, 3]
def baseStart_1611440 : Nat := 118140960795 + 1611440 * 2 ^ 59
def prefixEnd_1611440 : Nat := 4983230072969 + 3 ^ 40 * 1611440 * 2
def baseEnd_1611440 : Nat := 551628843920853644859419

theorem tailTrace_1611440 : CollatzResearch.WordTrace tailWord_1611440 prefixEnd_1611440 551628843920853644859419 := by
  unfold tailWord_1611440
  simp only [CollatzResearch.WordTrace]
  refine ⟨29387022641017783443179887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39182696854690377924239849 29387022641017783443179887)
  ·
    refine ⟨44080533961526675164769831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29387022641017783443179887 44080533961526675164769831)
    ·
      refine ⟨66120800942290012747154747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44080533961526675164769831 66120800942290012747154747)
      ·
        refine ⟨99181201413435019120732121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66120800942290012747154747 99181201413435019120732121)
        ·
          refine ⟨74385901060076264340549091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99181201413435019120732121 74385901060076264340549091)
          ·
            refine ⟨111578851590114396510823637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74385901060076264340549091 111578851590114396510823637)
            ·
              refine ⟨2615129334143306168222429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111578851590114396510823637 2615129334143306168222429)
              ·
                refine ⟨980673500303739813083411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615129334143306168222429 980673500303739813083411)
                ·
                  refine ⟨1471010250455609719625117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980673500303739813083411 1471010250455609719625117)
                  ·
                    refine ⟨551628843920853644859419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471010250455609719625117 551628843920853644859419)
                    ·
                      rfl

theorem cell22_1611440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_1611440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611440 prefixEnd_1611440 := by exact prefixLift 1611440
  have htrace : WordTrace (prefixWord ++ tailWord_1611440) baseStart_1611440 baseEnd_1611440 := by
    simpa [prefixWord, tailWord_1611440, baseEnd_1611440] using wordTrace_append hprefix tailTrace_1611440
  have hstable : (prefixWord ++ tailWord_1611440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611440).length < 2 ^ (prefixWord ++ tailWord_1611440).sum := by decide
  have hdescent : baseEnd_1611440 < baseStart_1611440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611508 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1611508 : Nat := 118140960795 + 1611508 * 2 ^ 59
def prefixEnd_1611508 : Nat := 4983230072969 + 3 ^ 40 * 1611508 * 2
def baseEnd_1611508 : Nat := 551652121710524134159211

theorem tailTrace_1611508 : CollatzResearch.WordTrace tailWord_1611508 prefixEnd_1611508 551652121710524134159211 := by
  unfold tailWord_1611508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29388262722894607249917589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39184350297192809666556785 29388262722894607249917589)
  ·
    refine ⟨1377574815135684714839887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29388262722894607249917589 1377574815135684714839887)
    ·
      refine ⟨2066362222703527072259831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377574815135684714839887 2066362222703527072259831)
      ·
        refine ⟨3099543334055290608389747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066362222703527072259831 3099543334055290608389747)
        ·
          refine ⟨4649315001082935912584621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099543334055290608389747 4649315001082935912584621)
          ·
            refine ⟨1743493125406100967219233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4649315001082935912584621 1743493125406100967219233)
            ·
              refine ⟨1307619844054575725414425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743493125406100967219233 1307619844054575725414425)
              ·
                refine ⟨980714883040931794060819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307619844054575725414425 980714883040931794060819)
                ·
                  refine ⟨1471072324561397691091229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980714883040931794060819 1471072324561397691091229)
                  ·
                    refine ⟨551652121710524134159211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471072324561397691091229 551652121710524134159211)
                    ·
                      rfl

theorem cell22_1611508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1611508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611508 prefixEnd_1611508 := by exact prefixLift 1611508
  have htrace : WordTrace (prefixWord ++ tailWord_1611508) baseStart_1611508 baseEnd_1611508 := by
    simpa [prefixWord, tailWord_1611508, baseEnd_1611508] using wordTrace_append hprefix tailTrace_1611508
  have hstable : (prefixWord ++ tailWord_1611508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611508).length < 2 ^ (prefixWord ++ tailWord_1611508).sum := by decide
  have hdescent : baseEnd_1611508 < baseStart_1611508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611530 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_1611530 : Nat := 118140960795 + 1611530 * 2 ^ 59
def prefixEnd_1611530 : Nat := 4983230072969 + 3 ^ 40 * 1611530 * 2
def baseEnd_1611530 : Nat := 551659652760123410109143

theorem tailTrace_1611530 : CollatzResearch.WordTrace tailWord_1611530 prefixEnd_1611530 551659652760123410109143 := by
  unfold tailWord_1611530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14694331962927378064284011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39184885234473008171424029 14694331962927378064284011)
  ·
    refine ⟨22041497944391067096426017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14694331962927378064284011 22041497944391067096426017)
    ·
      refine ⟨16531123458293300322319513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22041497944391067096426017 16531123458293300322319513)
      ·
        refine ⟨12398342593719975241739635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16531123458293300322319513 12398342593719975241739635)
        ·
          refine ⟨18597513890579962862609453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398342593719975241739635 18597513890579962862609453)
          ·
            refine ⟨6974067708967486073478545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18597513890579962862609453 6974067708967486073478545)
            ·
              refine ⟨5230550781725614555108909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974067708967486073478545 5230550781725614555108909)
              ·
                refine ⟨1961456543147105458165841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5230550781725614555108909 1961456543147105458165841)
                ·
                  refine ⟨1471092407360329093624381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961456543147105458165841 1471092407360329093624381)
                  ·
                    refine ⟨551659652760123410109143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471092407360329093624381 551659652760123410109143)
                    ·
                      rfl

theorem cell22_1611530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_1611530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611530 prefixEnd_1611530 := by exact prefixLift 1611530
  have htrace : WordTrace (prefixWord ++ tailWord_1611530) baseStart_1611530 baseEnd_1611530 := by
    simpa [prefixWord, tailWord_1611530, baseEnd_1611530] using wordTrace_append hprefix tailTrace_1611530
  have hstable : (prefixWord ++ tailWord_1611530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611530).length < 2 ^ (prefixWord ++ tailWord_1611530).sum := by decide
  have hdescent : baseEnd_1611530 < baseStart_1611530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611626 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1611626 : Nat := 118140960795 + 1611626 * 2 ^ 59
def prefixEnd_1611626 : Nat := 4983230072969 + 3 ^ 40 * 1611626 * 2
def baseEnd_1611626 : Nat := 551692515522011159708849

theorem tailTrace_1611626 : CollatzResearch.WordTrace tailWord_1611626 prefixEnd_1611626 551692515522011159708849 := by
  unfold tailWord_1611626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695207314840430163157683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39187219506241147101753821 14695207314840430163157683)
  ·
    refine ⟨22042810972260645244736525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14695207314840430163157683 22042810972260645244736525)
    ·
      refine ⟨8266054114597741966776197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22042810972260645244736525 8266054114597741966776197)
      ·
        refine ⟨1549885146487076618770537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8266054114597741966776197 1549885146487076618770537)
        ·
          refine ⟨1162413859865307464077903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549885146487076618770537 1162413859865307464077903)
          ·
            refine ⟨1743620789797961196116855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162413859865307464077903 1743620789797961196116855)
            ·
              refine ⟨2615431184696941794175283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743620789797961196116855 2615431184696941794175283)
              ·
                refine ⟨3923146777045412691262925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615431184696941794175283 3923146777045412691262925)
                ·
                  refine ⟨1471180041392029759223597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3923146777045412691262925 1471180041392029759223597)
                  ·
                    refine ⟨551692515522011159708849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471180041392029759223597 551692515522011159708849)
                    ·
                      rfl

theorem cell22_1611626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1611626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611626 prefixEnd_1611626 := by exact prefixLift 1611626
  have htrace : WordTrace (prefixWord ++ tailWord_1611626) baseStart_1611626 baseEnd_1611626 := by
    simpa [prefixWord, tailWord_1611626, baseEnd_1611626] using wordTrace_append hprefix tailTrace_1611626
  have hstable : (prefixWord ++ tailWord_1611626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611626).length < 2 ^ (prefixWord ++ tailWord_1611626).sum := by decide
  have hdescent : baseEnd_1611626 < baseStart_1611626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611648 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_1611648 : Nat := 118140960795 + 1611648 * 2 ^ 59
def prefixEnd_1611648 : Nat := 4983230072969 + 3 ^ 40 * 1611648 * 2
def baseEnd_1611648 : Nat := 551700046571610435658781

theorem tailTrace_1611648 : CollatzResearch.WordTrace tailWord_1611648 prefixEnd_1611648 551700046571610435658781 := by
  unfold tailWord_1611648
  simp only [CollatzResearch.WordTrace]
  refine ⟨29390815832641009204965799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39187754443521345606621065 29390815832641009204965799)
  ·
    refine ⟨44086223748961513807448699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29390815832641009204965799 44086223748961513807448699)
    ·
      refine ⟨66129335623442270711173049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44086223748961513807448699 66129335623442270711173049)
      ·
        refine ⟨49597001717581703033379787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66129335623442270711173049 49597001717581703033379787)
        ·
          refine ⟨74395502576372554550069681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49597001717581703033379787 74395502576372554550069681)
          ·
            refine ⟨55796626932279415912552261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74395502576372554550069681 55796626932279415912552261)
            ·
              refine ⟨10461867549802390483603549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55796626932279415912552261 10461867549802390483603549)
              ·
                refine ⟨3923200331175896431351331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10461867549802390483603549 3923200331175896431351331)
                ·
                  refine ⟨5884800496763844647026997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923200331175896431351331 5884800496763844647026997)
                  ·
                    refine ⟨551700046571610435658781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5884800496763844647026997 551700046571610435658781)
                    ·
                      rfl

theorem cell22_1611648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_1611648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611648 prefixEnd_1611648 := by exact prefixLift 1611648
  have htrace : WordTrace (prefixWord ++ tailWord_1611648) baseStart_1611648 baseEnd_1611648 := by
    simpa [prefixWord, tailWord_1611648, baseEnd_1611648] using wordTrace_append hprefix tailTrace_1611648
  have hstable : (prefixWord ++ tailWord_1611648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611648).length < 2 ^ (prefixWord ++ tailWord_1611648).sum := by decide
  have hdescent : baseEnd_1611648 < baseStart_1611648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611684 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1611684 : Nat := 118140960795 + 1611684 * 2 ^ 59
def prefixEnd_1611684 : Nat := 4983230072969 + 3 ^ 40 * 1611684 * 2
def baseEnd_1611684 : Nat := 183904123369106113919557

theorem tailTrace_1611684 : CollatzResearch.WordTrace tailWord_1611684 prefixEnd_1611684 183904123369106113919557 := by
  unfold tailWord_1611684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29391472346575798279121053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39188629795434397705494737 29391472346575798279121053)
  ·
    refine ⟨11021802129965924354670395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29391472346575798279121053 11021802129965924354670395)
    ·
      refine ⟨16532703194948886532005593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11021802129965924354670395 16532703194948886532005593)
      ·
        refine ⟨12399527396211664899004195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16532703194948886532005593 12399527396211664899004195)
        ·
          refine ⟨18599291094317497348506293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12399527396211664899004195 18599291094317497348506293)
          ·
            refine ⟨1743683540092265376422465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18599291094317497348506293 1743683540092265376422465)
            ·
              refine ⟨1307762655069199032316849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743683540092265376422465 1307762655069199032316849)
              ·
                refine ⟨980821991301899274237637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307762655069199032316849 980821991301899274237637)
                ·
                  refine ⟨183904123369106113919557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980821991301899274237637 183904123369106113919557)
                  ·
                    rfl

theorem cell22_1611684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1611684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611684 prefixEnd_1611684 := by exact prefixLift 1611684
  have htrace : WordTrace (prefixWord ++ tailWord_1611684) baseStart_1611684 baseEnd_1611684 := by
    simpa [prefixWord, tailWord_1611684, baseEnd_1611684] using wordTrace_append hprefix tailTrace_1611684
  have hstable : (prefixWord ++ tailWord_1611684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611684).length < 2 ^ (prefixWord ++ tailWord_1611684).sum := by decide
  have hdescent : baseEnd_1611684 < baseStart_1611684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611723 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 7]
def baseStart_1611723 : Nat := 118140960795 + 1611723 * 2 ^ 59
def prefixEnd_1611723 : Nat := 4983230072969 + 3 ^ 40 * 1611723 * 2
def baseEnd_1611723 : Nat := 183908573534778413344517

theorem tailTrace_1611723 : CollatzResearch.WordTrace tailWord_1611723 prefixEnd_1611723 183908573534778413344517 := by
  unfold tailWord_1611723
  simp only [CollatzResearch.WordTrace]
  refine ⟨58784367140010306218911823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39189578093340204145941215 58784367140010306218911823)
  ·
    refine ⟨88176550710015459328367735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58784367140010306218911823 88176550710015459328367735)
    ·
      refine ⟨132264826065023188992551603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88176550710015459328367735 132264826065023188992551603)
      ·
        refine ⟨198397239097534783488827405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132264826065023188992551603 198397239097534783488827405)
        ·
          refine ⟨74398964661575543808310277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198397239097534783488827405 74398964661575543808310277)
          ·
            refine ⟨13949805874045414464058177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74398964661575543808310277 13949805874045414464058177)
            ·
              refine ⟨10462354405534060848043633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13949805874045414464058177 10462354405534060848043633)
              ·
                refine ⟨7846765804150545636032725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10462354405534060848043633 7846765804150545636032725)
                ·
                  refine ⟨183908573534778413344517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7846765804150545636032725 183908573534778413344517)
                  ·
                    rfl

theorem cell22_1611723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_1611723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611723 prefixEnd_1611723 := by exact prefixLift 1611723
  have htrace : WordTrace (prefixWord ++ tailWord_1611723) baseStart_1611723 baseEnd_1611723 := by
    simpa [prefixWord, tailWord_1611723, baseEnd_1611723] using wordTrace_append hprefix tailTrace_1611723
  have hstable : (prefixWord ++ tailWord_1611723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611723).length < 2 ^ (prefixWord ++ tailWord_1611723).sum := by decide
  have hdescent : baseEnd_1611723 < baseStart_1611723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611802 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_1611802 : Nat := 118140960795 + 1611802 * 2 ^ 59
def prefixEnd_1611802 : Nat := 4983230072969 + 3 ^ 40 * 1611802 * 2
def baseEnd_1611802 : Nat := 183917587972935122436103

theorem tailTrace_1611802 : CollatzResearch.WordTrace tailWord_1611802 prefixEnd_1611802 183917587972935122436103 := by
  unfold tailWord_1611802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696812126681025677759415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39191499004482735140691773 14696812126681025677759415)
  ·
    refine ⟨22045218190021538516639123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14696812126681025677759415 22045218190021538516639123)
    ·
      refine ⟨33067827285032307774958685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22045218190021538516639123 33067827285032307774958685)
      ·
        refine ⟨12400435231887115415609507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33067827285032307774958685 12400435231887115415609507)
        ·
          refine ⟨18600652847830673123414261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12400435231887115415609507 18600652847830673123414261)
          ·
            refine ⟨1743811204484125605320087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18600652847830673123414261 1743811204484125605320087)
            ·
              refine ⟨2615716806726188407980131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743811204484125605320087 2615716806726188407980131)
              ·
                refine ⟨3923575210089282611970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615716806726188407980131 3923575210089282611970197)
                ·
                  refine ⟨183917587972935122436103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3923575210089282611970197 183917587972935122436103)
                  ·
                    rfl

theorem cell22_1611802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_1611802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611802 prefixEnd_1611802 := by exact prefixLift 1611802
  have htrace : WordTrace (prefixWord ++ tailWord_1611802) baseStart_1611802 baseEnd_1611802 := by
    simpa [prefixWord, tailWord_1611802, baseEnd_1611802] using wordTrace_append hprefix tailTrace_1611802
  have hstable : (prefixWord ++ tailWord_1611802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611802).length < 2 ^ (prefixWord ++ tailWord_1611802).sum := by decide
  have hdescent : baseEnd_1611802 < baseStart_1611802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611909 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 5]
def baseStart_1611909 : Nat := 118140960795 + 1611909 * 2 ^ 59
def prefixEnd_1611909 : Nat := 4983230072969 + 3 ^ 40 * 1611909 * 2
def baseEnd_1611909 : Nat := 183929797401830918294327

theorem tailTrace_1611909 : CollatzResearch.WordTrace tailWord_1611909 prefixEnd_1611909 183929797401830918294327 := by
  unfold tailWord_1611909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58791151117336459985182781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39194100744890973323455187 58791151117336459985182781)
  ·
    refine ⟨22046681669001172494443543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58791151117336459985182781 22046681669001172494443543)
    ·
      refine ⟨33070022503501758741665315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22046681669001172494443543 33070022503501758741665315)
      ·
        refine ⟨49605033755252638112497973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33070022503501758741665315 49605033755252638112497973)
        ·
          refine ⟨4650471914554934823046685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49605033755252638112497973 4650471914554934823046685)
          ·
            refine ⟨1743926967958100558642507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4650471914554934823046685 1743926967958100558642507)
            ·
              refine ⟨2615890451937150837963761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743926967958100558642507 2615890451937150837963761)
              ·
                refine ⟨1961917838952863128472821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2615890451937150837963761 1961917838952863128472821)
                ·
                  refine ⟨183929797401830918294327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1961917838952863128472821 183929797401830918294327)
                  ·
                    rfl

theorem cell22_1611909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_1611909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611909 prefixEnd_1611909 := by exact prefixLift 1611909
  have htrace : WordTrace (prefixWord ++ tailWord_1611909) baseStart_1611909 baseEnd_1611909 := by
    simpa [prefixWord, tailWord_1611909, baseEnd_1611909] using wordTrace_append hprefix tailTrace_1611909
  have hstable : (prefixWord ++ tailWord_1611909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611909).length < 2 ^ (prefixWord ++ tailWord_1611909).sum := by decide
  have hdescent : baseEnd_1611909 < baseStart_1611909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611937 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 6]
def baseStart_1611937 : Nat := 118140960795 + 1611937 * 2 ^ 59
def prefixEnd_1611937 : Nat := 4983230072969 + 3 ^ 40 * 1611937 * 2
def baseEnd_1611937 : Nat := 183932992392570005060965

theorem tailTrace_1611937 : CollatzResearch.WordTrace tailWord_1611937 prefixEnd_1611937 183932992392570005060965 := by
  unfold tailWord_1611937
  simp only [CollatzResearch.WordTrace]
  refine ⟨58792172361235020767202065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39194781574156680511468043 58792172361235020767202065)
  ·
    refine ⟨44094129270926265575401549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58792172361235020767202065 44094129270926265575401549)
    ·
      refine ⟨16535298476597349590775581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44094129270926265575401549 16535298476597349590775581)
      ·
        refine ⟨6200736928724006096540843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16535298476597349590775581 6200736928724006096540843)
        ·
          refine ⟨9301105393086009144811265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200736928724006096540843 9301105393086009144811265)
          ·
            refine ⟨6975829044814506858608449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9301105393086009144811265 6975829044814506858608449)
            ·
              refine ⟨5231871783610880143956337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6975829044814506858608449 5231871783610880143956337)
              ·
                refine ⟨3923903837708160107967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5231871783610880143956337 3923903837708160107967253)
                ·
                  refine ⟨183932992392570005060965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3923903837708160107967253 183932992392570005060965)
                  ·
                    rfl

theorem cell22_1611937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_1611937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611937 prefixEnd_1611937 := by exact prefixLift 1611937
  have htrace : WordTrace (prefixWord ++ tailWord_1611937) baseStart_1611937 baseEnd_1611937 := by
    simpa [prefixWord, tailWord_1611937, baseEnd_1611937] using wordTrace_append hprefix tailTrace_1611937
  have hstable : (prefixWord ++ tailWord_1611937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611937).length < 2 ^ (prefixWord ++ tailWord_1611937).sum := by decide
  have hdescent : baseEnd_1611937 < baseStart_1611937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611982 : List Nat := [4, 1, 1, 1, 4, 1, 1, 9]
def baseStart_1611982 : Nat := 118140960795 + 1611982 * 2 ^ 59
def prefixEnd_1611982 : Nat := 4983230072969 + 3 ^ 40 * 1611982 * 2
def baseEnd_1611982 : Nat := 61312709066371655311973

theorem tailTrace_1611982 : CollatzResearch.WordTrace tailWord_1611982 prefixEnd_1611982 61312709066371655311973 := by
  unfold tailWord_1611982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349226705758999181573775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39195875764047995635060133 7349226705758999181573775)
  ·
    refine ⟨11023840058638498772360663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7349226705758999181573775 11023840058638498772360663)
    ·
      refine ⟨16535760087957748158540995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023840058638498772360663 16535760087957748158540995)
      ·
        refine ⟨24803640131936622237811493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16535760087957748158540995 24803640131936622237811493)
        ·
          refine ⟨4650682524738116669589655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24803640131936622237811493 4650682524738116669589655)
          ·
            refine ⟨6976023787107175004384483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650682524738116669589655 6976023787107175004384483)
            ·
              refine ⟨10464035680660762506576725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976023787107175004384483 10464035680660762506576725)
              ·
                refine ⟨61312709066371655311973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10464035680660762506576725 61312709066371655311973)
                ·
                  rfl

theorem cell22_1611982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_1611982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611982 prefixEnd_1611982 := by exact prefixLift 1611982
  have htrace : WordTrace (prefixWord ++ tailWord_1611982) baseStart_1611982 baseEnd_1611982 := by
    simpa [prefixWord, tailWord_1611982, baseEnd_1611982] using wordTrace_append hprefix tailTrace_1611982
  have hstable : (prefixWord ++ tailWord_1611982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611982).length < 2 ^ (prefixWord ++ tailWord_1611982).sum := by decide
  have hdescent : baseEnd_1611982 < baseStart_1611982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611986 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1611986 : Nat := 118140960795 + 1611986 * 2 ^ 59
def prefixEnd_1611986 : Nat := 4983230072969 + 3 ^ 40 * 1611986 * 2
def baseEnd_1611986 : Nat := 551815750879090220707745

theorem tailTrace_1611986 : CollatzResearch.WordTrace tailWord_1611986 prefixEnd_1611986 551815750879090220707745 := by
  unfold tailWord_1611986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14698489884514375533933953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39195973025371668090490541 14698489884514375533933953)
  ·
    refine ⟨11023867413385781650450465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14698489884514375533933953 11023867413385781650450465)
    ·
      refine ⟨8267900560039336237837849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11023867413385781650450465 8267900560039336237837849)
      ·
        refine ⟨6200925420029502178378387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8267900560039336237837849 6200925420029502178378387)
        ·
          refine ⟨9301388130044253267567581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200925420029502178378387 9301388130044253267567581)
          ·
            refine ⟨3488020548766594975337843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9301388130044253267567581 3488020548766594975337843)
            ·
              refine ⟨5232030823149892463006765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488020548766594975337843 5232030823149892463006765)
              ·
                refine ⟨1962011558681209673627537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5232030823149892463006765 1962011558681209673627537)
                ·
                  refine ⟨1471508669010907255220653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962011558681209673627537 1471508669010907255220653)
                  ·
                    refine ⟨551815750879090220707745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471508669010907255220653 551815750879090220707745)
                    ·
                      rfl

theorem cell22_1611986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1611986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1611986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1611986 prefixEnd_1611986 := by exact prefixLift 1611986
  have htrace : WordTrace (prefixWord ++ tailWord_1611986) baseStart_1611986 baseEnd_1611986 := by
    simpa [prefixWord, tailWord_1611986, baseEnd_1611986] using wordTrace_append hprefix tailTrace_1611986
  have hstable : (prefixWord ++ tailWord_1611986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611986).length < 2 ^ (prefixWord ++ tailWord_1611986).sum := by decide
  have hdescent : baseEnd_1611986 < baseStart_1611986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612031 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 1, 3]
def baseStart_1612031 : Nat := 118140960795 + 1612031 * 2 ^ 59
def prefixEnd_1612031 : Nat := 4983230072969 + 3 ^ 40 * 1612031 * 2
def baseEnd_1612031 : Nat := 551831155298725103332607

theorem tailTrace_1612031 : CollatzResearch.WordTrace tailWord_1612031 prefixEnd_1612031 551831155298725103332607 := by
  unfold tailWord_1612031
  simp only [CollatzResearch.WordTrace]
  refine ⟨58795600822894474821123947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39197067215262983214082631 58795600822894474821123947)
  ·
    refine ⟨88193401234341712231685921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58795600822894474821123947 88193401234341712231685921)
    ·
      refine ⟨66145050925756284173764441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88193401234341712231685921 66145050925756284173764441)
      ·
        refine ⟨49608788194317213130323331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66145050925756284173764441 49608788194317213130323331)
        ·
          refine ⟨74413182291475819695484997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49608788194317213130323331 74413182291475819695484997)
          ·
            refine ⟨13952471679651716192903437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74413182291475819695484997 13952471679651716192903437)
            ·
              refine ⟨5232176879869393572338789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13952471679651716192903437 5232176879869393572338789)
              ·
                refine ⟨981033164975511294813523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5232176879869393572338789 981033164975511294813523)
                ·
                  refine ⟨1471549747463266942220285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981033164975511294813523 1471549747463266942220285)
                  ·
                    refine ⟨551831155298725103332607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471549747463266942220285 551831155298725103332607)
                    ·
                      rfl

theorem cell22_1612031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_1612031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612031 prefixEnd_1612031 := by exact prefixLift 1612031
  have htrace : WordTrace (prefixWord ++ tailWord_1612031) baseStart_1612031 baseEnd_1612031 := by
    simpa [prefixWord, tailWord_1612031, baseEnd_1612031] using wordTrace_append hprefix tailTrace_1612031
  have hstable : (prefixWord ++ tailWord_1612031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612031).length < 2 ^ (prefixWord ++ tailWord_1612031).sum := by decide
  have hdescent : baseEnd_1612031 < baseStart_1612031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612042 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1612042 : Nat := 118140960795 + 1612042 * 2 ^ 59
def prefixEnd_1612042 : Nat := 4983230072969 + 3 ^ 40 * 1612042 * 2
def baseEnd_1612042 : Nat := 551834920823524741307573

theorem tailTrace_1612042 : CollatzResearch.WordTrace tailWord_1612042 prefixEnd_1612042 551834920823524741307573 := by
  unfold tailWord_1612042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14699000506463655924943595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39197334683903082466516253 14699000506463655924943595)
  ·
    refine ⟨22048500759695483887415393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14699000506463655924943595 22048500759695483887415393)
    ·
      refine ⟨16536375569771612915561545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22048500759695483887415393 16536375569771612915561545)
      ·
        refine ⟨12402281677328709686671159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16536375569771612915561545 12402281677328709686671159)
        ·
          refine ⟨18603422515993064530006739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402281677328709686671159 18603422515993064530006739)
          ·
            refine ⟨27905133773989596795010109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18603422515993064530006739 27905133773989596795010109)
            ·
              refine ⟨10464425165246098798128791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27905133773989596795010109 10464425165246098798128791)
              ·
                refine ⟨15696637747869148197193187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10464425165246098798128791 15696637747869148197193187)
                ·
                  refine ⟨23544956621803722295789781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15696637747869148197193187 23544956621803722295789781)
                  ·
                    refine ⟨551834920823524741307573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23544956621803722295789781 551834920823524741307573)
                    ·
                      rfl

theorem cell22_1612042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1612042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612042 prefixEnd_1612042 := by exact prefixLift 1612042
  have htrace : WordTrace (prefixWord ++ tailWord_1612042) baseStart_1612042 baseEnd_1612042 := by
    simpa [prefixWord, tailWord_1612042, baseEnd_1612042] using wordTrace_append hprefix tailTrace_1612042
  have hstable : (prefixWord ++ tailWord_1612042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612042).length < 2 ^ (prefixWord ++ tailWord_1612042).sum := by decide
  have hdescent : baseEnd_1612042 < baseStart_1612042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612087 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1612087 : Nat := 118140960795 + 1612087 * 2 ^ 59
def prefixEnd_1612087 : Nat := 4983230072969 + 3 ^ 40 * 1612087 * 2
def baseEnd_1612087 : Nat := 551850325243159623932435

theorem tailTrace_1612087 : CollatzResearch.WordTrace tailWord_1612087 prefixEnd_1612087 551850325243159623932435 := by
  unfold tailWord_1612087
  simp only [CollatzResearch.WordTrace]
  refine ⟨58797643310691596385162515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39198428873794397590108343 58797643310691596385162515)
  ·
    refine ⟨88196464966037394577743773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58797643310691596385162515 88196464966037394577743773)
    ·
      refine ⟨33073674362264022966653915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88196464966037394577743773 33073674362264022966653915)
      ·
        refine ⟨49610511543396034449980873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33073674362264022966653915 49610511543396034449980873)
        ·
          refine ⟨37207883657547025837485655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49610511543396034449980873 37207883657547025837485655)
          ·
            refine ⟨55811825486320538756228483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37207883657547025837485655 55811825486320538756228483)
            ·
              refine ⟨83717738229480808134342725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55811825486320538756228483 83717738229480808134342725)
              ·
                refine ⟨15697075918027651525189261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83717738229480808134342725 15697075918027651525189261)
                ·
                  refine ⟨5886403469260369321945973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15697075918027651525189261 5886403469260369321945973)
                  ·
                    refine ⟨551850325243159623932435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5886403469260369321945973 551850325243159623932435)
                    ·
                      rfl

theorem cell22_1612087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1612087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612087 prefixEnd_1612087 := by exact prefixLift 1612087
  have htrace : WordTrace (prefixWord ++ tailWord_1612087) baseStart_1612087 baseEnd_1612087 := by
    simpa [prefixWord, tailWord_1612087, baseEnd_1612087] using wordTrace_append hprefix tailTrace_1612087
  have hstable : (prefixWord ++ tailWord_1612087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612087).length < 2 ^ (prefixWord ++ tailWord_1612087).sum := by decide
  have hdescent : baseEnd_1612087 < baseStart_1612087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612089 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 6]
def baseStart_1612089 : Nat := 118140960795 + 1612089 * 2 ^ 59
def prefixEnd_1612089 : Nat := 4983230072969 + 3 ^ 40 * 1612089 * 2
def baseEnd_1612089 : Nat := 183950336628010761794143

theorem tailTrace_1612089 : CollatzResearch.WordTrace tailWord_1612089 prefixEnd_1612089 183950336628010761794143 := by
  unfold tailWord_1612089
  simp only [CollatzResearch.WordTrace]
  refine ⟨58797716256684350726735321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39198477504456233817823547 58797716256684350726735321)
  ·
    refine ⟨44098287192513263045051491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58797716256684350726735321 44098287192513263045051491)
    ·
      refine ⟨66147430788769894567577237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44098287192513263045051491 66147430788769894567577237)
      ·
        refine ⟨3100660818223588807855183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66147430788769894567577237 3100660818223588807855183)
        ·
          refine ⟨4650991227335383211782775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100660818223588807855183 4650991227335383211782775)
          ·
            refine ⟨6976486841003074817674163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650991227335383211782775 6976486841003074817674163)
            ·
              refine ⟨10464730261504612226511245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976486841003074817674163 10464730261504612226511245)
              ·
                refine ⟨3924273848064229584941717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10464730261504612226511245 3924273848064229584941717)
                ·
                  refine ⟨183950336628010761794143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3924273848064229584941717 183950336628010761794143)
                  ·
                    rfl

theorem cell22_1612089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_1612089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612089 prefixEnd_1612089 := by exact prefixLift 1612089
  have htrace : WordTrace (prefixWord ++ tailWord_1612089) baseStart_1612089 baseEnd_1612089 := by
    simpa [prefixWord, tailWord_1612089, baseEnd_1612089] using wordTrace_append hprefix tailTrace_1612089
  have hstable : (prefixWord ++ tailWord_1612089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612089).length < 2 ^ (prefixWord ++ tailWord_1612089).sum := by decide
  have hdescent : baseEnd_1612089 < baseStart_1612089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612104 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_1612104 : Nat := 118140960795 + 1612104 * 2 ^ 59
def prefixEnd_1612104 : Nat := 4983230072969 + 3 ^ 40 * 1612104 * 2
def baseEnd_1612104 : Nat := 551856144690577246257383

theorem tailTrace_1612104 : CollatzResearch.WordTrace tailWord_1612104 prefixEnd_1612104 551856144690577246257383 := by
  unfold tailWord_1612104
  simp only [CollatzResearch.WordTrace]
  refine ⟨29399131675815004144265683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39198842234420005525687577 29399131675815004144265683)
  ·
    refine ⟨44098697513722506216398525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29399131675815004144265683 44098697513722506216398525)
    ·
      refine ⟨16537011567645939831149447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44098697513722506216398525 16537011567645939831149447)
      ·
        refine ⟨24805517351468909746724171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16537011567645939831149447 24805517351468909746724171)
        ·
          refine ⟨37208276027203364620086257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24805517351468909746724171 37208276027203364620086257)
          ·
            refine ⟨27906207020402523465064693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37208276027203364620086257 27906207020402523465064693)
            ·
              refine ⟨2616206908162736574849815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27906207020402523465064693 2616206908162736574849815)
              ·
                refine ⟨3924310362244104862274723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616206908162736574849815 3924310362244104862274723)
                ·
                  refine ⟨5886465543366157293412085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924310362244104862274723 5886465543366157293412085)
                  ·
                    refine ⟨551856144690577246257383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5886465543366157293412085 551856144690577246257383)
                    ·
                      rfl

theorem cell22_1612104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_1612104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612104 prefixEnd_1612104 := by exact prefixLift 1612104
  have htrace : WordTrace (prefixWord ++ tailWord_1612104) baseStart_1612104 baseEnd_1612104 := by
    simpa [prefixWord, tailWord_1612104, baseEnd_1612104] using wordTrace_append hprefix tailTrace_1612104
  have hstable : (prefixWord ++ tailWord_1612104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612104).length < 2 ^ (prefixWord ++ tailWord_1612104).sum := by decide
  have hdescent : baseEnd_1612104 < baseStart_1612104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612119 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1612119 : Nat := 118140960795 + 1612119 * 2 ^ 59
def prefixEnd_1612119 : Nat := 4983230072969 + 3 ^ 40 * 1612119 * 2
def baseEnd_1612119 : Nat := 551861279497122207132337

theorem tailTrace_1612119 : CollatzResearch.WordTrace tailWord_1612119 prefixEnd_1612119 551861279497122207132337 := by
  unfold tailWord_1612119
  simp only [CollatzResearch.WordTrace]
  refine ⟨58798810446575665850327411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39199206964383777233551607 58798810446575665850327411)
  ·
    refine ⟨88198215669863498775491117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58798810446575665850327411 88198215669863498775491117)
    ·
      refine ⟨33074330876198812040809169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88198215669863498775491117 33074330876198812040809169)
      ·
        refine ⟨24805748157149109030606877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33074330876198812040809169 24805748157149109030606877)
        ·
          refine ⟨9302155558930915886477579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24805748157149109030606877 9302155558930915886477579)
          ·
            refine ⟨13953233338396373829716369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9302155558930915886477579 13953233338396373829716369)
            ·
              refine ⟨10464925003797280372287277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13953233338396373829716369 10464925003797280372287277)
              ·
                refine ⟨3924346876423980139607729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10464925003797280372287277 3924346876423980139607729)
                ·
                  refine ⟨2943260157317985104705797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924346876423980139607729 2943260157317985104705797)
                  ·
                    refine ⟨551861279497122207132337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943260157317985104705797 551861279497122207132337)
                    ·
                      rfl

theorem cell22_1612119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1612119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612119 prefixEnd_1612119 := by exact prefixLift 1612119
  have htrace : WordTrace (prefixWord ++ tailWord_1612119) baseStart_1612119 baseEnd_1612119 := by
    simpa [prefixWord, tailWord_1612119, baseEnd_1612119] using wordTrace_append hprefix tailTrace_1612119
  have hstable : (prefixWord ++ tailWord_1612119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612119).length < 2 ^ (prefixWord ++ tailWord_1612119).sum := by decide
  have hdescent : baseEnd_1612119 < baseStart_1612119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612136 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1612136 : Nat := 118140960795 + 1612136 * 2 ^ 59
def prefixEnd_1612136 : Nat := 4983230072969 + 3 ^ 40 * 1612136 * 2
def baseEnd_1612136 : Nat := 551867098944539829457285

theorem tailTrace_1612136 : CollatzResearch.WordTrace tailWord_1612136 prefixEnd_1612136 551867098944539829457285 := by
  unfold tailWord_1612136
  simp only [CollatzResearch.WordTrace]
  refine ⟨29399715243757038876848131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39199620325009385169130841 29399715243757038876848131)
  ·
    refine ⟨44099572865635558315272197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29399715243757038876848131 44099572865635558315272197)
    ·
      refine ⟨8268669912306667184113537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44099572865635558315272197 8268669912306667184113537)
      ·
        refine ⟨6201502434230000388085153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8268669912306667184113537 6201502434230000388085153)
        ·
          refine ⟨4651126825672500291063865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6201502434230000388085153 4651126825672500291063865)
          ·
            refine ⟨3488345119254375218297899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651126825672500291063865 3488345119254375218297899)
            ·
              refine ⟨5232517678881562827446849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488345119254375218297899 5232517678881562827446849)
              ·
                refine ⟨3924388259161172120585137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232517678881562827446849 3924388259161172120585137)
                ·
                  refine ⟨2943291194370879090438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924388259161172120585137 2943291194370879090438853)
                  ·
                    refine ⟨551867098944539829457285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943291194370879090438853 551867098944539829457285)
                    ·
                      rfl

theorem cell22_1612136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1612136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612136 prefixEnd_1612136 := by exact prefixLift 1612136
  have htrace : WordTrace (prefixWord ++ tailWord_1612136) baseStart_1612136 baseEnd_1612136 := by
    simpa [prefixWord, tailWord_1612136, baseEnd_1612136] using wordTrace_append hprefix tailTrace_1612136
  have hstable : (prefixWord ++ tailWord_1612136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612136).length < 2 ^ (prefixWord ++ tailWord_1612136).sum := by decide
  have hdescent : baseEnd_1612136 < baseStart_1612136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612147 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_1612147 : Nat := 118140960795 + 1612147 * 2 ^ 59
def prefixEnd_1612147 : Nat := 4983230072969 + 3 ^ 40 * 1612147 * 2
def baseEnd_1612147 : Nat := 551870864469339467432251

theorem tailTrace_1612147 : CollatzResearch.WordTrace tailWord_1612147 prefixEnd_1612147 551870864469339467432251 := by
  unfold tailWord_1612147
  simp only [CollatzResearch.WordTrace]
  refine ⟨58799831690474226632346695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39199887793649484421564463 58799831690474226632346695)
  ·
    refine ⟨88199747535711339948520043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58799831690474226632346695 88199747535711339948520043)
    ·
      refine ⟨132299621303567009922780065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88199747535711339948520043 132299621303567009922780065)
      ·
        refine ⟨99224715977675257442085049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132299621303567009922780065 99224715977675257442085049)
        ·
          refine ⟨74418536983256443081563787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99224715977675257442085049 74418536983256443081563787)
          ·
            refine ⟨111627805474884664622345681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74418536983256443081563787 111627805474884664622345681)
            ·
              refine ⟨83720854106163498466759261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111627805474884664622345681 83720854106163498466759261)
              ·
                refine ⟨31395320289811311925034723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83720854106163498466759261 31395320289811311925034723)
                ·
                  refine ⟨47092980434716967887552085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31395320289811311925034723 47092980434716967887552085)
                  ·
                    refine ⟨551870864469339467432251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47092980434716967887552085 551870864469339467432251)
                    ·
                      rfl

theorem cell22_1612147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_1612147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612147 prefixEnd_1612147 := by exact prefixLift 1612147
  have htrace : WordTrace (prefixWord ++ tailWord_1612147) baseStart_1612147 baseEnd_1612147 := by
    simpa [prefixWord, tailWord_1612147, baseEnd_1612147] using wordTrace_append hprefix tailTrace_1612147
  have hstable : (prefixWord ++ tailWord_1612147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612147).length < 2 ^ (prefixWord ++ tailWord_1612147).sum := by decide
  have hdescent : baseEnd_1612147 < baseStart_1612147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612202 : List Nat := [3, 1, 6, 1, 2, 1, 1, 7]
def baseStart_1612202 : Nat := 118140960795 + 1612202 * 2 ^ 59
def prefixEnd_1612202 : Nat := 4983230072969 + 3 ^ 40 * 1612202 * 2
def baseEnd_1612202 : Nat := 61321076899259739700787

theorem tailTrace_1612202 : CollatzResearch.WordTrace tailWord_1612202 prefixEnd_1612202 61321076899259739700787 := by
  unfold tailWord_1612202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700459426318742756399715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39201225136849980683732573 14700459426318742756399715)
  ·
    refine ⟨22050689139478114134599573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14700459426318742756399715 22050689139478114134599573)
    ·
      refine ⟨1033626053413036600059355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22050689139478114134599573 1033626053413036600059355)
      ·
        refine ⟨1550439080119554900089033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033626053413036600059355 1550439080119554900089033)
        ·
          refine ⟨1162829310089666175066775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550439080119554900089033 1162829310089666175066775)
          ·
            refine ⟨1744243965134499262600163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162829310089666175066775 1744243965134499262600163)
            ·
              refine ⟨2616365947701748893900245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744243965134499262600163 2616365947701748893900245)
              ·
                refine ⟨61321076899259739700787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2616365947701748893900245 61321076899259739700787)
                ·
                  rfl

theorem cell22_1612202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_1612202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612202 prefixEnd_1612202 := by exact prefixLift 1612202
  have htrace : WordTrace (prefixWord ++ tailWord_1612202) baseStart_1612202 baseEnd_1612202 := by
    simpa [prefixWord, tailWord_1612202, baseEnd_1612202] using wordTrace_append hprefix tailTrace_1612202
  have hstable : (prefixWord ++ tailWord_1612202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612202).length < 2 ^ (prefixWord ++ tailWord_1612202).sum := by decide
  have hdescent : baseEnd_1612202 < baseStart_1612202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612256 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_1612256 : Nat := 118140960795 + 1612256 * 2 ^ 59
def prefixEnd_1612256 : Nat := 4983230072969 + 3 ^ 40 * 1612256 * 2
def baseEnd_1612256 : Nat := 551908177396899516456917

theorem tailTrace_1612256 : CollatzResearch.WordTrace tailWord_1612256 prefixEnd_1612256 551908177396899516456917 := by
  unfold tailWord_1612256
  simp only [CollatzResearch.WordTrace]
  refine ⟨29401903623539669124032311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39202538164719558832043081 29401903623539669124032311)
  ·
    refine ⟨44102855435309503686048467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29401903623539669124032311 44102855435309503686048467)
    ·
      refine ⟨66154283152964255529072701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44102855435309503686048467 66154283152964255529072701)
      ·
        refine ⟨24807856182361595823402263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66154283152964255529072701 24807856182361595823402263)
        ·
          refine ⟨37211784273542393735103395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24807856182361595823402263 37211784273542393735103395)
          ·
            refine ⟨55817676410313590602655093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37211784273542393735103395 55817676410313590602655093)
            ·
              refine ⟨5232907163466899118998915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55817676410313590602655093 5232907163466899118998915)
              ·
                refine ⟨7849360745200348678498373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232907163466899118998915 7849360745200348678498373)
                ·
                  refine ⟨1471755139725065377218445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7849360745200348678498373 1471755139725065377218445)
                  ·
                    refine ⟨551908177396899516456917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471755139725065377218445 551908177396899516456917)
                    ·
                      rfl

theorem cell22_1612256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_1612256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612256 prefixEnd_1612256 := by exact prefixLift 1612256
  have htrace : WordTrace (prefixWord ++ tailWord_1612256) baseStart_1612256 baseEnd_1612256 := by
    simpa [prefixWord, tailWord_1612256, baseEnd_1612256] using wordTrace_append hprefix tailTrace_1612256
  have hstable : (prefixWord ++ tailWord_1612256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612256).length < 2 ^ (prefixWord ++ tailWord_1612256).sum := by decide
  have hdescent : baseEnd_1612256 < baseStart_1612256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612284 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1612284 : Nat := 118140960795 + 1612284 * 2 ^ 59
def prefixEnd_1612284 : Nat := 4983230072969 + 3 ^ 40 * 1612284 * 2
def baseEnd_1612284 : Nat := 551917762369116776756831

theorem tailTrace_1612284 : CollatzResearch.WordTrace tailWord_1612284 prefixEnd_1612284 551917762369116776756831 := by
  unfold tailWord_1612284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29402414245488949515041953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39203218993985266020055937 29402414245488949515041953)
  ·
    refine ⟨22051810684116712136281465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29402414245488949515041953 22051810684116712136281465)
    ·
      refine ⟨16538858013087534102211099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22051810684116712136281465 16538858013087534102211099)
      ·
        refine ⟨24808287019631301153316649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16538858013087534102211099 24808287019631301153316649)
        ·
          refine ⟨18606215264723475864987487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24808287019631301153316649 18606215264723475864987487)
          ·
            refine ⟨27909322897085213797481231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18606215264723475864987487 27909322897085213797481231)
            ·
              refine ⟨41863984345627820696221847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27909322897085213797481231 41863984345627820696221847)
              ·
                refine ⟨62795976518441731044332771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41863984345627820696221847 62795976518441731044332771)
                ·
                  refine ⟨94193964777662596566499157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62795976518441731044332771 94193964777662596566499157)
                  ·
                    refine ⟨551917762369116776756831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94193964777662596566499157 551917762369116776756831)
                    ·
                      rfl

theorem cell22_1612284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1612284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612284 prefixEnd_1612284 := by exact prefixLift 1612284
  have htrace : WordTrace (prefixWord ++ tailWord_1612284) baseStart_1612284 baseEnd_1612284 := by
    simpa [prefixWord, tailWord_1612284, baseEnd_1612284] using wordTrace_append hprefix tailTrace_1612284
  have hstable : (prefixWord ++ tailWord_1612284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612284).length < 2 ^ (prefixWord ++ tailWord_1612284).sum := by decide
  have hdescent : baseEnd_1612284 < baseStart_1612284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612324 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_1612324 : Nat := 118140960795 + 1612324 * 2 ^ 59
def prefixEnd_1612324 : Nat := 4983230072969 + 3 ^ 40 * 1612324 * 2
def baseEnd_1612324 : Nat := 551931455186570005756709

theorem tailTrace_1612324 : CollatzResearch.WordTrace tailWord_1612324 prefixEnd_1612324 551931455186570005756709 := by
  unfold tailWord_1612324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403143705416492930770013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39204191607221990574360017 29403143705416492930770013)
  ·
    refine ⟨11026178889531184849038755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29403143705416492930770013 11026178889531184849038755)
    ·
      refine ⟨16539268334296777273558133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026178889531184849038755 16539268334296777273558133)
      ·
        refine ⟨1550556406340322869396075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16539268334296777273558133 1550556406340322869396075)
        ·
          refine ⟨2325834609510484304094113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550556406340322869396075 2325834609510484304094113)
          ·
            refine ⟨1744375957132863228070585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325834609510484304094113 1744375957132863228070585)
            ·
              refine ⟨1308281967849647421052939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744375957132863228070585 1308281967849647421052939)
              ·
                refine ⟨1962422951774471131579409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308281967849647421052939 1962422951774471131579409)
                ·
                  refine ⟨1471817213830853348684557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962422951774471131579409 1471817213830853348684557)
                  ·
                    refine ⟨551931455186570005756709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471817213830853348684557 551931455186570005756709)
                    ·
                      rfl

theorem cell22_1612324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_1612324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612324 prefixEnd_1612324 := by exact prefixLift 1612324
  have htrace : WordTrace (prefixWord ++ tailWord_1612324) baseStart_1612324 baseEnd_1612324 := by
    simpa [prefixWord, tailWord_1612324, baseEnd_1612324] using wordTrace_append hprefix tailTrace_1612324
  have hstable : (prefixWord ++ tailWord_1612324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612324).length < 2 ^ (prefixWord ++ tailWord_1612324).sum := by decide
  have hdescent : baseEnd_1612324 < baseStart_1612324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612365 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1612365 : Nat := 118140960795 + 1612365 * 2 ^ 59
def prefixEnd_1612365 : Nat := 4983230072969 + 3 ^ 40 * 1612365 * 2
def baseEnd_1612365 : Nat := 183981830108153188493861

theorem tailTrace_1612365 : CollatzResearch.WordTrace tailWord_1612365 prefixEnd_1612365 183981830108153188493861 := by
  unfold tailWord_1612365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58807782803684449863782549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39205188535789633242521699 58807782803684449863782549)
  ·
    refine ⟨2756614818922708587364807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58807782803684449863782549 2756614818922708587364807)
    ·
      refine ⟨4134922228384062881047211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2756614818922708587364807 4134922228384062881047211)
      ·
        refine ⟨6202383342576094321570817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4134922228384062881047211 6202383342576094321570817)
        ·
          refine ⟨4651787506932070741178113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6202383342576094321570817 4651787506932070741178113)
          ·
            refine ⟨3488840630199053055883585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651787506932070741178113 3488840630199053055883585)
            ·
              refine ⟨2616630472649289791912689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3488840630199053055883585 2616630472649289791912689)
              ·
                refine ⟨1962472854486967343934517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616630472649289791912689 1962472854486967343934517)
                ·
                  refine ⟨183981830108153188493861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1962472854486967343934517 183981830108153188493861)
                  ·
                    rfl

theorem cell22_1612365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1612365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612365 prefixEnd_1612365 := by exact prefixLift 1612365
  have htrace : WordTrace (prefixWord ++ tailWord_1612365) baseStart_1612365 baseEnd_1612365 := by
    simpa [prefixWord, tailWord_1612365, baseEnd_1612365] using wordTrace_append hprefix tailTrace_1612365
  have hstable : (prefixWord ++ tailWord_1612365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612365).length < 2 ^ (prefixWord ++ tailWord_1612365).sum := by decide
  have hdescent : baseEnd_1612365 < baseStart_1612365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612421 : List Nat := [1, 3, 1, 1, 4, 3, 9]
def baseStart_1612421 : Nat := 118140960795 + 1612421 * 2 ^ 59
def prefixEnd_1612421 : Nat := 4983230072969 + 3 ^ 40 * 1612421 * 2
def baseEnd_1612421 : Nat := 20443135565514595780793

theorem tailTrace_1612421 : CollatzResearch.WordTrace tailWord_1612421 prefixEnd_1612421 20443135565514595780793 := by
  unfold tailWord_1612421
  simp only [CollatzResearch.WordTrace]
  refine ⟨58809825291481571427821117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39206550194321047618547411 58809825291481571427821117)
  ·
    refine ⟨22053684484305589285432919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58809825291481571427821117 22053684484305589285432919)
    ·
      refine ⟨33080526726458383928149379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22053684484305589285432919 33080526726458383928149379)
      ·
        refine ⟨49620790089687575892224069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33080526726458383928149379 49620790089687575892224069)
        ·
          refine ⟨9303898141816420479792013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49620790089687575892224069 9303898141816420479792013)
          ·
            refine ⟨3488961803181157679922005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9303898141816420479792013 3488961803181157679922005)
            ·
              refine ⟨20443135565514595780793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3488961803181157679922005 20443135565514595780793)
              ·
                rfl

theorem cell22_1612421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 9].length) (baseStart_1612421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612421 prefixEnd_1612421 := by exact prefixLift 1612421
  have htrace : WordTrace (prefixWord ++ tailWord_1612421) baseStart_1612421 baseEnd_1612421 := by
    simpa [prefixWord, tailWord_1612421, baseEnd_1612421] using wordTrace_append hprefix tailTrace_1612421
  have hstable : (prefixWord ++ tailWord_1612421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612421).length < 2 ^ (prefixWord ++ tailWord_1612421).sum := by decide
  have hdescent : baseEnd_1612421 < baseStart_1612421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612442 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_1612442 : Nat := 118140960795 + 1612442 * 2 ^ 59
def prefixEnd_1612442 : Nat := 4983230072969 + 3 ^ 40 * 1612442 * 2
def baseEnd_1612442 : Nat := 551971848998057031306347

theorem tailTrace_1612442 : CollatzResearch.WordTrace tailWord_1612442 prefixEnd_1612442 551971848998057031306347 := by
  unfold tailWord_1612442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702647806101373003583895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39207060816270328009557053 14702647806101373003583895)
  ·
    refine ⟨22053971709152059505375843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14702647806101373003583895 22053971709152059505375843)
    ·
      refine ⟨33080957563728089258063765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22053971709152059505375843 33080957563728089258063765)
      ·
        refine ⟨1550669885799754183971739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33080957563728089258063765 1550669885799754183971739)
        ·
          refine ⟨2326004828699631275957609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550669885799754183971739 2326004828699631275957609)
          ·
            refine ⟨1744503621524723456968207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326004828699631275957609 1744503621524723456968207)
            ·
              refine ⟨2616755432287085185452311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744503621524723456968207 2616755432287085185452311)
              ·
                refine ⟨3925133148430627778178467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616755432287085185452311 3925133148430627778178467)
                ·
                  refine ⟨5887699722645941667267701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925133148430627778178467 5887699722645941667267701)
                  ·
                    refine ⟨551971848998057031306347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5887699722645941667267701 551971848998057031306347)
                    ·
                      rfl

theorem cell22_1612442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_1612442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612442 prefixEnd_1612442 := by exact prefixLift 1612442
  have htrace : WordTrace (prefixWord ++ tailWord_1612442) baseStart_1612442 baseEnd_1612442 := by
    simpa [prefixWord, tailWord_1612442, baseEnd_1612442] using wordTrace_append hprefix tailTrace_1612442
  have hstable : (prefixWord ++ tailWord_1612442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612442).length < 2 ^ (prefixWord ++ tailWord_1612442).sum := by decide
  have hdescent : baseEnd_1612442 < baseStart_1612442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612455 : List Nat := [1, 1, 6, 3, 1, 1, 1, 8]
def baseStart_1612455 : Nat := 118140960795 + 1612455 * 2 ^ 59
def prefixEnd_1612455 : Nat := 4983230072969 + 3 ^ 40 * 1612455 * 2
def baseEnd_1612455 : Nat := 61330699907081036747923

theorem tailTrace_1612455 : CollatzResearch.WordTrace tailWord_1612455 prefixEnd_1612455 61330699907081036747923 := by
  unfold tailWord_1612455
  simp only [CollatzResearch.WordTrace]
  refine ⟨58811065373358395234558819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39207376915572263489705879 58811065373358395234558819)
  ·
    refine ⟨88216598060037592851838229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58811065373358395234558819 88216598060037592851838229)
    ·
      refine ⟨4135153034064262164929917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88216598060037592851838229 4135153034064262164929917)
      ·
        refine ⟨1550682387774098311848719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4135153034064262164929917 1550682387774098311848719)
        ·
          refine ⟨2326023581661147467773079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550682387774098311848719 2326023581661147467773079)
          ·
            refine ⟨3489035372491721201659619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326023581661147467773079 3489035372491721201659619)
            ·
              refine ⟨5233553058737581802489429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489035372491721201659619 5233553058737581802489429)
              ·
                refine ⟨61330699907081036747923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5233553058737581802489429 61330699907081036747923)
                ·
                  rfl

theorem cell22_1612455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 8].length) (baseStart_1612455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612455 prefixEnd_1612455 := by exact prefixLift 1612455
  have htrace : WordTrace (prefixWord ++ tailWord_1612455) baseStart_1612455 baseEnd_1612455 := by
    simpa [prefixWord, tailWord_1612455, baseEnd_1612455] using wordTrace_append hprefix tailTrace_1612455
  have hstable : (prefixWord ++ tailWord_1612455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612455).length < 2 ^ (prefixWord ++ tailWord_1612455).sum := by decide
  have hdescent : baseEnd_1612455 < baseStart_1612455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612493 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1612493 : Nat := 118140960795 + 1612493 * 2 ^ 59
def prefixEnd_1612493 : Nat := 4983230072969 + 3 ^ 40 * 1612493 * 2
def baseEnd_1612493 : Nat := 551989307340309898281191

theorem tailTrace_1612493 : CollatzResearch.WordTrace tailWord_1612493 prefixEnd_1612493 551989307340309898281191 := by
  unfold tailWord_1612493
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812451347220727724442133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39208300898147151816294755 58812451347220727724442133)
  ·
    refine ⟨2756833656900971612083225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58812451347220727724442133 2756833656900971612083225)
    ·
      refine ⟨2067625242675728709062419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2756833656900971612083225 2067625242675728709062419)
      ·
        refine ⟨3101437864013593063593629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067625242675728709062419 3101437864013593063593629)
        ·
          refine ⟨1163039199005097398847611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3101437864013593063593629 1163039199005097398847611)
          ·
            refine ⟨1744558798507646098271417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163039199005097398847611 1744558798507646098271417)
            ·
              refine ⟨1308419098880734573703563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744558798507646098271417 1308419098880734573703563)
              ·
                refine ⟨1962628648321101860555345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308419098880734573703563 1962628648321101860555345)
                ·
                  refine ⟨1471971486240826395416509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962628648321101860555345 1471971486240826395416509)
                  ·
                    refine ⟨551989307340309898281191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471971486240826395416509 551989307340309898281191)
                    ·
                      rfl

theorem cell22_1612493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1612493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612493 prefixEnd_1612493 := by exact prefixLift 1612493
  have htrace : WordTrace (prefixWord ++ tailWord_1612493) baseStart_1612493 baseEnd_1612493 := by
    simpa [prefixWord, tailWord_1612493, baseEnd_1612493] using wordTrace_append hprefix tailTrace_1612493
  have hstable : (prefixWord ++ tailWord_1612493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612493).length < 2 ^ (prefixWord ++ tailWord_1612493).sum := by decide
  have hdescent : baseEnd_1612493 < baseStart_1612493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612558 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1612558 : Nat := 118140960795 + 1612558 * 2 ^ 59
def prefixEnd_1612558 : Nat := 4983230072969 + 3 ^ 40 * 1612558 * 2
def baseEnd_1612558 : Nat := 552011558168671395405991

theorem tailTrace_1612558 : CollatzResearch.WordTrace tailWord_1612558 prefixEnd_1612558 552011558168671395405991 := by
  unfold tailWord_1612558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351852761498155478194791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39209881394656829217038885 7351852761498155478194791)
  ·
    refine ⟨11027779142247233217292187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351852761498155478194791 11027779142247233217292187)
    ·
      refine ⟨16541668713370849825938281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11027779142247233217292187 16541668713370849825938281)
      ·
        refine ⟨12406251535028137369453711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16541668713370849825938281 12406251535028137369453711)
        ·
          refine ⟨18609377302542206054180567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406251535028137369453711 18609377302542206054180567)
          ·
            refine ⟨27914065953813309081270851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18609377302542206054180567 27914065953813309081270851)
            ·
              refine ⟨41871098930719963621906277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27914065953813309081270851 41871098930719963621906277)
              ·
                refine ⟨7850831049509993179107427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41871098930719963621906277 7850831049509993179107427)
                ·
                  refine ⟨11776246574264989768661141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850831049509993179107427 11776246574264989768661141)
                  ·
                    refine ⟨552011558168671395405991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11776246574264989768661141 552011558168671395405991)
                    ·
                      rfl

theorem cell22_1612558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1612558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612558 prefixEnd_1612558 := by exact prefixLift 1612558
  have htrace : WordTrace (prefixWord ++ tailWord_1612558) baseStart_1612558 baseEnd_1612558 := by
    simpa [prefixWord, tailWord_1612558, baseEnd_1612558] using wordTrace_append hprefix tailTrace_1612558
  have hstable : (prefixWord ++ tailWord_1612558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612558).length < 2 ^ (prefixWord ++ tailWord_1612558).sum := by decide
  have hdescent : baseEnd_1612558 < baseStart_1612558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612562 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1612562 : Nat := 118140960795 + 1612562 * 2 ^ 59
def prefixEnd_1612562 : Nat := 4983230072969 + 3 ^ 40 * 1612562 * 2
def baseEnd_1612562 : Nat := 184004309150138906101993

theorem tailTrace_1612562 : CollatzResearch.WordTrace tailWord_1612562 prefixEnd_1612562 184004309150138906101993 := by
  unfold tailWord_1612562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703741995992688127175985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39209978655980501672469293 14703741995992688127175985)
  ·
    refine ⟨11027806496994516095381989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14703741995992688127175985 11027806496994516095381989)
    ·
      refine ⟨2067713718186471767884123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11027806496994516095381989 2067713718186471767884123)
      ·
        refine ⟨3101570577279707651826185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067713718186471767884123 3101570577279707651826185)
        ·
          refine ⟨2326177932959780738869639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3101570577279707651826185 2326177932959780738869639)
          ·
            refine ⟨3489266899439671108304459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326177932959780738869639 3489266899439671108304459)
            ·
              refine ⟨5233900349159506662456689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489266899439671108304459 5233900349159506662456689)
              ·
                refine ⟨3925425261869629996842517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233900349159506662456689 3925425261869629996842517)
                ·
                  refine ⟨184004309150138906101993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3925425261869629996842517 184004309150138906101993)
                  ·
                    rfl

theorem cell22_1612562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1612562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612562 prefixEnd_1612562 := by exact prefixLift 1612562
  have htrace : WordTrace (prefixWord ++ tailWord_1612562) baseStart_1612562 baseEnd_1612562 := by
    simpa [prefixWord, tailWord_1612562, baseEnd_1612562] using wordTrace_append hprefix tailTrace_1612562
  have hstable : (prefixWord ++ tailWord_1612562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612562).length < 2 ^ (prefixWord ++ tailWord_1612562).sum := by decide
  have hdescent : baseEnd_1612562 < baseStart_1612562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612575 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 2, 4]
def baseStart_1612575 : Nat := 118140960795 + 1612575 * 2 ^ 59
def prefixEnd_1612575 : Nat := 4983230072969 + 3 ^ 40 * 1612575 * 2
def baseEnd_1612575 : Nat := 552017377616089017730939

theorem tailTrace_1612575 : CollatzResearch.WordTrace tailWord_1612575 prefixEnd_1612575 552017377616089017730939 := by
  unfold tailWord_1612575
  simp only [CollatzResearch.WordTrace]
  refine ⟨58815442132923655728927179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39210294755282437152618119 58815442132923655728927179)
  ·
    refine ⟨88223163199385483593390769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58815442132923655728927179 88223163199385483593390769)
    ·
      refine ⟨66167372399539112695043077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88223163199385483593390769 66167372399539112695043077)
      ·
        refine ⟨12406382324913583630320577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66167372399539112695043077 12406382324913583630320577)
        ·
          refine ⟨9304786743685187722740433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12406382324913583630320577 9304786743685187722740433)
          ·
            refine ⟨6978590057763890792055325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9304786743685187722740433 6978590057763890792055325)
            ·
              refine ⟨2616971271661459047020747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6978590057763890792055325 2616971271661459047020747)
              ·
                refine ⟨3925456907492188570531121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616971271661459047020747 3925456907492188570531121)
                ·
                  refine ⟨2944092680619141427898341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3925456907492188570531121 2944092680619141427898341)
                  ·
                    refine ⟨552017377616089017730939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944092680619141427898341 552017377616089017730939)
                    ·
                      rfl

theorem cell22_1612575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_1612575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612575 prefixEnd_1612575 := by exact prefixLift 1612575
  have htrace : WordTrace (prefixWord ++ tailWord_1612575) baseStart_1612575 baseEnd_1612575 := by
    simpa [prefixWord, tailWord_1612575, baseEnd_1612575] using wordTrace_append hprefix tailTrace_1612575
  have hstable : (prefixWord ++ tailWord_1612575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612575).length < 2 ^ (prefixWord ++ tailWord_1612575).sum := by decide
  have hdescent : baseEnd_1612575 < baseStart_1612575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612590 : List Nat := [4, 1, 3, 2, 1, 2, 9]
def baseStart_1612590 : Nat := 118140960795 + 1612590 * 2 ^ 59
def prefixEnd_1612590 : Nat := 4983230072969 + 3 ^ 40 * 1612590 * 2
def baseEnd_1612590 : Nat := 20445278237875332540959

theorem tailTrace_1612590 : CollatzResearch.WordTrace tailWord_1612590 prefixEnd_1612590 20445278237875332540959 := by
  unfold tailWord_1612590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351998653483664161340403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39210659485246208860482149 7351998653483664161340403)
  ·
    refine ⟨11027997980225496242010605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351998653483664161340403 11027997980225496242010605)
    ·
      refine ⟨4135499242584561090753977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11027997980225496242010605 4135499242584561090753977)
      ·
        refine ⟨3101624431938420818065483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4135499242584561090753977 3101624431938420818065483)
        ·
          refine ⟨4652436647907631227098225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101624431938420818065483 4652436647907631227098225)
          ·
            refine ⟨3489327485930723420323669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652436647907631227098225 3489327485930723420323669)
            ·
              refine ⟨20445278237875332540959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3489327485930723420323669 20445278237875332540959)
              ·
                rfl

theorem cell22_1612590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 9].length) (baseStart_1612590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612590 prefixEnd_1612590 := by exact prefixLift 1612590
  have htrace : WordTrace (prefixWord ++ tailWord_1612590) baseStart_1612590 baseEnd_1612590 := by
    simpa [prefixWord, tailWord_1612590, baseEnd_1612590] using wordTrace_append hprefix tailTrace_1612590
  have hstable : (prefixWord ++ tailWord_1612590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612590).length < 2 ^ (prefixWord ++ tailWord_1612590).sum := by decide
  have hdescent : baseEnd_1612590 < baseStart_1612590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612682 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1612682 : Nat := 118140960795 + 1612682 * 2 ^ 59
def prefixEnd_1612682 : Nat := 4983230072969 + 3 ^ 40 * 1612682 * 2
def baseEnd_1612682 : Nat := 552054005902776405305611

theorem tailTrace_1612682 : CollatzResearch.WordTrace tailWord_1612682 prefixEnd_1612682 552054005902776405305611 := by
  unfold tailWord_1612682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704836185884003250768075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39212896495690675335381533 14704836185884003250768075)
  ·
    refine ⟨22057254278826004876152113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14704836185884003250768075 22057254278826004876152113)
    ·
      refine ⟨16542940709119503657114085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22057254278826004876152113 16542940709119503657114085)
      ·
        refine ⟨3101801382959906935708891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16542940709119503657114085 3101801382959906935708891)
        ·
          refine ⟨4652702074439860403563337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101801382959906935708891 4652702074439860403563337)
          ·
            refine ⟨3489526555829895302672503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652702074439860403563337 3489526555829895302672503)
            ·
              refine ⟨5234289833744842954008755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489526555829895302672503 5234289833744842954008755)
              ·
                refine ⟨7851434750617264431013133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234289833744842954008755 7851434750617264431013133)
                ·
                  refine ⟨2944288031481474161629925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7851434750617264431013133 2944288031481474161629925)
                  ·
                    refine ⟨552054005902776405305611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944288031481474161629925 552054005902776405305611)
                    ·
                      rfl

theorem cell22_1612682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1612682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612682 prefixEnd_1612682 := by exact prefixLift 1612682
  have htrace : WordTrace (prefixWord ++ tailWord_1612682) baseStart_1612682 baseEnd_1612682 := by
    simpa [prefixWord, tailWord_1612682, baseEnd_1612682] using wordTrace_append hprefix tailTrace_1612682
  have hstable : (prefixWord ++ tailWord_1612682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612682).length < 2 ^ (prefixWord ++ tailWord_1612682).sum := by decide
  have hdescent : baseEnd_1612682 < baseStart_1612682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612695 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1612695 : Nat := 118140960795 + 1612695 * 2 ^ 59
def prefixEnd_1612695 : Nat := 4983230072969 + 3 ^ 40 * 1612695 * 2
def baseEnd_1612695 : Nat := 552058456068448704730571

theorem tailTrace_1612695 : CollatzResearch.WordTrace tailWord_1612695 prefixEnd_1612695 552058456068448704730571 := by
  unfold tailWord_1612695
  simp only [CollatzResearch.WordTrace]
  refine ⟨58819818892488916223295539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39213212594992610815530359 58819818892488916223295539)
  ·
    refine ⟨88229728338733374334943309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58819818892488916223295539 88229728338733374334943309)
    ·
      refine ⟨33086148127025015375603741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88229728338733374334943309 33086148127025015375603741)
      ·
        refine ⟨12407305547634380765851403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33086148127025015375603741 12407305547634380765851403)
        ·
          refine ⟨18610958321451571148777105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12407305547634380765851403 18610958321451571148777105)
          ·
            refine ⟨13958218741088678361582829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18610958321451571148777105 13958218741088678361582829)
            ·
              refine ⟨5234332027908254385593561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13958218741088678361582829 5234332027908254385593561)
              ·
                refine ⟨3925749020931190789195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234332027908254385593561 3925749020931190789195171)
                ·
                  refine ⟨5888623531396786183792757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925749020931190789195171 5888623531396786183792757)
                  ·
                    refine ⟨552058456068448704730571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5888623531396786183792757 552058456068448704730571)
                    ·
                      rfl

theorem cell22_1612695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1612695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612695 prefixEnd_1612695 := by exact prefixLift 1612695
  have htrace : WordTrace (prefixWord ++ tailWord_1612695) baseStart_1612695 baseEnd_1612695 := by
    simpa [prefixWord, tailWord_1612695, baseEnd_1612695] using wordTrace_append hprefix tailTrace_1612695
  have hstable : (prefixWord ++ tailWord_1612695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612695).length < 2 ^ (prefixWord ++ tailWord_1612695).sum := by decide
  have hdescent : baseEnd_1612695 < baseStart_1612695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612744 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_1612744 : Nat := 118140960795 + 1612744 * 2 ^ 59
def prefixEnd_1612744 : Nat := 4983230072969 + 3 ^ 40 * 1612744 * 2
def baseEnd_1612744 : Nat := 552075229769828910255421

theorem tailTrace_1612744 : CollatzResearch.WordTrace tailWord_1612744 prefixEnd_1612744 552075229769828910255421 := by
  unfold tailWord_1612744
  simp only [CollatzResearch.WordTrace]
  refine ⟨29410803034655698795914643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39214404046207598394552857 29410803034655698795914643)
  ·
    refine ⟨44116204551983548193871965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29410803034655698795914643 44116204551983548193871965)
    ·
      refine ⟨16543576706993830572701987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44116204551983548193871965 16543576706993830572701987)
      ·
        refine ⟨24815365060490745859052981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16543576706993830572701987 24815365060490745859052981)
        ·
          refine ⟨2326440474421007424286217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24815365060490745859052981 2326440474421007424286217)
          ·
            refine ⟨1744830355815755568214663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326440474421007424286217 1744830355815755568214663)
            ·
              refine ⟨2617245533723633352321995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744830355815755568214663 2617245533723633352321995)
              ·
                refine ⟨3925868300585450028482993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617245533723633352321995 3925868300585450028482993)
                ·
                  refine ⟨2944401225439087521362245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3925868300585450028482993 2944401225439087521362245)
                  ·
                    refine ⟨552075229769828910255421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944401225439087521362245 552075229769828910255421)
                    ·
                      rfl

theorem cell22_1612744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_1612744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612744 prefixEnd_1612744 := by exact prefixLift 1612744
  have htrace : WordTrace (prefixWord ++ tailWord_1612744) baseStart_1612744 baseEnd_1612744 := by
    simpa [prefixWord, tailWord_1612744, baseEnd_1612744] using wordTrace_append hprefix tailTrace_1612744
  have hstable : (prefixWord ++ tailWord_1612744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612744).length < 2 ^ (prefixWord ++ tailWord_1612744).sum := by decide
  have hdescent : baseEnd_1612744 < baseStart_1612744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_1612800 : Nat := 118140960795 + 1612800 * 2 ^ 59
def prefixEnd_1612800 : Nat := 4983230072969 + 3 ^ 40 * 1612800 * 2
def baseEnd_1612800 : Nat := 552094399714263430855249

theorem tailTrace_1612800 : CollatzResearch.WordTrace tailWord_1612800 prefixEnd_1612800 552094399714263430855249 := by
  unfold tailWord_1612800
  simp only [CollatzResearch.WordTrace]
  refine ⟨29411824278554259577933927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39215765704739012770578569 29411824278554259577933927)
  ·
    refine ⟨44117736417831389366900891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29411824278554259577933927 44117736417831389366900891)
    ·
      refine ⟨66176604626747084050351337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44117736417831389366900891 66176604626747084050351337)
      ·
        refine ⟨49632453470060313037763503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66176604626747084050351337 49632453470060313037763503)
        ·
          refine ⟨74448680205090469556645255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49632453470060313037763503 74448680205090469556645255)
          ·
            refine ⟨111673020307635704334967883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74448680205090469556645255 111673020307635704334967883)
            ·
              refine ⟨167509530461453556502451825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111673020307635704334967883 167509530461453556502451825)
              ·
                refine ⟨125632147846090167376838869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167509530461453556502451825 125632147846090167376838869)
                ·
                  refine ⟨2944503465142738297894661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125632147846090167376838869 2944503465142738297894661)
                  ·
                    refine ⟨552094399714263430855249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944503465142738297894661 552094399714263430855249)
                    ·
                      rfl

theorem cell22_1612800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_1612800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612800 prefixEnd_1612800 := by exact prefixLift 1612800
  have htrace : WordTrace (prefixWord ++ tailWord_1612800) baseStart_1612800 baseEnd_1612800 := by
    simpa [prefixWord, tailWord_1612800, baseEnd_1612800] using wordTrace_append hprefix tailTrace_1612800
  have hstable : (prefixWord ++ tailWord_1612800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612800).length < 2 ^ (prefixWord ++ tailWord_1612800).sum := by decide
  have hdescent : baseEnd_1612800 < baseStart_1612800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612877 : List Nat := [1, 6, 1, 1, 1, 12]
def baseStart_1612877 : Nat := 118140960795 + 1612877 * 2 ^ 59
def prefixEnd_1612877 : Nat := 4983230072969 + 3 ^ 40 * 1612877 * 2
def baseEnd_1612877 : Nat := 6816305659109393786173

theorem tailTrace_1612877 : CollatzResearch.WordTrace tailWord_1612877 prefixEnd_1612877 6816305659109393786173 := by
  unfold tailWord_1612877
  simp only [CollatzResearch.WordTrace]
  refine ⟨58826456977829561306420885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39217637985219707537613923 58826456977829561306420885)
  ·
    refine ⟨2757490170835760686238479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58826456977829561306420885 2757490170835760686238479)
    ·
      refine ⟨4136235256253641029357719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757490170835760686238479 4136235256253641029357719)
      ·
        refine ⟨6204352884380461544036579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136235256253641029357719 6204352884380461544036579)
        ·
          refine ⟨9306529326570692316054869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204352884380461544036579 9306529326570692316054869)
          ·
            refine ⟨6816305659109393786173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9306529326570692316054869 6816305659109393786173)
            ·
              rfl

theorem cell22_1612877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 12].length) (baseStart_1612877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612877 prefixEnd_1612877 := by exact prefixLift 1612877
  have htrace : WordTrace (prefixWord ++ tailWord_1612877) baseStart_1612877 baseEnd_1612877 := by
    simpa [prefixWord, tailWord_1612877, baseEnd_1612877] using wordTrace_append hprefix tailTrace_1612877
  have hstable : (prefixWord ++ tailWord_1612877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612877).length < 2 ^ (prefixWord ++ tailWord_1612877).sum := by decide
  have hdescent : baseEnd_1612877 < baseStart_1612877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612909 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1612909 : Nat := 118140960795 + 1612909 * 2 ^ 59
def prefixEnd_1612909 : Nat := 4983230072969 + 3 ^ 40 * 1612909 * 2
def baseEnd_1612909 : Nat := 552131712641823479879915

theorem tailTrace_1612909 : CollatzResearch.WordTrace tailWord_1612909 prefixEnd_1612909 552131712641823479879915 := by
  unfold tailWord_1612909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58827624113713630771585781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39218416075809087181057187 58827624113713630771585781)
  ·
    refine ⟨5515089760660652884836167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58827624113713630771585781 5515089760660652884836167)
    ·
      refine ⟨8272634640990979327254251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515089760660652884836167 8272634640990979327254251)
      ·
        refine ⟨12408951961486468990881377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272634640990979327254251 12408951961486468990881377)
        ·
          refine ⟨9306713971114851743161033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12408951961486468990881377 9306713971114851743161033)
          ·
            refine ⟨6980035478336138807370775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306713971114851743161033 6980035478336138807370775)
            ·
              refine ⟨10470053217504208211056163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980035478336138807370775 10470053217504208211056163)
              ·
                refine ⟨15705079826256312316584245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470053217504208211056163 15705079826256312316584245)
                ·
                  refine ⟨1472351233711529279679773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15705079826256312316584245 1472351233711529279679773)
                  ·
                    refine ⟨552131712641823479879915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472351233711529279679773 552131712641823479879915)
                    ·
                      rfl

theorem cell22_1612909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1612909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612909 prefixEnd_1612909 := by exact prefixLift 1612909
  have htrace : WordTrace (prefixWord ++ tailWord_1612909) baseStart_1612909 baseEnd_1612909 := by
    simpa [prefixWord, tailWord_1612909, baseEnd_1612909] using wordTrace_append hprefix tailTrace_1612909
  have hstable : (prefixWord ++ tailWord_1612909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612909).length < 2 ^ (prefixWord ++ tailWord_1612909).sum := by decide
  have hdescent : baseEnd_1612909 < baseStart_1612909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612937 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_1612937 : Nat := 118140960795 + 1612937 * 2 ^ 59
def prefixEnd_1612937 : Nat := 4983230072969 + 3 ^ 40 * 1612937 * 2
def baseEnd_1612937 : Nat := 552141297614040740179829

theorem tailTrace_1612937 : CollatzResearch.WordTrace tailWord_1612937 prefixEnd_1612937 552141297614040740179829 := by
  unfold tailWord_1612937
  simp only [CollatzResearch.WordTrace]
  refine ⟨58828645357612191553605065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39219096905074794369070043 58828645357612191553605065)
  ·
    refine ⟨44121484018209143665203799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58828645357612191553605065 44121484018209143665203799)
    ·
      refine ⟨66182226027313715497805699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44121484018209143665203799 66182226027313715497805699)
      ·
        refine ⟨99273339040970573246708549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66182226027313715497805699 99273339040970573246708549)
        ·
          refine ⟨18613751070181982483757853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99273339040970573246708549 18613751070181982483757853)
          ·
            refine ⟨6980156651318243431409195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18613751070181982483757853 6980156651318243431409195)
            ·
              refine ⟨10470234976977365147113793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980156651318243431409195 10470234976977365147113793)
              ·
                refine ⟨7852676232733023860335345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10470234976977365147113793 7852676232733023860335345)
                ·
                  refine ⟨5889507174549767895251509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852676232733023860335345 5889507174549767895251509)
                  ·
                    refine ⟨552141297614040740179829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5889507174549767895251509 552141297614040740179829)
                    ·
                      rfl

theorem cell22_1612937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_1612937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612937 prefixEnd_1612937 := by exact prefixLift 1612937
  have htrace : WordTrace (prefixWord ++ tailWord_1612937) baseStart_1612937 baseEnd_1612937 := by
    simpa [prefixWord, tailWord_1612937, baseEnd_1612937] using wordTrace_append hprefix tailTrace_1612937
  have hstable : (prefixWord ++ tailWord_1612937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612937).length < 2 ^ (prefixWord ++ tailWord_1612937).sum := by decide
  have hdescent : baseEnd_1612937 < baseStart_1612937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612954 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1612954 : Nat := 118140960795 + 1612954 * 2 ^ 59
def prefixEnd_1612954 : Nat := 4983230072969 + 3 ^ 40 * 1612954 * 2
def baseEnd_1612954 : Nat := 552147117061458362504777

theorem tailTrace_1612954 : CollatzResearch.WordTrace tailWord_1612954 prefixEnd_1612954 552147117061458362504777 := by
  unfold tailWord_1612954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707316349637650864243479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39219510265700402304649277 14707316349637650864243479)
  ·
    refine ⟨22060974524456476296365219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14707316349637650864243479 22060974524456476296365219)
    ·
      refine ⟨33091461786684714444547829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22060974524456476296365219 33091461786684714444547829)
      ·
        refine ⟨3102324542501691979176359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33091461786684714444547829 3102324542501691979176359)
        ·
          refine ⟨4653486813752537968764539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102324542501691979176359 4653486813752537968764539)
          ·
            refine ⟨6980230220628806953146809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653486813752537968764539 6980230220628806953146809)
            ·
              refine ⟨5235172665471605214860107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980230220628806953146809 5235172665471605214860107)
              ·
                refine ⟨7852758998207407822290161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235172665471605214860107 7852758998207407822290161)
                ·
                  refine ⟨5889569248655555866717621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852758998207407822290161 5889569248655555866717621)
                  ·
                    refine ⟨552147117061458362504777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5889569248655555866717621 552147117061458362504777)
                    ·
                      rfl

theorem cell22_1612954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1612954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612954 prefixEnd_1612954 := by exact prefixLift 1612954
  have htrace : WordTrace (prefixWord ++ tailWord_1612954) baseStart_1612954 baseEnd_1612954 := by
    simpa [prefixWord, tailWord_1612954, baseEnd_1612954] using wordTrace_append hprefix tailTrace_1612954
  have hstable : (prefixWord ++ tailWord_1612954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612954).length < 2 ^ (prefixWord ++ tailWord_1612954).sum := by decide
  have hdescent : baseEnd_1612954 < baseStart_1612954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612956 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_1612956 : Nat := 118140960795 + 1612956 * 2 ^ 59
def prefixEnd_1612956 : Nat := 4983230072969 + 3 ^ 40 * 1612956 * 2
def baseEnd_1612956 : Nat := 184049267234110341318257

theorem tailTrace_1612956 : CollatzResearch.WordTrace tailWord_1612956 prefixEnd_1612956 184049267234110341318257 := by
  unfold tailWord_1612956
  simp only [CollatzResearch.WordTrace]
  refine ⟨29414669172271678899273361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39219558896362238532364481 29414669172271678899273361)
  ·
    refine ⟨22061001879203759174455021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29414669172271678899273361 22061001879203759174455021)
    ·
      refine ⟨8272875704701409690420633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22061001879203759174455021 8272875704701409690420633)
      ·
        refine ⟨6204656778526057267815475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8272875704701409690420633 6204656778526057267815475)
        ·
          refine ⟨9306985167789085901723213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204656778526057267815475 9306985167789085901723213)
          ·
            refine ⟨3490119437920907213146205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9306985167789085901723213 3490119437920907213146205)
            ·
              refine ⟨1308794789220340204929827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3490119437920907213146205 1308794789220340204929827)
              ·
                refine ⟨1963192183830510307394741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308794789220340204929827 1963192183830510307394741)
                ·
                  refine ⟨184049267234110341318257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1963192183830510307394741 184049267234110341318257)
                  ·
                    rfl

theorem cell22_1612956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_1612956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612956 prefixEnd_1612956 := by exact prefixLift 1612956
  have htrace : WordTrace (prefixWord ++ tailWord_1612956) baseStart_1612956 baseEnd_1612956 := by
    simpa [prefixWord, tailWord_1612956, baseEnd_1612956] using wordTrace_append hprefix tailTrace_1612956
  have hstable : (prefixWord ++ tailWord_1612956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612956).length < 2 ^ (prefixWord ++ tailWord_1612956).sum := by decide
  have hdescent : baseEnd_1612956 < baseStart_1612956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612984 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_1612984 : Nat := 118140960795 + 1612984 * 2 ^ 59
def prefixEnd_1612984 : Nat := 4983230072969 + 3 ^ 40 * 1612984 * 2
def baseEnd_1612984 : Nat := 184052462224849428084895

theorem tailTrace_1612984 : CollatzResearch.WordTrace tailWord_1612984 prefixEnd_1612984 184052462224849428084895 := by
  unfold tailWord_1612984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29415179794220959290283003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39220239725627945720377337 29415179794220959290283003)
  ·
    refine ⟨44122769691331438935424505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29415179794220959290283003 44122769691331438935424505)
    ·
      refine ⟨33092077268498579201568379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44122769691331438935424505 33092077268498579201568379)
      ·
        refine ⟨49638115902747868802352569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33092077268498579201568379 49638115902747868802352569)
        ·
          refine ⟨37228586927060901601764427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49638115902747868802352569 37228586927060901601764427)
          ·
            refine ⟨55842880390591352402646641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37228586927060901601764427 55842880390591352402646641)
            ·
              refine ⟨41882160292943514301984981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55842880390591352402646641 41882160292943514301984981)
              ·
                refine ⟨981613131865863616452773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41882160292943514301984981 981613131865863616452773)
                ·
                  refine ⟨184052462224849428084895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981613131865863616452773 184052462224849428084895)
                  ·
                    rfl

theorem cell22_1612984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_1612984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612984 prefixEnd_1612984 := by exact prefixLift 1612984
  have htrace : WordTrace (prefixWord ++ tailWord_1612984) baseStart_1612984 baseEnd_1612984 := by
    simpa [prefixWord, tailWord_1612984, baseEnd_1612984] using wordTrace_append hprefix tailTrace_1612984
  have hstable : (prefixWord ++ tailWord_1612984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612984).length < 2 ^ (prefixWord ++ tailWord_1612984).sum := by decide
  have hdescent : baseEnd_1612984 < baseStart_1612984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612994 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1612994 : Nat := 118140960795 + 1612994 * 2 ^ 59
def prefixEnd_1612994 : Nat := 4983230072969 + 3 ^ 40 * 1612994 * 2
def baseEnd_1612994 : Nat := 552160809878911591504655

theorem tailTrace_1612994 : CollatzResearch.WordTrace tailWord_1612994 prefixEnd_1612994 552160809878911591504655 := by
  unfold tailWord_1612994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707681079601422572107509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39220482878937126858953357 14707681079601422572107509)
  ·
    refine ⟨1378845101212633366135079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14707681079601422572107509 1378845101212633366135079)
    ·
      refine ⟨2068267651818950049202619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378845101212633366135079 2068267651818950049202619)
      ·
        refine ⟨3102401477728425073803929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068267651818950049202619 3102401477728425073803929)
        ·
          refine ⟨2326801108296318805352947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102401477728425073803929 2326801108296318805352947)
          ·
            refine ⟨3490201662444478208029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326801108296318805352947 3490201662444478208029421)
            ·
              refine ⟨1308825623416679328011033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3490201662444478208029421 1308825623416679328011033)
              ·
                refine ⟨981619217562509496008275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308825623416679328011033 981619217562509496008275)
                ·
                  refine ⟨1472428826343764244012413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981619217562509496008275 1472428826343764244012413)
                  ·
                    refine ⟨552160809878911591504655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472428826343764244012413 552160809878911591504655)
                    ·
                      rfl

theorem cell22_1612994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1612994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1612994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1612994 prefixEnd_1612994 := by exact prefixLift 1612994
  have htrace : WordTrace (prefixWord ++ tailWord_1612994) baseStart_1612994 baseEnd_1612994 := by
    simpa [prefixWord, tailWord_1612994, baseEnd_1612994] using wordTrace_append hprefix tailTrace_1612994
  have hstable : (prefixWord ++ tailWord_1612994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612994).length < 2 ^ (prefixWord ++ tailWord_1612994).sum := by decide
  have hdescent : baseEnd_1612994 < baseStart_1612994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613119 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 6]
def baseStart_1613119 : Nat := 118140960795 + 1613119 * 2 ^ 59
def prefixEnd_1613119 : Nat := 4983230072969 + 3 ^ 40 * 1613119 * 2
def baseEnd_1613119 : Nat := 184067866644484310709757

theorem tailTrace_1613119 : CollatzResearch.WordTrace tailWord_1613119 prefixEnd_1613119 184067866644484310709757 := by
  unfold tailWord_1613119
  simp only [CollatzResearch.WordTrace]
  refine ⟨58835283442952836636730411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39223522295301891091153607 58835283442952836636730411)
  ·
    refine ⟨88252925164429254955095617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58835283442952836636730411 88252925164429254955095617)
    ·
      refine ⟨66189693873321941216321713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88252925164429254955095617 66189693873321941216321713)
      ·
        refine ⟨49642270404991455912241285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66189693873321941216321713 49642270404991455912241285)
        ·
          refine ⟨9307925700935897983545241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49642270404991455912241285 9307925700935897983545241)
          ·
            refine ⟨6980944275701923487658931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307925700935897983545241 6980944275701923487658931)
            ·
              refine ⟨10471416413552885231488397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980944275701923487658931 10471416413552885231488397)
              ·
                refine ⟨3926781155082331961808149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10471416413552885231488397 3926781155082331961808149)
                ·
                  refine ⟨184067866644484310709757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3926781155082331961808149 184067866644484310709757)
                  ·
                    rfl

theorem cell22_1613119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_1613119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613119 prefixEnd_1613119 := by exact prefixLift 1613119
  have htrace : WordTrace (prefixWord ++ tailWord_1613119) baseStart_1613119 baseEnd_1613119 := by
    simpa [prefixWord, tailWord_1613119, baseEnd_1613119] using wordTrace_append hprefix tailTrace_1613119
  have hstable : (prefixWord ++ tailWord_1613119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613119).length < 2 ^ (prefixWord ++ tailWord_1613119).sum := by decide
  have hdescent : baseEnd_1613119 < baseStart_1613119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613164 : List Nat := [2, 2, 1, 1, 5, 1, 10]
def baseStart_1613164 : Nat := 118140960795 + 1613164 * 2 ^ 59
def prefixEnd_1613164 : Nat := 4983230072969 + 3 ^ 40 * 1613164 * 2
def baseEnd_1613164 : Nat := 20452555716781030176079

theorem tailTrace_1613164 : CollatzResearch.WordTrace tailWord_1613164 prefixEnd_1613164 20452555716781030176079 := by
  unfold tailWord_1613164
  simp only [CollatzResearch.WordTrace]
  refine ⟨29418462363894904661059273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39224616485193206214745697 29418462363894904661059273)
  ·
    refine ⟨22063846772921178495794455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29418462363894904661059273 22063846772921178495794455)
    ·
      refine ⟨33095770159381767743691683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22063846772921178495794455 33095770159381767743691683)
      ·
        refine ⟨49643655239072651615537525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33095770159381767743691683 49643655239072651615537525)
        ·
          refine ⟨4654092678663061088956643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49643655239072651615537525 4654092678663061088956643)
          ·
            refine ⟨6981139017994591633434965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654092678663061088956643 6981139017994591633434965)
            ·
              refine ⟨20452555716781030176079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6981139017994591633434965 20452555716781030176079)
              ·
                rfl

theorem cell22_1613164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 10].length) (baseStart_1613164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613164 prefixEnd_1613164 := by exact prefixLift 1613164
  have htrace : WordTrace (prefixWord ++ tailWord_1613164) baseStart_1613164 baseEnd_1613164 := by
    simpa [prefixWord, tailWord_1613164, baseEnd_1613164] using wordTrace_append hprefix tailTrace_1613164
  have hstable : (prefixWord ++ tailWord_1613164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613164).length < 2 ^ (prefixWord ++ tailWord_1613164).sum := by decide
  have hdescent : baseEnd_1613164 < baseStart_1613164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613185 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1613185 : Nat := 118140960795 + 1613185 * 2 ^ 59
def prefixEnd_1613185 : Nat := 4983230072969 + 3 ^ 40 * 1613185 * 2
def baseEnd_1613185 : Nat := 552226193082250759979069

theorem tailTrace_1613185 : CollatzResearch.WordTrace tailWord_1613185 prefixEnd_1613185 552226193082250759979069 := by
  unfold tailWord_1613185
  simp only [CollatzResearch.WordTrace]
  refine ⟨58837690660713729908633009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39225127107142486605755339 58837690660713729908633009)
  ·
    refine ⟨44128267995535297431474757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58837690660713729908633009 44128267995535297431474757)
    ·
      refine ⟨8274050249162868268401517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44128267995535297431474757 8274050249162868268401517)
      ·
        refine ⟨3102768843436075600650569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8274050249162868268401517 3102768843436075600650569)
        ·
          refine ⟨2327076632577056700487927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102768843436075600650569 2327076632577056700487927)
          ·
            refine ⟨3490614948865585050731891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327076632577056700487927 3490614948865585050731891)
            ·
              refine ⟨5235922423298377576097837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490614948865585050731891 5235922423298377576097837)
              ·
                refine ⟨1963470908736891591036689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235922423298377576097837 1963470908736891591036689)
                ·
                  refine ⟨1472603181552668693277517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963470908736891591036689 1472603181552668693277517)
                  ·
                    refine ⟨552226193082250759979069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472603181552668693277517 552226193082250759979069)
                    ·
                      rfl

theorem cell22_1613185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1613185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613185 prefixEnd_1613185 := by exact prefixLift 1613185
  have htrace : WordTrace (prefixWord ++ tailWord_1613185) baseStart_1613185 baseEnd_1613185 := by
    simpa [prefixWord, tailWord_1613185, baseEnd_1613185] using wordTrace_append hprefix tailTrace_1613185
  have hstable : (prefixWord ++ tailWord_1613185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613185).length < 2 ^ (prefixWord ++ tailWord_1613185).sum := by decide
  have hdescent : baseEnd_1613185 < baseStart_1613185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613196 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1613196 : Nat := 118140960795 + 1613196 * 2 ^ 59
def prefixEnd_1613196 : Nat := 4983230072969 + 3 ^ 40 * 1613196 * 2
def baseEnd_1613196 : Nat := 552229958607050397954035

theorem tailTrace_1613196 : CollatzResearch.WordTrace tailWord_1613196 prefixEnd_1613196 552229958607050397954035 := by
  unfold tailWord_1613196
  simp only [CollatzResearch.WordTrace]
  refine ⟨29419045931836939393641721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39225394575782585858188961 29419045931836939393641721)
  ·
    refine ⟨22064284448877704545231291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29419045931836939393641721 22064284448877704545231291)
    ·
      refine ⟨33096426673316556817846937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22064284448877704545231291 33096426673316556817846937)
      ·
        refine ⟨24822320004987417613385203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33096426673316556817846937 24822320004987417613385203)
        ·
          refine ⟨37233480007481126420077805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24822320004987417613385203 37233480007481126420077805)
          ·
            refine ⟨13962555002805422407529177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37233480007481126420077805 13962555002805422407529177)
            ·
              refine ⟨10471916252104066805646883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13962555002805422407529177 10471916252104066805646883)
              ·
                refine ⟨15707874378156100208470325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471916252104066805646883 15707874378156100208470325)
                ·
                  refine ⟨1472613222952134394544093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15707874378156100208470325 1472613222952134394544093)
                  ·
                    refine ⟨552229958607050397954035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472613222952134394544093 552229958607050397954035)
                    ·
                      rfl

theorem cell22_1613196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1613196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613196 prefixEnd_1613196 := by exact prefixLift 1613196
  have htrace : WordTrace (prefixWord ++ tailWord_1613196) baseStart_1613196 baseEnd_1613196 := by
    simpa [prefixWord, tailWord_1613196, baseEnd_1613196] using wordTrace_append hprefix tailTrace_1613196
  have hstable : (prefixWord ++ tailWord_1613196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613196).length < 2 ^ (prefixWord ++ tailWord_1613196).sum := by decide
  have hdescent : baseEnd_1613196 < baseStart_1613196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613256 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_1613256 : Nat := 118140960795 + 1613256 * 2 ^ 59
def prefixEnd_1613256 : Nat := 4983230072969 + 3 ^ 40 * 1613256 * 2
def baseEnd_1613256 : Nat := 552250497833230241453851

theorem tailTrace_1613256 : CollatzResearch.WordTrace tailWord_1613256 prefixEnd_1613256 552250497833230241453851 := by
  unfold tailWord_1613256
  simp only [CollatzResearch.WordTrace]
  refine ⟨29420140121728254517233811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39226853495637672689645081 29420140121728254517233811)
  ·
    refine ⟨44130210182592381775850717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29420140121728254517233811 44130210182592381775850717)
    ·
      refine ⟨16548828818472143165944019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44130210182592381775850717 16548828818472143165944019)
      ·
        refine ⟨24823243227708214748916029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16548828818472143165944019 24823243227708214748916029)
        ·
          refine ⟨9308716210390580530843511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24823243227708214748916029 9308716210390580530843511)
          ·
            refine ⟨13963074315585870796265267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9308716210390580530843511 13963074315585870796265267)
            ·
              refine ⟨20944611473378806194397901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13963074315585870796265267 20944611473378806194397901)
              ·
                refine ⟨7854229302517052322899213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20944611473378806194397901 7854229302517052322899213)
                ·
                  refine ⟨2945335988443894621087205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7854229302517052322899213 2945335988443894621087205)
                  ·
                    refine ⟨552250497833230241453851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2945335988443894621087205 552250497833230241453851)
                    ·
                      rfl

theorem cell22_1613256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_1613256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613256 prefixEnd_1613256 := by exact prefixLift 1613256
  have htrace : WordTrace (prefixWord ++ tailWord_1613256) baseStart_1613256 baseEnd_1613256 := by
    simpa [prefixWord, tailWord_1613256, baseEnd_1613256] using wordTrace_append hprefix tailTrace_1613256
  have hstable : (prefixWord ++ tailWord_1613256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613256).length < 2 ^ (prefixWord ++ tailWord_1613256).sum := by decide
  have hdescent : baseEnd_1613256 < baseStart_1613256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613273 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_1613273 : Nat := 118140960795 + 1613273 * 2 ^ 59
def prefixEnd_1613273 : Nat := 4983230072969 + 3 ^ 40 * 1613273 * 2
def baseEnd_1613273 : Nat := 552256317280647863778799

theorem tailTrace_1613273 : CollatzResearch.WordTrace tailWord_1613273 prefixEnd_1613273 552256317280647863778799 := by
  unfold tailWord_1613273
  simp only [CollatzResearch.WordTrace]
  refine ⟨58840900284394920937836473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39227266856263280625224315 58840900284394920937836473)
  ·
    refine ⟨44130675213296190703377355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58840900284394920937836473 44130675213296190703377355)
    ·
      refine ⟨66196012819944286055066033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44130675213296190703377355 66196012819944286055066033)
      ·
        refine ⟨49647009614958214541299525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66196012819944286055066033 49647009614958214541299525)
        ·
          refine ⟨9308814302804665226493661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49647009614958214541299525 9308814302804665226493661)
          ·
            refine ⟨3490805363551749459935123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9308814302804665226493661 3490805363551749459935123)
            ·
              refine ⟨5236208045327624189902685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490805363551749459935123 5236208045327624189902685)
              ·
                refine ⟨1963578016997859071213507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5236208045327624189902685 1963578016997859071213507)
                ·
                  refine ⟨2945367025496788606820261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963578016997859071213507 2945367025496788606820261)
                  ·
                    refine ⟨552256317280647863778799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2945367025496788606820261 552256317280647863778799)
                    ·
                      rfl

theorem cell22_1613273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_1613273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613273 prefixEnd_1613273 := by exact prefixLift 1613273
  have htrace : WordTrace (prefixWord ++ tailWord_1613273) baseStart_1613273 baseEnd_1613273 := by
    simpa [prefixWord, tailWord_1613273, baseEnd_1613273] using wordTrace_append hprefix tailTrace_1613273
  have hstable : (prefixWord ++ tailWord_1613273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613273).length < 2 ^ (prefixWord ++ tailWord_1613273).sum := by decide
  have hdescent : baseEnd_1613273 < baseStart_1613273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613288 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_1613288 : Nat := 118140960795 + 1613288 * 2 ^ 59
def prefixEnd_1613288 : Nat := 4983230072969 + 3 ^ 40 * 1613288 * 2
def baseEnd_1613288 : Nat := 184087150695730941551251

theorem tailTrace_1613288 : CollatzResearch.WordTrace tailWord_1613288 prefixEnd_1613288 184087150695730941551251 := by
  unfold tailWord_1613288
  simp only [CollatzResearch.WordTrace]
  refine ⟨29420723689670289249816259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39227631586227052333088345 29420723689670289249816259)
  ·
    refine ⟨44131085534505433874724389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29420723689670289249816259 44131085534505433874724389)
    ·
      refine ⟨8274578537719768851510823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44131085534505433874724389 8274578537719768851510823)
      ·
        refine ⟨12411867806579653277266235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274578537719768851510823 12411867806579653277266235)
        ·
          refine ⟨18617801709869479915899353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12411867806579653277266235 18617801709869479915899353)
          ·
            refine ⟨13963351282402109936924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18617801709869479915899353 13963351282402109936924515)
            ·
              refine ⟨20945026923603164905386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13963351282402109936924515 20945026923603164905386773)
              ·
                refine ⟨981798137043898354940005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20945026923603164905386773 981798137043898354940005)
                ·
                  refine ⟨184087150695730941551251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981798137043898354940005 184087150695730941551251)
                  ·
                    rfl

theorem cell22_1613288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_1613288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613288 prefixEnd_1613288 := by exact prefixLift 1613288
  have htrace : WordTrace (prefixWord ++ tailWord_1613288) baseStart_1613288 baseEnd_1613288 := by
    simpa [prefixWord, tailWord_1613288, baseEnd_1613288] using wordTrace_append hprefix tailTrace_1613288
  have hstable : (prefixWord ++ tailWord_1613288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613288).length < 2 ^ (prefixWord ++ tailWord_1613288).sum := by decide
  have hdescent : baseEnd_1613288 < baseStart_1613288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613376 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_1613376 : Nat := 118140960795 + 1613376 * 2 ^ 59
def prefixEnd_1613376 : Nat := 4983230072969 + 3 ^ 40 * 1613376 * 2
def baseEnd_1613376 : Nat := 552291576285589928453483

theorem tailTrace_1613376 : CollatzResearch.WordTrace tailWord_1613376 prefixEnd_1613376 552291576285589928453483 := by
  unfold tailWord_1613376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29422328501510884764417991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39229771335347846352557321 29422328501510884764417991)
  ·
    refine ⟨44133492752266327146626987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29422328501510884764417991 44133492752266327146626987)
    ·
      refine ⟨66200239128399490719940481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44133492752266327146626987 66200239128399490719940481)
      ·
        refine ⟨49650179346299618039955361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66200239128399490719940481 49650179346299618039955361)
        ·
          refine ⟨37237634509724713529966521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49650179346299618039955361 37237634509724713529966521)
          ·
            refine ⟨27928225882293535147474891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37237634509724713529966521 27928225882293535147474891)
            ·
              refine ⟨41892338823440302721212337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27928225882293535147474891 41892338823440302721212337)
              ·
                refine ⟨31419254117580227040909253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41892338823440302721212337 31419254117580227040909253)
                ·
                  refine ⟨5891110147046292570170485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31419254117580227040909253 5891110147046292570170485)
                  ·
                    refine ⟨552291576285589928453483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5891110147046292570170485 552291576285589928453483)
                    ·
                      rfl

theorem cell22_1613376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_1613376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613376 prefixEnd_1613376 := by exact prefixLift 1613376
  have htrace : WordTrace (prefixWord ++ tailWord_1613376) baseStart_1613376 baseEnd_1613376 := by
    simpa [prefixWord, tailWord_1613376, baseEnd_1613376] using wordTrace_append hprefix tailTrace_1613376
  have hstable : (prefixWord ++ tailWord_1613376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613376).length < 2 ^ (prefixWord ++ tailWord_1613376).sum := by decide
  have hdescent : baseEnd_1613376 < baseStart_1613376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613399 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 1, 3]
def baseStart_1613399 : Nat := 118140960795 + 1613399 * 2 ^ 59
def prefixEnd_1613399 : Nat := 4983230072969 + 3 ^ 40 * 1613399 * 2
def baseEnd_1613399 : Nat := 552299449655625535128413

theorem tailTrace_1613399 : CollatzResearch.WordTrace tailWord_1613399 prefixEnd_1613399 552299449655625535128413 := by
  unfold tailWord_1613399
  simp only [CollatzResearch.WordTrace]
  refine ⟨58845495881938444456923251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39230330587958962971282167 58845495881938444456923251)
  ·
    refine ⟨88268243822907666685384877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58845495881938444456923251 88268243822907666685384877)
    ·
      refine ⟨33100591433590375007019329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88268243822907666685384877 33100591433590375007019329)
      ·
        refine ⟨24825443575192781255264497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33100591433590375007019329 24825443575192781255264497)
        ·
          refine ⟨18619082681394585941448373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24825443575192781255264497 18619082681394585941448373)
          ·
            refine ⟨1745539001380742432010785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18619082681394585941448373 1745539001380742432010785)
            ·
              refine ⟨1309154251035556824008089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745539001380742432010785 1309154251035556824008089)
              ·
                refine ⟨981865688276667618006067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309154251035556824008089 981865688276667618006067)
                ·
                  refine ⟨1472798532415001427009101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981865688276667618006067 1472798532415001427009101)
                  ·
                    refine ⟨552299449655625535128413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472798532415001427009101 552299449655625535128413)
                    ·
                      rfl

theorem cell22_1613399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_1613399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613399 prefixEnd_1613399 := by exact prefixLift 1613399
  have htrace : WordTrace (prefixWord ++ tailWord_1613399) baseStart_1613399 baseEnd_1613399 := by
    simpa [prefixWord, tailWord_1613399, baseEnd_1613399] using wordTrace_append hprefix tailTrace_1613399
  have hstable : (prefixWord ++ tailWord_1613399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613399).length < 2 ^ (prefixWord ++ tailWord_1613399).sum := by decide
  have hdescent : baseEnd_1613399 < baseStart_1613399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613440 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_1613440 : Nat := 118140960795 + 1613440 * 2 ^ 59
def prefixEnd_1613440 : Nat := 4983230072969 + 3 ^ 40 * 1613440 * 2
def baseEnd_1613440 : Nat := 184104494931171698284429

theorem tailTrace_1613440 : CollatzResearch.WordTrace tailWord_1613440 prefixEnd_1613440 184104494931171698284429 := by
  unfold tailWord_1613440
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423495637394954229582887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39231327516526605639443849 29423495637394954229582887)
  ·
    refine ⟨44135243456092431344374331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29423495637394954229582887 44135243456092431344374331)
    ·
      refine ⟨66202865184138647016561497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44135243456092431344374331 66202865184138647016561497)
      ·
        refine ⟨49652148888103985262421123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66202865184138647016561497 49652148888103985262421123)
        ·
          refine ⟨74478223332155977893631685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49652148888103985262421123 74478223332155977893631685)
          ·
            refine ⟨13964666874779245855055941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74478223332155977893631685 13964666874779245855055941)
            ·
              refine ⟨2618375039021108597822989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13964666874779245855055941 2618375039021108597822989)
              ·
                refine ⟨981890639632915724183621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2618375039021108597822989 981890639632915724183621)
                ·
                  refine ⟨184104494931171698284429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981890639632915724183621 184104494931171698284429)
                  ·
                    rfl

theorem cell22_1613440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_1613440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613440 prefixEnd_1613440 := by exact prefixLift 1613440
  have htrace : WordTrace (prefixWord ++ tailWord_1613440) baseStart_1613440 baseEnd_1613440 := by
    simpa [prefixWord, tailWord_1613440, baseEnd_1613440] using wordTrace_append hprefix tailTrace_1613440
  have hstable : (prefixWord ++ tailWord_1613440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613440).length < 2 ^ (prefixWord ++ tailWord_1613440).sum := by decide
  have hdescent : baseEnd_1613440 < baseStart_1613440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613451 : List Nat := [1, 1, 1, 1, 4, 1, 13]
def baseStart_1613451 : Nat := 118140960795 + 1613451 * 2 ^ 59
def prefixEnd_1613451 : Nat := 4983230072969 + 3 ^ 40 * 1613451 * 2
def baseEnd_1613451 : Nat := 20456194456233878993639

theorem tailTrace_1613451 : CollatzResearch.WordTrace tailWord_1613451 prefixEnd_1613451 20456194456233878993639 := by
  unfold tailWord_1613451
  simp only [CollatzResearch.WordTrace]
  refine ⟨58847392477750057337816207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39231594985166704891877471 58847392477750057337816207)
  ·
    refine ⟨88271088716625086006724311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58847392477750057337816207 88271088716625086006724311)
    ·
      refine ⟨132406633074937629010086467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88271088716625086006724311 132406633074937629010086467)
      ·
        refine ⟨198609949612406443515129701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132406633074937629010086467 198609949612406443515129701)
        ·
          refine ⟨37239365552326208159086819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198609949612406443515129701 37239365552326208159086819)
          ·
            refine ⟨55859048328489312238630229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37239365552326208159086819 55859048328489312238630229)
            ·
              refine ⟨20456194456233878993639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 55859048328489312238630229 20456194456233878993639)
              ·
                rfl

theorem cell22_1613451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 13].length) (baseStart_1613451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613451 prefixEnd_1613451 := by exact prefixLift 1613451
  have htrace : WordTrace (prefixWord ++ tailWord_1613451) baseStart_1613451 baseEnd_1613451 := by
    simpa [prefixWord, tailWord_1613451, baseEnd_1613451] using wordTrace_append hprefix tailTrace_1613451
  have hstable : (prefixWord ++ tailWord_1613451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613451).length < 2 ^ (prefixWord ++ tailWord_1613451).sum := by decide
  have hdescent : baseEnd_1613451 < baseStart_1613451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613470 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1613470 : Nat := 118140960795 + 1613470 * 2 ^ 59
def prefixEnd_1613470 : Nat := 4983230072969 + 3 ^ 40 * 1613470 * 2
def baseEnd_1613470 : Nat := 552323754406605016603195

theorem tailTrace_1613470 : CollatzResearch.WordTrace tailWord_1613470 prefixEnd_1613470 552323754406605016603195 := by
  unfold tailWord_1613470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356010683085152947844733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39232056976454149055171909 7356010683085152947844733)
  ·
    refine ⟨2758504006156932355441775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7356010683085152947844733 2758504006156932355441775)
    ·
      refine ⟨4137756009235398533162663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758504006156932355441775 4137756009235398533162663)
      ·
        refine ⟨6206634013853097799743995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137756009235398533162663 6206634013853097799743995)
        ·
          refine ⟨9309951020779646699615993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206634013853097799743995 9309951020779646699615993)
          ·
            refine ⟨6982463265584735024711995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309951020779646699615993 6982463265584735024711995)
            ·
              refine ⟨10473694898377102537067993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982463265584735024711995 10473694898377102537067993)
              ·
                refine ⟨7855271173782826902800995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10473694898377102537067993 7855271173782826902800995)
                ·
                  refine ⟨11782906760674240354201493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855271173782826902800995 11782906760674240354201493)
                  ·
                    refine ⟨552323754406605016603195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11782906760674240354201493 552323754406605016603195)
                    ·
                      rfl

theorem cell22_1613470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1613470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613470 prefixEnd_1613470 := by exact prefixLift 1613470
  have htrace : WordTrace (prefixWord ++ tailWord_1613470) baseStart_1613470 baseEnd_1613470 := by
    simpa [prefixWord, tailWord_1613470, baseEnd_1613470] using wordTrace_append hprefix tailTrace_1613470
  have hstable : (prefixWord ++ tailWord_1613470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613470).length < 2 ^ (prefixWord ++ tailWord_1613470).sum := by decide
  have hdescent : baseEnd_1613470 < baseStart_1613470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613528 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_1613528 : Nat := 118140960795 + 1613528 * 2 ^ 59
def prefixEnd_1613528 : Nat := 4983230072969 + 3 ^ 40 * 1613528 * 2
def baseEnd_1613528 : Nat := 552343608991912198653017

theorem tailTrace_1613528 : CollatzResearch.WordTrace tailWord_1613528 prefixEnd_1613528 552343608991912198653017 := by
  unfold tailWord_1613528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425100449235549744184619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39233467265647399658912825 29425100449235549744184619)
  ·
    refine ⟨44137650673853324616276929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29425100449235549744184619 44137650673853324616276929)
    ·
      refine ⟨33103238005389993462207697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44137650673853324616276929 33103238005389993462207697)
      ·
        refine ⟨24827428504042495096655773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33103238005389993462207697 24827428504042495096655773)
        ·
          refine ⟨9310285689015935661245915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24827428504042495096655773 9310285689015935661245915)
          ·
            refine ⟨13965428533523903491868873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310285689015935661245915 13965428533523903491868873)
            ·
              refine ⟨10474071400142927618901655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13965428533523903491868873 10474071400142927618901655)
              ·
                refine ⟨15711107100214391428352483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10474071400142927618901655 15711107100214391428352483)
                ·
                  refine ⟨23566660650321587142528725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15711107100214391428352483 23566660650321587142528725)
                  ·
                    refine ⟨552343608991912198653017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23566660650321587142528725 552343608991912198653017)
                    ·
                      rfl

theorem cell22_1613528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_1613528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613528 prefixEnd_1613528 := by exact prefixLift 1613528
  have htrace : WordTrace (prefixWord ++ tailWord_1613528) baseStart_1613528 baseEnd_1613528 := by
    simpa [prefixWord, tailWord_1613528, baseEnd_1613528] using wordTrace_append hprefix tailTrace_1613528
  have hstable : (prefixWord ++ tailWord_1613528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613528).length < 2 ^ (prefixWord ++ tailWord_1613528).sum := by decide
  have hdescent : baseEnd_1613528 < baseStart_1613528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613530 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_1613530 : Nat := 118140960795 + 1613530 * 2 ^ 59
def prefixEnd_1613530 : Nat := 4983230072969 + 3 ^ 40 * 1613530 * 2
def baseEnd_1613530 : Nat := 184114764544261620034337

theorem tailTrace_1613530 : CollatzResearch.WordTrace tailWord_1613530 prefixEnd_1613530 184114764544261620034337 := by
  unfold tailWord_1613530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14712568461115963457485511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39233515896309235886628029 14712568461115963457485511)
  ·
    refine ⟨22068852691673945186228267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14712568461115963457485511 22068852691673945186228267)
    ·
      refine ⟨33103279037510917779342401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22068852691673945186228267 33103279037510917779342401)
      ·
        refine ⟨24827459278133188334506801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33103279037510917779342401 24827459278133188334506801)
        ·
          refine ⟨18620594458599891250880101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24827459278133188334506801 18620594458599891250880101)
          ·
            refine ⟨3491361460987479609540019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18620594458599891250880101 3491361460987479609540019)
            ·
              refine ⟨5237042191481219414310029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491361460987479609540019 5237042191481219414310029)
              ·
                refine ⟨1963890821805457280366261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5237042191481219414310029 1963890821805457280366261)
                ·
                  refine ⟨184114764544261620034337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1963890821805457280366261 184114764544261620034337)
                  ·
                    rfl

theorem cell22_1613530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_1613530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613530 prefixEnd_1613530 := by exact prefixLift 1613530
  have htrace : WordTrace (prefixWord ++ tailWord_1613530) baseStart_1613530 baseEnd_1613530 := by
    simpa [prefixWord, tailWord_1613530, baseEnd_1613530] using wordTrace_append hprefix tailTrace_1613530
  have hstable : (prefixWord ++ tailWord_1613530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613530).length < 2 ^ (prefixWord ++ tailWord_1613530).sum := by decide
  have hdescent : baseEnd_1613530 < baseStart_1613530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613603 : List Nat := [1, 1, 1, 4, 2, 1, 2, 10]
def baseStart_1613603 : Nat := 118140960795 + 1613603 * 2 ^ 59
def prefixEnd_1613603 : Nat := 4983230072969 + 3 ^ 40 * 1613603 * 2
def baseEnd_1613603 : Nat := 61374364780515222558643

theorem tailTrace_1613603 : CollatzResearch.WordTrace tailWord_1613603 prefixEnd_1613603 61374364780515222558643 := by
  unfold tailWord_1613603
  simp only [CollatzResearch.WordTrace]
  refine ⟨58852936373199387297349463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39235290915466258198232975 58852936373199387297349463)
  ·
    refine ⟨88279404559799080946024195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58852936373199387297349463 88279404559799080946024195)
    ·
      refine ⟨132419106839698621419036293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88279404559799080946024195 132419106839698621419036293)
      ·
        refine ⟨24828582532443491516069305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132419106839698621419036293 24828582532443491516069305)
        ·
          refine ⟨18621436899332618637051979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24828582532443491516069305 18621436899332618637051979)
          ·
            refine ⟨27932155348998927955577969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18621436899332618637051979 27932155348998927955577969)
            ·
              refine ⟨20949116511749195966683477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27932155348998927955577969 20949116511749195966683477)
              ·
                refine ⟨61374364780515222558643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20949116511749195966683477 61374364780515222558643)
                ·
                  rfl

theorem cell22_1613603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 10].length) (baseStart_1613603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613603 prefixEnd_1613603 := by exact prefixLift 1613603
  have htrace : WordTrace (prefixWord ++ tailWord_1613603) baseStart_1613603 baseEnd_1613603 := by
    simpa [prefixWord, tailWord_1613603, baseEnd_1613603] using wordTrace_append hprefix tailTrace_1613603
  have hstable : (prefixWord ++ tailWord_1613603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613603).length < 2 ^ (prefixWord ++ tailWord_1613603).sum := by decide
  have hdescent : baseEnd_1613603 < baseStart_1613603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613605 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_1613605 : Nat := 118140960795 + 1613605 * 2 ^ 59
def prefixEnd_1613605 : Nat := 4983230072969 + 3 ^ 40 * 1613605 * 2
def baseEnd_1613605 : Nat := 552369967665509664477781

theorem tailTrace_1613605 : CollatzResearch.WordTrace tailWord_1613605 prefixEnd_1613605 552369967665509664477781 := by
  unfold tailWord_1613605
  simp only [CollatzResearch.WordTrace]
  refine ⟨58853009319192141638922269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39235339546128094425948179 58853009319192141638922269)
  ·
    refine ⟨22069878494697053114595851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58853009319192141638922269 22069878494697053114595851)
    ·
      refine ⟨33104817742045579671893777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22069878494697053114595851 33104817742045579671893777)
      ·
        refine ⟨24828613306534184753920333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33104817742045579671893777 24828613306534184753920333)
        ·
          refine ⟨9310729989950319282720125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24828613306534184753920333 9310729989950319282720125)
          ·
            refine ⟨3491523746231369731020047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9310729989950319282720125 3491523746231369731020047)
            ·
              refine ⟨5237285619347054596530071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491523746231369731020047 5237285619347054596530071)
              ·
                refine ⟨7855928429020581894795107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237285619347054596530071 7855928429020581894795107)
                ·
                  refine ⟨11783892643530872842192661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855928429020581894795107 11783892643530872842192661)
                  ·
                    refine ⟨552369967665509664477781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11783892643530872842192661 552369967665509664477781)
                    ·
                      rfl

theorem cell22_1613605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_1613605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613605 prefixEnd_1613605 := by exact prefixLift 1613605
  have htrace : WordTrace (prefixWord ++ tailWord_1613605) baseStart_1613605 baseEnd_1613605 := by
    simpa [prefixWord, tailWord_1613605, baseEnd_1613605] using wordTrace_append hprefix tailTrace_1613605
  have hstable : (prefixWord ++ tailWord_1613605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613605).length < 2 ^ (prefixWord ++ tailWord_1613605).sum := by decide
  have hdescent : baseEnd_1613605 < baseStart_1613605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613624 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_1613624 : Nat := 118140960795 + 1613624 * 2 ^ 59
def prefixEnd_1613624 : Nat := 4983230072969 + 3 ^ 40 * 1613624 * 2
def baseEnd_1613624 : Nat := 552376471753799948252723

theorem tailTrace_1613624 : CollatzResearch.WordTrace tailWord_1613624 prefixEnd_1613624 552376471753799948252723 := by
  unfold tailWord_1613624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29426851153061653941931963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39235801537415538589242617 29426851153061653941931963)
  ·
    refine ⟨44140276729592480912897945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29426851153061653941931963 44140276729592480912897945)
    ·
      refine ⟨33105207547194360684673459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44140276729592480912897945 33105207547194360684673459)
      ·
        refine ⟨49657811320791541027010189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33105207547194360684673459 49657811320791541027010189)
        ·
          refine ⟨18621679245296827885128821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49657811320791541027010189 18621679245296827885128821)
          ·
            refine ⟨1745782429246577614230827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18621679245296827885128821 1745782429246577614230827)
            ·
              refine ⟨2618673643869866421346241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745782429246577614230827 2618673643869866421346241)
              ·
                refine ⟨1964005232902399816009681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618673643869866421346241 1964005232902399816009681)
                ·
                  refine ⟨1473003924676799862007261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964005232902399816009681 1473003924676799862007261)
                  ·
                    refine ⟨552376471753799948252723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1473003924676799862007261 552376471753799948252723)
                    ·
                      rfl

theorem cell22_1613624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_1613624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613624 prefixEnd_1613624 := by exact prefixLift 1613624
  have htrace : WordTrace (prefixWord ++ tailWord_1613624) baseStart_1613624 baseEnd_1613624 := by
    simpa [prefixWord, tailWord_1613624, baseEnd_1613624] using wordTrace_append hprefix tailTrace_1613624
  have hstable : (prefixWord ++ tailWord_1613624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613624).length < 2 ^ (prefixWord ++ tailWord_1613624).sum := by decide
  have hdescent : baseEnd_1613624 < baseStart_1613624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613695 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_1613695 : Nat := 118140960795 + 1613695 * 2 ^ 59
def prefixEnd_1613695 : Nat := 4983230072969 + 3 ^ 40 * 1613695 * 2
def baseEnd_1613695 : Nat := 552400776504779429727505

theorem tailTrace_1613695 : CollatzResearch.WordTrace tailWord_1613695 prefixEnd_1613695 552400776504779429727505 := by
  unfold tailWord_1613695
  simp only [CollatzResearch.WordTrace]
  refine ⟨58856291888866087009698539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39237527925910724673132359 58856291888866087009698539)
  ·
    refine ⟨88284437833299130514547809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58856291888866087009698539 88284437833299130514547809)
    ·
      refine ⟨66213328374974347885910857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88284437833299130514547809 66213328374974347885910857)
      ·
        refine ⟨49659996281230760914433143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66213328374974347885910857 49659996281230760914433143)
        ·
          refine ⟨74489994421846141371649715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49659996281230760914433143 74489994421846141371649715)
          ·
            refine ⟨111734991632769212057474573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74489994421846141371649715 111734991632769212057474573)
            ·
              refine ⟨41900621862288454521552965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111734991632769212057474573 41900621862288454521552965)
              ·
                refine ⟨7856366599179085222791181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41900621862288454521552965 7856366599179085222791181)
                ·
                  refine ⟨2946137474692156958546693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7856366599179085222791181 2946137474692156958546693)
                  ·
                    refine ⟨552400776504779429727505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946137474692156958546693 552400776504779429727505)
                    ·
                      rfl

theorem cell22_1613695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_1613695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613695 prefixEnd_1613695 := by exact prefixLift 1613695
  have htrace : WordTrace (prefixWord ++ tailWord_1613695) baseStart_1613695 baseEnd_1613695 := by
    simpa [prefixWord, tailWord_1613695, baseEnd_1613695] using wordTrace_append hprefix tailTrace_1613695
  have hstable : (prefixWord ++ tailWord_1613695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613695).length < 2 ^ (prefixWord ++ tailWord_1613695).sum := by decide
  have hdescent : baseEnd_1613695 < baseStart_1613695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613699 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 5]
def baseStart_1613699 : Nat := 118140960795 + 1613699 * 2 ^ 59
def prefixEnd_1613699 : Nat := 4983230072969 + 3 ^ 40 * 1613699 * 2
def baseEnd_1613699 : Nat := 184134048595508250875831

theorem tailTrace_1613699 : CollatzResearch.WordTrace tailWord_1613699 prefixEnd_1613699 184134048595508250875831 := by
  unfold tailWord_1613699
  simp only [CollatzResearch.WordTrace]
  refine ⟨58856437780851595692844151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39237625187234397128562767 58856437780851595692844151)
  ·
    refine ⟨88284656671277393539266227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58856437780851595692844151 88284656671277393539266227)
    ·
      refine ⟨132426985006916090308899341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88284656671277393539266227 132426985006916090308899341)
      ·
        refine ⟨49660119377593533865837253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132426985006916090308899341 49660119377593533865837253)
        ·
          refine ⟨9311272383298787599844485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49660119377593533865837253 9311272383298787599844485)
          ·
            refine ⟨1745863571868522674970841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9311272383298787599844485 1745863571868522674970841)
            ·
              refine ⟨1309397678901392006228131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745863571868522674970841 1309397678901392006228131)
              ·
                refine ⟨1964096518352088009342197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309397678901392006228131 1964096518352088009342197)
                ·
                  refine ⟨184134048595508250875831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1964096518352088009342197 184134048595508250875831)
                  ·
                    rfl

theorem cell22_1613699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 5].length) (baseStart_1613699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613699 prefixEnd_1613699 := by exact prefixLift 1613699
  have htrace : WordTrace (prefixWord ++ tailWord_1613699) baseStart_1613699 baseEnd_1613699 := by
    simpa [prefixWord, tailWord_1613699, baseEnd_1613699] using wordTrace_append hprefix tailTrace_1613699
  have hstable : (prefixWord ++ tailWord_1613699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613699).length < 2 ^ (prefixWord ++ tailWord_1613699).sum := by decide
  have hdescent : baseEnd_1613699 < baseStart_1613699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613909 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1613909 : Nat := 118140960795 + 1613909 * 2 ^ 59
def prefixEnd_1613909 : Nat := 4983230072969 + 3 ^ 40 * 1613909 * 2
def baseEnd_1613909 : Nat := 552474033078154204876849

theorem tailTrace_1613909 : CollatzResearch.WordTrace tailWord_1613909 prefixEnd_1613909 552474033078154204876849 := by
  unfold tailWord_1613909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58864097110090801557988781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39242731406727201038659187 58864097110090801557988781)
  ·
    refine ⟨22074036416284050584245793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58864097110090801557988781 22074036416284050584245793)
    ·
      refine ⟨16555527312213037938184345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22074036416284050584245793 16555527312213037938184345)
      ·
        refine ⟨12416645484159778453638259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16555527312213037938184345 12416645484159778453638259)
        ·
          refine ⟨18624968226239667680457389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12416645484159778453638259 18624968226239667680457389)
          ·
            refine ⟨6984363084839875380171521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18624968226239667680457389 6984363084839875380171521)
            ·
              refine ⟨5238272313629906535128641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6984363084839875380171521 5238272313629906535128641)
              ·
                refine ⟨3928704235222429901346481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238272313629906535128641 3928704235222429901346481)
                ·
                  refine ⟨2946528176416822426009861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3928704235222429901346481 2946528176416822426009861)
                  ·
                    refine ⟨552474033078154204876849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946528176416822426009861 552474033078154204876849)
                    ·
                      rfl

theorem cell22_1613909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1613909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613909 prefixEnd_1613909 := by exact prefixLift 1613909
  have htrace : WordTrace (prefixWord ++ tailWord_1613909) baseStart_1613909 baseEnd_1613909 := by
    simpa [prefixWord, tailWord_1613909, baseEnd_1613909] using wordTrace_append hprefix tailTrace_1613909
  have hstable : (prefixWord ++ tailWord_1613909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613909).length < 2 ^ (prefixWord ++ tailWord_1613909).sum := by decide
  have hdescent : baseEnd_1613909 < baseStart_1613909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613937 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1613937 : Nat := 118140960795 + 1613937 * 2 ^ 59
def prefixEnd_1613937 : Nat := 4983230072969 + 3 ^ 40 * 1613937 * 2
def baseEnd_1613937 : Nat := 552483618050371465176763

theorem tailTrace_1613937 : CollatzResearch.WordTrace tailWord_1613937 prefixEnd_1613937 552483618050371465176763 := by
  unfold tailWord_1613937
  simp only [CollatzResearch.WordTrace]
  refine ⟨58865118353989362340008065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39243412235992908226672043 58865118353989362340008065)
  ·
    refine ⟨44148838765492021755006049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58865118353989362340008065 44148838765492021755006049)
    ·
      refine ⟨33111629074119016316254537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44148838765492021755006049 33111629074119016316254537)
      ·
        refine ⟨24833721805589262237190903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33111629074119016316254537 24833721805589262237190903)
        ·
          refine ⟨37250582708383893355786355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24833721805589262237190903 37250582708383893355786355)
          ·
            refine ⟨55875874062575840033679533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37250582708383893355786355 55875874062575840033679533)
            ·
              refine ⟨20953452773465940012629825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55875874062575840033679533 20953452773465940012629825)
              ·
                refine ⟨15715089580099455009472369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20953452773465940012629825 15715089580099455009472369)
                ·
                  refine ⟨11786317185074591257104277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15715089580099455009472369 11786317185074591257104277)
                  ·
                    refine ⟨552483618050371465176763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11786317185074591257104277 552483618050371465176763)
                    ·
                      rfl

theorem cell22_1613937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1613937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613937 prefixEnd_1613937 := by exact prefixLift 1613937
  have htrace : WordTrace (prefixWord ++ tailWord_1613937) baseStart_1613937 baseEnd_1613937 := by
    simpa [prefixWord, tailWord_1613937, baseEnd_1613937] using wordTrace_append hprefix tailTrace_1613937
  have hstable : (prefixWord ++ tailWord_1613937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613937).length < 2 ^ (prefixWord ++ tailWord_1613937).sum := by decide
  have hdescent : baseEnd_1613937 < baseStart_1613937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613952 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_1613952 : Nat := 118140960795 + 1613952 * 2 ^ 59
def prefixEnd_1613952 : Nat := 4983230072969 + 3 ^ 40 * 1613952 * 2
def baseEnd_1613952 : Nat := 184162917618972142017239

theorem tailTrace_1613952 : CollatzResearch.WordTrace tailWord_1613952 prefixEnd_1613952 184162917618972142017239 := by
  unfold tailWord_1613952
  simp only [CollatzResearch.WordTrace]
  refine ⟨29432832724467509950902055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39243776965956679934536073 29432832724467509950902055)
  ·
    refine ⟨44149249086701264926353083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29432832724467509950902055 44149249086701264926353083)
    ·
      refine ⟨66223873630051897389529625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44149249086701264926353083 66223873630051897389529625)
      ·
        refine ⟨49667905222538923042147219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66223873630051897389529625 49667905222538923042147219)
        ·
          refine ⟨74501857833808384563220829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49667905222538923042147219 74501857833808384563220829)
          ·
            refine ⟨27938196687678144211207811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74501857833808384563220829 27938196687678144211207811)
            ·
              refine ⟨41907295031517216316811717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27938196687678144211207811 41907295031517216316811717)
              ·
                refine ⟨7857617818409478059402197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41907295031517216316811717 7857617818409478059402197)
                ·
                  refine ⟨184162917618972142017239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7857617818409478059402197 184162917618972142017239)
                  ·
                    rfl

theorem cell22_1613952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_1613952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613952 prefixEnd_1613952 := by exact prefixLift 1613952
  have htrace : WordTrace (prefixWord ++ tailWord_1613952) baseStart_1613952 baseEnd_1613952 := by
    simpa [prefixWord, tailWord_1613952, baseEnd_1613952] using wordTrace_append hprefix tailTrace_1613952
  have hstable : (prefixWord ++ tailWord_1613952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613952).length < 2 ^ (prefixWord ++ tailWord_1613952).sum := by decide
  have hdescent : baseEnd_1613952 < baseStart_1613952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613984 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_1613984 : Nat := 118140960795 + 1613984 * 2 ^ 59
def prefixEnd_1613984 : Nat := 4983230072969 + 3 ^ 40 * 1613984 * 2
def baseEnd_1613984 : Nat := 552499707110879009251619

theorem tailTrace_1613984 : CollatzResearch.WordTrace tailWord_1613984 prefixEnd_1613984 552499707110879009251619 := by
  unfold tailWord_1613984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29433416292409544683484503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39244555056546059577979337 29433416292409544683484503)
  ·
    refine ⟨44150124438614317025226755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29433416292409544683484503 44150124438614317025226755)
    ·
      refine ⟨66225186657921475537840133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44150124438614317025226755 66225186657921475537840133)
      ·
        refine ⟨12417222498360276663345025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66225186657921475537840133 12417222498360276663345025)
        ·
          refine ⟨9312916873770207497508769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12417222498360276663345025 9312916873770207497508769)
          ·
            refine ⟨6984687655327655623131577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9312916873770207497508769 6984687655327655623131577)
            ·
              refine ⟨5238515741495741717348683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6984687655327655623131577 5238515741495741717348683)
              ·
                refine ⟨7857773612243612576023025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5238515741495741717348683 7857773612243612576023025)
                ·
                  refine ⟨5893330209182709432017269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7857773612243612576023025 5893330209182709432017269)
                  ·
                    refine ⟨552499707110879009251619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5893330209182709432017269 552499707110879009251619)
                    ·
                      rfl

theorem cell22_1613984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_1613984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1613984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1613984 prefixEnd_1613984 := by exact prefixLift 1613984
  have htrace : WordTrace (prefixWord ++ tailWord_1613984) baseStart_1613984 baseEnd_1613984 := by
    simpa [prefixWord, tailWord_1613984, baseEnd_1613984] using wordTrace_append hprefix tailTrace_1613984
  have hstable : (prefixWord ++ tailWord_1613984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613984).length < 2 ^ (prefixWord ++ tailWord_1613984).sum := by decide
  have hdescent : baseEnd_1613984 < baseStart_1613984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614016 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_1614016 : Nat := 118140960795 + 1614016 * 2 ^ 59
def prefixEnd_1614016 : Nat := 4983230072969 + 3 ^ 40 * 1614016 * 2
def baseEnd_1614016 : Nat := 552510661364841592451521

theorem tailTrace_1614016 : CollatzResearch.WordTrace tailWord_1614016 prefixEnd_1614016 552510661364841592451521 := by
  unfold tailWord_1614016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29433999860351579416066951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39245333147135439221422601 29433999860351579416066951)
  ·
    refine ⟨44150999790527369124100427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29433999860351579416066951 44150999790527369124100427)
    ·
      refine ⟨66226499685791053686150641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44150999790527369124100427 66226499685791053686150641)
      ·
        refine ⟨49669874764343290264612981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66226499685791053686150641 49669874764343290264612981)
        ·
          refine ⟨4656550759157183462307467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49669874764343290264612981 4656550759157183462307467)
          ·
            refine ⟨6984826138735775193461201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656550759157183462307467 6984826138735775193461201)
            ·
              refine ⟨5238619604051831395095901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6984826138735775193461201 5238619604051831395095901)
              ·
                refine ⟨1964482351519436773160963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5238619604051831395095901 1964482351519436773160963)
                ·
                  refine ⟨2946723527279155159741445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964482351519436773160963 2946723527279155159741445)
                  ·
                    refine ⟨552510661364841592451521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946723527279155159741445 552510661364841592451521)
                    ·
                      rfl

theorem cell22_1614016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_1614016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614016 prefixEnd_1614016 := by exact prefixLift 1614016
  have htrace : WordTrace (prefixWord ++ tailWord_1614016) baseStart_1614016 baseEnd_1614016 := by
    simpa [prefixWord, tailWord_1614016, baseEnd_1614016] using wordTrace_append hprefix tailTrace_1614016
  have hstable : (prefixWord ++ tailWord_1614016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614016).length < 2 ^ (prefixWord ++ tailWord_1614016).sum := by decide
  have hdescent : baseEnd_1614016 < baseStart_1614016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614082 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1614082 : Nat := 118140960795 + 1614082 * 2 ^ 59
def prefixEnd_1614082 : Nat := 4983230072969 + 3 ^ 40 * 1614082 * 2
def baseEnd_1614082 : Nat := 184177751504546473433773

theorem tailTrace_1614082 : CollatzResearch.WordTrace tailWord_1614082 prefixEnd_1614082 184177751504546473433773 := by
  unfold tailWord_1614082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14717601734616013026009125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39246937958976034736024333 14717601734616013026009125)
  ·
    refine ⟨2759550325240502442376711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14717601734616013026009125 2759550325240502442376711)
    ·
      refine ⟨4139325487860753663565067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759550325240502442376711 4139325487860753663565067)
      ·
        refine ⟨6208988231791130495347601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139325487860753663565067 6208988231791130495347601)
        ·
          refine ⟨4656741173843347871510701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6208988231791130495347601 4656741173843347871510701)
          ·
            refine ⟨1746277940191255451816513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4656741173843347871510701 1746277940191255451816513)
            ·
              refine ⟨1309708455143441588862385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746277940191255451816513 1309708455143441588862385)
              ·
                refine ⟨982281341357581191646789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309708455143441588862385 982281341357581191646789)
                ·
                  refine ⟨184177751504546473433773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982281341357581191646789 184177751504546473433773)
                  ·
                    rfl

theorem cell22_1614082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1614082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614082 prefixEnd_1614082 := by exact prefixLift 1614082
  have htrace : WordTrace (prefixWord ++ tailWord_1614082) baseStart_1614082 baseEnd_1614082 := by
    simpa [prefixWord, tailWord_1614082, baseEnd_1614082] using wordTrace_append hprefix tailTrace_1614082
  have hstable : (prefixWord ++ tailWord_1614082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614082).length < 2 ^ (prefixWord ++ tailWord_1614082).sum := by decide
  have hdescent : baseEnd_1614082 < baseStart_1614082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614089 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_1614089 : Nat := 118140960795 + 1614089 * 2 ^ 59
def prefixEnd_1614089 : Nat := 4983230072969 + 3 ^ 40 * 1614089 * 2
def baseEnd_1614089 : Nat := 552535650756693735376297

theorem tailTrace_1614089 : CollatzResearch.WordTrace tailWord_1614089 prefixEnd_1614089 552535650756693735376297 := by
  unfold tailWord_1614089
  simp only [CollatzResearch.WordTrace]
  refine ⟨58870662249438692299541321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39247108166292461533027547 58870662249438692299541321)
  ·
    refine ⟨44152996687079019224655991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58870662249438692299541321 44152996687079019224655991)
    ·
      refine ⟨66229495030618528836983987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44152996687079019224655991 66229495030618528836983987)
      ·
        refine ⟨99344242545927793255475981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66229495030618528836983987 99344242545927793255475981)
        ·
          refine ⟨37254090954722922470803493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99344242545927793255475981 37254090954722922470803493)
          ·
            refine ⟨6985142054010547963275655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37254090954722922470803493 6985142054010547963275655)
            ·
              refine ⟨10477713081015821944913483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6985142054010547963275655 10477713081015821944913483)
              ·
                refine ⟨15716569621523732917370225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10477713081015821944913483 15716569621523732917370225)
                ·
                  refine ⟨11787427216142799688027669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15716569621523732917370225 11787427216142799688027669)
                  ·
                    refine ⟨552535650756693735376297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11787427216142799688027669 552535650756693735376297)
                    ·
                      rfl

theorem cell22_1614089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_1614089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614089 prefixEnd_1614089 := by exact prefixLift 1614089
  have htrace : WordTrace (prefixWord ++ tailWord_1614089) baseStart_1614089 baseEnd_1614089 := by
    simpa [prefixWord, tailWord_1614089, baseEnd_1614089] using wordTrace_append hprefix tailTrace_1614089
  have hstable : (prefixWord ++ tailWord_1614089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614089).length < 2 ^ (prefixWord ++ tailWord_1614089).sum := by decide
  have hdescent : baseEnd_1614089 < baseStart_1614089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614091 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 3, 3]
def baseStart_1614091 : Nat := 118140960795 + 1614091 * 2 ^ 59
def prefixEnd_1614091 : Nat := 4983230072969 + 3 ^ 40 * 1614091 * 2
def baseEnd_1614091 : Nat := 552536335397566396826291

theorem tailTrace_1614091 : CollatzResearch.WordTrace tailWord_1614091 prefixEnd_1614091 552536335397566396826291 := by
  unfold tailWord_1614091
  simp only [CollatzResearch.WordTrace]
  refine ⟨58870735195431446641114127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39247156796954297760742751 58870735195431446641114127)
  ·
    refine ⟨88306102793147169961671191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58870735195431446641114127 88306102793147169961671191)
    ·
      refine ⟨132459154189720754942506787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88306102793147169961671191 132459154189720754942506787)
      ·
        refine ⟨198688731284581132413760181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132459154189720754942506787 198688731284581132413760181)
        ·
          refine ⟨18627068557929481163790017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198688731284581132413760181 18627068557929481163790017)
          ·
            refine ⟨13970301418447110872842513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18627068557929481163790017 13970301418447110872842513)
            ·
              refine ⟨10477726063835333154631885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13970301418447110872842513 10477726063835333154631885)
              ·
                refine ⟨3929147273938249932986957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10477726063835333154631885 3929147273938249932986957)
                ·
                  refine ⟨1473430227726843724870109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3929147273938249932986957 1473430227726843724870109)
                  ·
                    refine ⟨552536335397566396826291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1473430227726843724870109 552536335397566396826291)
                    ·
                      rfl

theorem cell22_1614091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3].length) (baseStart_1614091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614091 prefixEnd_1614091 := by exact prefixLift 1614091
  have htrace : WordTrace (prefixWord ++ tailWord_1614091) baseStart_1614091 baseEnd_1614091 := by
    simpa [prefixWord, tailWord_1614091, baseEnd_1614091] using wordTrace_append hprefix tailTrace_1614091
  have hstable : (prefixWord ++ tailWord_1614091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614091).length < 2 ^ (prefixWord ++ tailWord_1614091).sum := by decide
  have hdescent : baseEnd_1614091 < baseStart_1614091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614110 : List Nat := [4, 3, 2, 1, 1, 2, 3, 6]
def baseStart_1614110 : Nat := 118140960795 + 1614110 * 2 ^ 59
def prefixEnd_1614110 : Nat := 4983230072969 + 3 ^ 40 * 1614110 * 2
def baseEnd_1614110 : Nat := 61393648831761853400137

theorem tailTrace_1614110 : CollatzResearch.WordTrace tailWord_1614110 prefixEnd_1614110 61393648831761853400137 := by
  unfold tailWord_1614110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358928522795326610756973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39247618788241741924037189 7358928522795326610756973)
  ·
    refine ⟨2759598196048247479033865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7358928522795326610756973 2759598196048247479033865)
    ·
      refine ⟨2069698647036185609275399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2759598196048247479033865 2069698647036185609275399)
      ·
        refine ⟨3104547970554278413913099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069698647036185609275399 3104547970554278413913099)
        ·
          refine ⟨4656821955831417620869649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104547970554278413913099 4656821955831417620869649)
          ·
            refine ⟨3492616466873563215652237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656821955831417620869649 3492616466873563215652237)
            ·
              refine ⟨1309731175077586205869589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492616466873563215652237 1309731175077586205869589)
              ·
                refine ⟨61393648831761853400137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1309731175077586205869589 61393648831761853400137)
                ·
                  rfl

theorem cell22_1614110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_1614110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614110 prefixEnd_1614110 := by exact prefixLift 1614110
  have htrace : WordTrace (prefixWord ++ tailWord_1614110) baseStart_1614110 baseEnd_1614110 := by
    simpa [prefixWord, tailWord_1614110, baseEnd_1614110] using wordTrace_append hprefix tailTrace_1614110
  have hstable : (prefixWord ++ tailWord_1614110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614110).length < 2 ^ (prefixWord ++ tailWord_1614110).sum := by decide
  have hdescent : baseEnd_1614110 < baseStart_1614110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614138 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_1614138 : Nat := 118140960795 + 1614138 * 2 ^ 59
def prefixEnd_1614138 : Nat := 4983230072969 + 3 ^ 40 * 1614138 * 2
def baseEnd_1614138 : Nat := 184184141486024646967049

theorem tailTrace_1614138 : CollatzResearch.WordTrace tailWord_1614138 prefixEnd_1614138 184184141486024646967049 := by
  unfold tailWord_1614138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718112356565293417018767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39248299617507449112050045 14718112356565293417018767)
  ·
    refine ⟨22077168534847940125528151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14718112356565293417018767 22077168534847940125528151)
    ·
      refine ⟨33115752802271910188292227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22077168534847940125528151 33115752802271910188292227)
      ·
        refine ⟨49673629203407865282438341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33115752802271910188292227 49673629203407865282438341)
        ·
          refine ⟨9313805475638974740457189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49673629203407865282438341 9313805475638974740457189)
          ·
            refine ⟨1746338526682307763835723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9313805475638974740457189 1746338526682307763835723)
            ·
              refine ⟨2619507790023461645753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746338526682307763835723 2619507790023461645753585)
              ·
                refine ⟨1964630842517596234315189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619507790023461645753585 1964630842517596234315189)
                ·
                  refine ⟨184184141486024646967049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1964630842517596234315189 184184141486024646967049)
                  ·
                    rfl

theorem cell22_1614138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_1614138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614138 prefixEnd_1614138 := by exact prefixLift 1614138
  have htrace : WordTrace (prefixWord ++ tailWord_1614138) baseStart_1614138 baseEnd_1614138 := by
    simpa [prefixWord, tailWord_1614138, baseEnd_1614138] using wordTrace_append hprefix tailTrace_1614138
  have hstable : (prefixWord ++ tailWord_1614138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614138).length < 2 ^ (prefixWord ++ tailWord_1614138).sum := by decide
  have hdescent : baseEnd_1614138 < baseStart_1614138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614294 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1614294 : Nat := 118140960795 + 1614294 * 2 ^ 59
def prefixEnd_1614294 : Nat := 4983230072969 + 3 ^ 40 * 1614294 * 2
def baseEnd_1614294 : Nat := 552605826446141534000669

theorem tailTrace_1614294 : CollatzResearch.WordTrace tailWord_1614294 prefixEnd_1614294 552605826446141534000669 := by
  unfold tailWord_1614294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679883700856000769422121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39252092809130674873835957 3679883700856000769422121)
  ·
    refine ⟨2759912775642000577066591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3679883700856000769422121 2759912775642000577066591)
    ·
      refine ⟨4139869163463000865599887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759912775642000577066591 4139869163463000865599887)
      ·
        refine ⟨6209803745194501298399831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139869163463000865599887 6209803745194501298399831)
        ·
          refine ⟨9314705617791751947599747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209803745194501298399831 9314705617791751947599747)
          ·
            refine ⟨13972058426687627921399621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314705617791751947599747 13972058426687627921399621)
            ·
              refine ⟨2619760955003930235262429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13972058426687627921399621 2619760955003930235262429)
              ·
                refine ⟨982410358126473838223411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2619760955003930235262429 982410358126473838223411)
                ·
                  refine ⟨1473615537189710757335117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982410358126473838223411 1473615537189710757335117)
                  ·
                    refine ⟨552605826446141534000669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1473615537189710757335117 552605826446141534000669)
                    ·
                      rfl

theorem cell22_1614294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1614294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614294 prefixEnd_1614294 := by exact prefixLift 1614294
  have htrace : WordTrace (prefixWord ++ tailWord_1614294) baseStart_1614294 baseEnd_1614294 := by
    simpa [prefixWord, tailWord_1614294, baseEnd_1614294] using wordTrace_append hprefix tailTrace_1614294
  have hstable : (prefixWord ++ tailWord_1614294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614294).length < 2 ^ (prefixWord ++ tailWord_1614294).sum := by decide
  have hdescent : baseEnd_1614294 < baseStart_1614294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614307 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 5]
def baseStart_1614307 : Nat := 118140960795 + 1614307 * 2 ^ 59
def prefixEnd_1614307 : Nat := 4983230072969 + 3 ^ 40 * 1614307 * 2
def baseEnd_1614307 : Nat := 184203425537271277808543

theorem tailTrace_1614307 : CollatzResearch.WordTrace tailWord_1614307 prefixEnd_1614307 184203425537271277808543 := by
  unfold tailWord_1614307
  simp only [CollatzResearch.WordTrace]
  refine ⟨58878613362648915530977175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39252408908432610353984783 58878613362648915530977175)
  ·
    refine ⟨88317920043973373296465763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58878613362648915530977175 88317920043973373296465763)
    ·
      refine ⟨132476880065960059944698645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88317920043973373296465763 132476880065960059944698645)
      ·
        refine ⟨6209853753091877809907749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132476880065960059944698645 6209853753091877809907749)
        ·
          refine ⟨1164347578704727089357703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6209853753091877809907749 1164347578704727089357703)
          ·
            refine ⟨1746521368057090634036555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164347578704727089357703 1746521368057090634036555)
            ·
              refine ⟨2619782052085635951054833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746521368057090634036555 2619782052085635951054833)
              ·
                refine ⟨1964836539064226963291125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619782052085635951054833 1964836539064226963291125)
                ·
                  refine ⟨184203425537271277808543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1964836539064226963291125 184203425537271277808543)
                  ·
                    rfl

theorem cell22_1614307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 5].length) (baseStart_1614307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614307 prefixEnd_1614307 := by exact prefixLift 1614307
  have htrace : WordTrace (prefixWord ++ tailWord_1614307) baseStart_1614307 baseEnd_1614307 := by
    simpa [prefixWord, tailWord_1614307, baseEnd_1614307] using wordTrace_append hprefix tailTrace_1614307
  have hstable : (prefixWord ++ tailWord_1614307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614307).length < 2 ^ (prefixWord ++ tailWord_1614307).sum := by decide
  have hdescent : baseEnd_1614307 < baseStart_1614307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614318 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_1614318 : Nat := 118140960795 + 1614318 * 2 ^ 59
def prefixEnd_1614318 : Nat := 4983230072969 + 3 ^ 40 * 1614318 * 2
def baseEnd_1614318 : Nat := 184204680712204490466865

theorem tailTrace_1614318 : CollatzResearch.WordTrace tailWord_1614318 prefixEnd_1614318 184204680712204490466865 := by
  unfold tailWord_1614318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7359876820701133051203451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39252676377072709606418405 7359876820701133051203451)
  ·
    refine ⟨11039815231051699576805177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7359876820701133051203451 11039815231051699576805177)
    ·
      refine ⟨8279861423288774682603883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11039815231051699576805177 8279861423288774682603883)
      ·
        refine ⟨12419792134933162023905825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8279861423288774682603883 12419792134933162023905825)
        ·
          refine ⟨9314844101199871517929369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12419792134933162023905825 9314844101199871517929369)
          ·
            refine ⟨6986133075899903638447027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9314844101199871517929369 6986133075899903638447027)
            ·
              refine ⟨10479199613849855457670541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986133075899903638447027 10479199613849855457670541)
              ·
                refine ⟨3929699855193695796626453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10479199613849855457670541 3929699855193695796626453)
                ·
                  refine ⟨184204680712204490466865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3929699855193695796626453 184204680712204490466865)
                  ·
                    rfl

theorem cell22_1614318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_1614318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614318 prefixEnd_1614318 := by exact prefixLift 1614318
  have htrace : WordTrace (prefixWord ++ tailWord_1614318) baseStart_1614318 baseEnd_1614318 := by
    simpa [prefixWord, tailWord_1614318, baseEnd_1614318] using wordTrace_append hprefix tailTrace_1614318
  have hstable : (prefixWord ++ tailWord_1614318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614318).length < 2 ^ (prefixWord ++ tailWord_1614318).sum := by decide
  have hdescent : baseEnd_1614318 < baseStart_1614318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614348 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1614348 : Nat := 118140960795 + 1614348 * 2 ^ 59
def prefixEnd_1614348 : Nat := 4983230072969 + 3 ^ 40 * 1614348 * 2
def baseEnd_1614348 : Nat := 552624311749703393150503

theorem tailTrace_1614348 : CollatzResearch.WordTrace tailWord_1614348 prefixEnd_1614348 552624311749703393150503 := by
  unfold tailWord_1614348
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440054377750189766609849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39253405837000253022146465 29440054377750189766609849)
  ·
    refine ⟨22080040783312642324957387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29440054377750189766609849 22080040783312642324957387)
    ·
      refine ⟨33120061174968963487436081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22080040783312642324957387 33120061174968963487436081)
      ·
        refine ⟨24840045881226722615577061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33120061174968963487436081 24840045881226722615577061)
        ·
          refine ⟨4657508602730010490420699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24840045881226722615577061 4657508602730010490420699)
          ·
            refine ⟨6986262904095015735631049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657508602730010490420699 6986262904095015735631049)
            ·
              refine ⟨5239697178071261801723287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6986262904095015735631049 5239697178071261801723287)
              ·
                refine ⟨7859545767106892702584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5239697178071261801723287 7859545767106892702584931)
                ·
                  refine ⟨11789318650660339053877397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7859545767106892702584931 11789318650660339053877397)
                  ·
                    refine ⟨552624311749703393150503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11789318650660339053877397 552624311749703393150503)
                    ·
                      rfl

theorem cell22_1614348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1614348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614348 prefixEnd_1614348 := by exact prefixLift 1614348
  have htrace : WordTrace (prefixWord ++ tailWord_1614348) baseStart_1614348 baseEnd_1614348 := by
    simpa [prefixWord, tailWord_1614348, baseEnd_1614348] using wordTrace_append hprefix tailTrace_1614348
  have hstable : (prefixWord ++ tailWord_1614348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614348).length < 2 ^ (prefixWord ++ tailWord_1614348).sum := by decide
  have hdescent : baseEnd_1614348 < baseStart_1614348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614350 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1614350 : Nat := 118140960795 + 1614350 * 2 ^ 59
def prefixEnd_1614350 : Nat := 4983230072969 + 3 ^ 40 * 1614350 * 2
def baseEnd_1614350 : Nat := 552624996390576054600497

theorem tailTrace_1614350 : CollatzResearch.WordTrace tailWord_1614350 prefixEnd_1614350 552624996390576054600497 := by
  unfold tailWord_1614350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360022712686641734349063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39253454467662089249861669 7360022712686641734349063)
  ·
    refine ⟨11040034069029962601523595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360022712686641734349063 11040034069029962601523595)
    ·
      refine ⟨16560051103544943902285393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040034069029962601523595 16560051103544943902285393)
      ·
        refine ⟨12420038327658707926714045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16560051103544943902285393 12420038327658707926714045)
        ·
          refine ⟨4657514372872015472517767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12420038327658707926714045 4657514372872015472517767)
          ·
            refine ⟨6986271559308023208776651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657514372872015472517767 6986271559308023208776651)
            ·
              refine ⟨10479407338962034813164977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986271559308023208776651 10479407338962034813164977)
              ·
                refine ⟨7859555504221526109873733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10479407338962034813164977 7859555504221526109873733)
                ·
                  refine ⟨1473666657041536145601325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7859555504221526109873733 1473666657041536145601325)
                  ·
                    refine ⟨552624996390576054600497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1473666657041536145601325 552624996390576054600497)
                    ·
                      rfl

theorem cell22_1614350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1614350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614350 prefixEnd_1614350 := by exact prefixLift 1614350
  have htrace : WordTrace (prefixWord ++ tailWord_1614350) baseStart_1614350 baseEnd_1614350 := by
    simpa [prefixWord, tailWord_1614350, baseEnd_1614350] using wordTrace_append hprefix tailTrace_1614350
  have hstable : (prefixWord ++ tailWord_1614350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614350).length < 2 ^ (prefixWord ++ tailWord_1614350).sum := by decide
  have hdescent : baseEnd_1614350 < baseStart_1614350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614361 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1614361 : Nat := 118140960795 + 1614361 * 2 ^ 59
def prefixEnd_1614361 : Nat := 4983230072969 + 3 ^ 40 * 1614361 * 2
def baseEnd_1614361 : Nat := 552628761915375692575463

theorem tailTrace_1614361 : CollatzResearch.WordTrace tailWord_1614361 prefixEnd_1614361 552628761915375692575463 := by
  unfold tailWord_1614361
  simp only [CollatzResearch.WordTrace]
  refine ⟨58880582904453282753442937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39253721936302188502295291 58880582904453282753442937)
  ·
    refine ⟨44160437178339962065082203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58880582904453282753442937 44160437178339962065082203)
    ·
      refine ⟨66240655767509943097623305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44160437178339962065082203 66240655767509943097623305)
      ·
        refine ⟨49680491825632457323217479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66240655767509943097623305 49680491825632457323217479)
        ·
          refine ⟨74520737738448685984826219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49680491825632457323217479 74520737738448685984826219)
          ·
            refine ⟨111781106607673028977239329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74520737738448685984826219 111781106607673028977239329)
            ·
              refine ⟨83835829955754771732929497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111781106607673028977239329 83835829955754771732929497)
              ·
                refine ⟨62876872466816078799697123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83835829955754771732929497 62876872466816078799697123)
                ·
                  refine ⟨94315308700224118199545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62876872466816078799697123 94315308700224118199545685)
                  ·
                    refine ⟨552628761915375692575463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94315308700224118199545685 552628761915375692575463)
                    ·
                      rfl

theorem cell22_1614361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1614361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614361 prefixEnd_1614361 := by exact prefixLift 1614361
  have htrace : WordTrace (prefixWord ++ tailWord_1614361) baseStart_1614361 baseEnd_1614361 := by
    simpa [prefixWord, tailWord_1614361, baseEnd_1614361] using wordTrace_append hprefix tailTrace_1614361
  have hstable : (prefixWord ++ tailWord_1614361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614361).length < 2 ^ (prefixWord ++ tailWord_1614361).sum := by decide
  have hdescent : baseEnd_1614361 < baseStart_1614361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614365 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1614365 : Nat := 118140960795 + 1614365 * 2 ^ 59
def prefixEnd_1614365 : Nat := 4983230072969 + 3 ^ 40 * 1614365 * 2
def baseEnd_1614365 : Nat := 552630131197121015475451

theorem tailTrace_1614365 : CollatzResearch.WordTrace tailWord_1614365 prefixEnd_1614365 552630131197121015475451 := by
  unfold tailWord_1614365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58880728796438791436588549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39253819197625860957725699 58880728796438791436588549)
  ·
    refine ⟨11040136649332273394360353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58880728796438791436588549 11040136649332273394360353)
    ·
      refine ⟨8280102486999205045770265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11040136649332273394360353 8280102486999205045770265)
      ·
        refine ⟨6210076865249403784327699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8280102486999205045770265 6210076865249403784327699)
        ·
          refine ⟨9315115297874105676491549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210076865249403784327699 9315115297874105676491549)
          ·
            refine ⟨3493168236702789628684331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9315115297874105676491549 3493168236702789628684331)
            ·
              refine ⟨5239752355054184443026497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493168236702789628684331 5239752355054184443026497)
              ·
                refine ⟨3929814266290638332269873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239752355054184443026497 3929814266290638332269873)
                ·
                  refine ⟨2947360699717978749202405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929814266290638332269873 2947360699717978749202405)
                  ·
                    refine ⟨552630131197121015475451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947360699717978749202405 552630131197121015475451)
                    ·
                      rfl

theorem cell22_1614365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1614365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614365 prefixEnd_1614365 := by exact prefixLift 1614365
  have htrace : WordTrace (prefixWord ++ tailWord_1614365) baseStart_1614365 baseEnd_1614365 := by
    simpa [prefixWord, tailWord_1614365, baseEnd_1614365] using wordTrace_append hprefix tailTrace_1614365
  have hstable : (prefixWord ++ tailWord_1614365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614365).length < 2 ^ (prefixWord ++ tailWord_1614365).sum := by decide
  have hdescent : baseEnd_1614365 < baseStart_1614365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614412 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_1614412 : Nat := 118140960795 + 1614412 * 2 ^ 59
def prefixEnd_1614412 : Nat := 4983230072969 + 3 ^ 40 * 1614412 * 2
def baseEnd_1614412 : Nat := 552646220257628559550307

theorem tailTrace_1614412 : CollatzResearch.WordTrace tailWord_1614412 prefixEnd_1614412 552646220257628559550307 := by
  unfold tailWord_1614412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441221513634259231774745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39254962018179012309032993 29441221513634259231774745)
  ·
    refine ⟨22080916135225694423831059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29441221513634259231774745 22080916135225694423831059)
    ·
      refine ⟨33121374202838541635746589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22080916135225694423831059 33121374202838541635746589)
      ·
        refine ⟨12420515326064453113404971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33121374202838541635746589 12420515326064453113404971)
        ·
          refine ⟨18630772989096679670107457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420515326064453113404971 18630772989096679670107457)
          ·
            refine ⟨13973079741822509752580593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18630772989096679670107457 13973079741822509752580593)
            ·
              refine ⟨10479809806366882314435445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973079741822509752580593 10479809806366882314435445)
              ·
                refine ⟨982482169346895216978323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10479809806366882314435445 982482169346895216978323)
                ·
                  refine ⟨1473723254020342825467485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982482169346895216978323 1473723254020342825467485)
                  ·
                    refine ⟨552646220257628559550307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1473723254020342825467485 552646220257628559550307)
                    ·
                      rfl

theorem cell22_1614412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_1614412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614412 prefixEnd_1614412 := by exact prefixLift 1614412
  have htrace : WordTrace (prefixWord ++ tailWord_1614412) baseStart_1614412 baseEnd_1614412 := by
    simpa [prefixWord, tailWord_1614412, baseEnd_1614412] using wordTrace_append hprefix tailTrace_1614412
  have hstable : (prefixWord ++ tailWord_1614412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614412).length < 2 ^ (prefixWord ++ tailWord_1614412).sum := by decide
  have hdescent : baseEnd_1614412 < baseStart_1614412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614423 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1614423 : Nat := 118140960795 + 1614423 * 2 ^ 59
def prefixEnd_1614423 : Nat := 4983230072969 + 3 ^ 40 * 1614423 * 2
def baseEnd_1614423 : Nat := 552649985782428197525273

theorem tailTrace_1614423 : CollatzResearch.WordTrace tailWord_1614423 prefixEnd_1614423 552649985782428197525273 := by
  unfold tailWord_1614423
  simp only [CollatzResearch.WordTrace]
  refine ⟨58882844230228667342199923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39255229486819111561466615 58882844230228667342199923)
  ·
    refine ⟨88324266345343001013299885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58882844230228667342199923 88324266345343001013299885)
    ·
      refine ⟨33121599879503625379987457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88324266345343001013299885 33121599879503625379987457)
      ·
        refine ⟨24841199909627719034990593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33121599879503625379987457 24841199909627719034990593)
        ·
          refine ⟨18630899932220789276242945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24841199909627719034990593 18630899932220789276242945)
          ·
            refine ⟨13973174949165591957182209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18630899932220789276242945 13973174949165591957182209)
            ·
              refine ⟨10479881211874193967886657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973174949165591957182209 10479881211874193967886657)
              ·
                refine ⟨7859910908905645475914993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10479881211874193967886657 7859910908905645475914993)
                ·
                  refine ⟨5894933181679234106936245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7859910908905645475914993 5894933181679234106936245)
                  ·
                    refine ⟨552649985782428197525273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5894933181679234106936245 552649985782428197525273)
                    ·
                      rfl

theorem cell22_1614423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1614423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614423 prefixEnd_1614423 := by exact prefixLift 1614423
  have htrace : WordTrace (prefixWord ++ tailWord_1614423) baseStart_1614423 baseEnd_1614423 := by
    simpa [prefixWord, tailWord_1614423, baseEnd_1614423] using wordTrace_append hprefix tailTrace_1614423
  have hstable : (prefixWord ++ tailWord_1614423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614423).length < 2 ^ (prefixWord ++ tailWord_1614423).sum := by decide
  have hdescent : baseEnd_1614423 < baseStart_1614423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614506 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1614506 : Nat := 118140960795 + 1614506 * 2 ^ 59
def prefixEnd_1614506 : Nat := 4983230072969 + 3 ^ 40 * 1614506 * 2
def baseEnd_1614506 : Nat := 552678398378643647700019

theorem tailTrace_1614506 : CollatzResearch.WordTrace tailWord_1614506 prefixEnd_1614506 552678398378643647700019 := by
  unfold tailWord_1614506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721467872231993129367843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39257247659285315011647581 14721467872231993129367843)
  ·
    refine ⟨22082201808347989694051765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721467872231993129367843 22082201808347989694051765)
    ·
      refine ⟨2070206419532624033817353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22082201808347989694051765 2070206419532624033817353)
      ·
        refine ⟨1552654814649468025363015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070206419532624033817353 1552654814649468025363015)
        ·
          refine ⟨2328982221974202038044523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552654814649468025363015 2328982221974202038044523)
          ·
            refine ⟨3493473332961303057066785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328982221974202038044523 3493473332961303057066785)
            ·
              refine ⟨2620104999720977292800089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493473332961303057066785 2620104999720977292800089)
              ·
                refine ⟨1965078749790732969600067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620104999720977292800089 1965078749790732969600067)
                ·
                  refine ⟨2947618124686099454400101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965078749790732969600067 2947618124686099454400101)
                  ·
                    refine ⟨552678398378643647700019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947618124686099454400101 552678398378643647700019)
                    ·
                      rfl

theorem cell22_1614506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1614506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614506 prefixEnd_1614506 := by exact prefixLift 1614506
  have htrace : WordTrace (prefixWord ++ tailWord_1614506) baseStart_1614506 baseEnd_1614506 := by
    simpa [prefixWord, tailWord_1614506, baseEnd_1614506] using wordTrace_append hprefix tailTrace_1614506
  have hstable : (prefixWord ++ tailWord_1614506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614506).length < 2 ^ (prefixWord ++ tailWord_1614506).sum := by decide
  have hdescent : baseEnd_1614506 < baseStart_1614506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614515 : List Nat := [1, 1, 1, 2, 3, 4, 4, 6]
def baseStart_1614515 : Nat := 118140960795 + 1614515 * 2 ^ 59
def prefixEnd_1614515 : Nat := 4983230072969 + 3 ^ 40 * 1614515 * 2
def baseEnd_1614515 : Nat := 61409053251396736024999

theorem tailTrace_1614515 : CollatzResearch.WordTrace tailWord_1614515 prefixEnd_1614515 61409053251396736024999 := by
  unfold tailWord_1614515
  simp only [CollatzResearch.WordTrace]
  refine ⟨58886199745895367054548999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39257466497263578036365999 58886199745895367054548999)
  ·
    refine ⟨88329299618843050581823499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58886199745895367054548999 88329299618843050581823499)
    ·
      refine ⟨132493949428264575872735249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88329299618843050581823499 132493949428264575872735249)
      ·
        refine ⟨99370462071198431904551437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132493949428264575872735249 99370462071198431904551437)
        ·
          refine ⟨37263923276699411964206789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99370462071198431904551437 37263923276699411964206789)
          ·
            refine ⟨6986985614381139743288773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37263923276699411964206789 6986985614381139743288773)
            ·
              refine ⟨1310059802696463701866645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6986985614381139743288773 1310059802696463701866645)
              ·
                refine ⟨61409053251396736024999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1310059802696463701866645 61409053251396736024999)
                ·
                  rfl

theorem cell22_1614515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 6].length) (baseStart_1614515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614515 prefixEnd_1614515 := by exact prefixLift 1614515
  have htrace : WordTrace (prefixWord ++ tailWord_1614515) baseStart_1614515 baseEnd_1614515 := by
    simpa [prefixWord, tailWord_1614515, baseEnd_1614515] using wordTrace_append hprefix tailTrace_1614515
  have hstable : (prefixWord ++ tailWord_1614515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614515).length < 2 ^ (prefixWord ++ tailWord_1614515).sum := by decide
  have hdescent : baseEnd_1614515 < baseStart_1614515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614594 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1614594 : Nat := 118140960795 + 1614594 * 2 ^ 59
def prefixEnd_1614594 : Nat := 4983230072969 + 3 ^ 40 * 1614594 * 2
def baseEnd_1614594 : Nat := 184236174192346917166583

theorem tailTrace_1614594 : CollatzResearch.WordTrace tailWord_1614594 prefixEnd_1614594 184236174192346917166583 := by
  unfold tailWord_1614594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722270278152290886668709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39259387408406109031116557 14722270278152290886668709)
  ·
    refine ⟨2760425677153554541250383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14722270278152290886668709 2760425677153554541250383)
    ·
      refine ⟨4140638515730331811875575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760425677153554541250383 4140638515730331811875575)
      ·
        refine ⟨6210957773595497717813363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140638515730331811875575 6210957773595497717813363)
        ·
          refine ⟨9316436660393246576720045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210957773595497717813363 9316436660393246576720045)
          ·
            refine ⟨3493663747647467466270017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9316436660393246576720045 3493663747647467466270017)
            ·
              refine ⟨2620247810735600599702513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493663747647467466270017 2620247810735600599702513)
              ·
                refine ⟨1965185858051700449776885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620247810735600599702513 1965185858051700449776885)
                ·
                  refine ⟨184236174192346917166583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1965185858051700449776885 184236174192346917166583)
                  ·
                    rfl

theorem cell22_1614594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1614594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614594 prefixEnd_1614594 := by exact prefixLift 1614594
  have htrace : WordTrace (prefixWord ++ tailWord_1614594) baseStart_1614594 baseEnd_1614594 := by
    simpa [prefixWord, tailWord_1614594, baseEnd_1614594] using wordTrace_append hprefix tailTrace_1614594
  have hstable : (prefixWord ++ tailWord_1614594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614594).length < 2 ^ (prefixWord ++ tailWord_1614594).sum := by decide
  have hdescent : baseEnd_1614594 < baseStart_1614594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614680 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_1614680 : Nat := 118140960795 + 1614680 * 2 ^ 59
def prefixEnd_1614680 : Nat := 4983230072969 + 3 ^ 40 * 1614680 * 2
def baseEnd_1614680 : Nat := 552737962134565193849485

theorem tailTrace_1614680 : CollatzResearch.WordTrace tailWord_1614680 prefixEnd_1614680 552737962134565193849485 := by
  unfold tailWord_1614680
  simp only [CollatzResearch.WordTrace]
  refine ⟨29446108895148800117152747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39261478526865066822870329 29446108895148800117152747)
  ·
    refine ⟨44169163342723200175729121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29446108895148800117152747 44169163342723200175729121)
    ·
      refine ⟨33126872507042400131796841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44169163342723200175729121 33126872507042400131796841)
      ·
        refine ⟨24845154380281800098847631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33126872507042400131796841 24845154380281800098847631)
        ·
          refine ⟨37267731570422700148271447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24845154380281800098847631 37267731570422700148271447)
          ·
            refine ⟨55901597355634050222407171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37267731570422700148271447 55901597355634050222407171)
            ·
              refine ⟨83852396033451075333610757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55901597355634050222407171 83852396033451075333610757)
              ·
                refine ⟨15722324256272076625052017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83852396033451075333610757 15722324256272076625052017)
                ·
                  refine ⟨11791743192204057468789013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15722324256272076625052017 11791743192204057468789013)
                  ·
                    refine ⟨552737962134565193849485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11791743192204057468789013 552737962134565193849485)
                    ·
                      rfl

theorem cell22_1614680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_1614680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614680 prefixEnd_1614680 := by exact prefixLift 1614680
  have htrace : WordTrace (prefixWord ++ tailWord_1614680) baseStart_1614680 baseEnd_1614680 := by
    simpa [prefixWord, tailWord_1614680, baseEnd_1614680] using wordTrace_append hprefix tailTrace_1614680
  have hstable : (prefixWord ++ tailWord_1614680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614680).length < 2 ^ (prefixWord ++ tailWord_1614680).sum := by decide
  have hdescent : baseEnd_1614680 < baseStart_1614680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614684 : List Nat := [2, 2, 4, 2, 1, 1, 4, 6]
def baseStart_1614684 : Nat := 118140960795 + 1614684 * 2 ^ 59
def prefixEnd_1614684 : Nat := 4983230072969 + 3 ^ 40 * 1614684 * 2
def baseEnd_1614684 : Nat := 61415481268478946305497

theorem tailTrace_1614684 : CollatzResearch.WordTrace tailWord_1614684 prefixEnd_1614684 61415481268478946305497 := by
  unfold tailWord_1614684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29446181841141554458725553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39261575788188739278300737 29446181841141554458725553)
  ·
    refine ⟨22084636380856165844044165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29446181841141554458725553 22084636380856165844044165)
    ·
      refine ⟨4140869321410531095758281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22084636380856165844044165 4140869321410531095758281)
      ·
        refine ⟨3105651991057898321818711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4140869321410531095758281 3105651991057898321818711)
        ·
          refine ⟨4658477986586847482728067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105651991057898321818711 4658477986586847482728067)
          ·
            refine ⟨6987716979880271224092101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658477986586847482728067 6987716979880271224092101)
            ·
              refine ⟨1310196933727550854517269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6987716979880271224092101 1310196933727550854517269)
              ·
                refine ⟨61415481268478946305497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1310196933727550854517269 61415481268478946305497)
                ·
                  rfl

theorem cell22_1614684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_1614684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614684 prefixEnd_1614684 := by exact prefixLift 1614684
  have htrace : WordTrace (prefixWord ++ tailWord_1614684) baseStart_1614684 baseEnd_1614684 := by
    simpa [prefixWord, tailWord_1614684, baseEnd_1614684] using wordTrace_append hprefix tailTrace_1614684
  have hstable : (prefixWord ++ tailWord_1614684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614684).length < 2 ^ (prefixWord ++ tailWord_1614684).sum := by decide
  have hdescent : baseEnd_1614684 < baseStart_1614684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614722 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1614722 : Nat := 118140960795 + 1614722 * 2 ^ 59
def prefixEnd_1614722 : Nat := 4983230072969 + 3 ^ 40 * 1614722 * 2
def baseEnd_1614722 : Nat := 552752339592891084299357

theorem tailTrace_1614722 : CollatzResearch.WordTrace tailWord_1614722 prefixEnd_1614722 552752339592891084299357 := by
  unfold tailWord_1614722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723437414036360351833605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39262499770763627604889613 14723437414036360351833605)
  ·
    refine ⟨2760644515131817565968801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14723437414036360351833605 2760644515131817565968801)
    ·
      refine ⟨2070483386348863174476601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2760644515131817565968801 2070483386348863174476601)
      ·
        refine ⟨1552862539761647380857451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070483386348863174476601 1552862539761647380857451)
        ·
          refine ⟨2329293809642471071286177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552862539761647380857451 2329293809642471071286177)
          ·
            refine ⟨1746970357231853303464633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329293809642471071286177 1746970357231853303464633)
            ·
              refine ⟨1310227767923889977598475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746970357231853303464633 1310227767923889977598475)
              ·
                refine ⟨1965341651885834966397713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310227767923889977598475 1965341651885834966397713)
                ·
                  refine ⟨1474006238914376224798285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1965341651885834966397713 1474006238914376224798285)
                  ·
                    refine ⟨552752339592891084299357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474006238914376224798285 552752339592891084299357)
                    ·
                      rfl

theorem cell22_1614722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1614722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614722 prefixEnd_1614722 := by exact prefixLift 1614722
  have htrace : WordTrace (prefixWord ++ tailWord_1614722) baseStart_1614722 baseEnd_1614722 := by
    simpa [prefixWord, tailWord_1614722, baseEnd_1614722] using wordTrace_append hprefix tailTrace_1614722
  have hstable : (prefixWord ++ tailWord_1614722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614722).length < 2 ^ (prefixWord ++ tailWord_1614722).sum := by decide
  have hdescent : baseEnd_1614722 < baseStart_1614722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614729 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 5]
def baseStart_1614729 : Nat := 118140960795 + 1614729 * 2 ^ 59
def prefixEnd_1614729 : Nat := 4983230072969 + 3 ^ 40 * 1614729 * 2
def baseEnd_1614729 : Nat := 184251578611981799791445

theorem tailTrace_1614729 : CollatzResearch.WordTrace tailWord_1614729 prefixEnd_1614729 184251578611981799791445 := by
  unfold tailWord_1614729
  simp only [CollatzResearch.WordTrace]
  refine ⟨58894004967120081602839241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39262669978080054401892827 58894004967120081602839241)
  ·
    refine ⟨44170503725340061202129431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58894004967120081602839241 44170503725340061202129431)
    ·
      refine ⟨66255755588010091803194147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44170503725340061202129431 66255755588010091803194147)
      ·
        refine ⟨99383633382015137704791221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66255755588010091803194147 99383633382015137704791221)
        ·
          refine ⟨9317215629563919159824177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99383633382015137704791221 9317215629563919159824177)
          ·
            refine ⟨6987911722172939369868133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9317215629563919159824177 6987911722172939369868133)
            ·
              refine ⟨1310233447907426131850275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6987911722172939369868133 1310233447907426131850275)
              ·
                refine ⟨1965350171861139197775413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310233447907426131850275 1965350171861139197775413)
                ·
                  refine ⟨184251578611981799791445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1965350171861139197775413 184251578611981799791445)
                  ·
                    rfl

theorem cell22_1614729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_1614729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614729 prefixEnd_1614729 := by exact prefixLift 1614729
  have htrace : WordTrace (prefixWord ++ tailWord_1614729) baseStart_1614729 baseEnd_1614729 := by
    simpa [prefixWord, tailWord_1614729, baseEnd_1614729] using wordTrace_append hprefix tailTrace_1614729
  have hstable : (prefixWord ++ tailWord_1614729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614729).length < 2 ^ (prefixWord ++ tailWord_1614729).sum := by decide
  have hdescent : baseEnd_1614729 < baseStart_1614729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614804 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1614804 : Nat := 118140960795 + 1614804 * 2 ^ 59
def prefixEnd_1614804 : Nat := 4983230072969 + 3 ^ 40 * 1614804 * 2
def baseEnd_1614804 : Nat := 552780409868670203749105

theorem tailTrace_1614804 : CollatzResearch.WordTrace tailWord_1614804 prefixEnd_1614804 552780409868670203749105 := by
  unfold tailWord_1614804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448370220924184705909733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39264493627898912941212977 29448370220924184705909733)
  ·
    refine ⟨5521569416423284632358075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29448370220924184705909733 5521569416423284632358075)
    ·
      refine ⟨8282354124634926948537113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521569416423284632358075 8282354124634926948537113)
      ·
        refine ⟨6211765593476195211402835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8282354124634926948537113 6211765593476195211402835)
        ·
          refine ⟨9317648390214292817104253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211765593476195211402835 9317648390214292817104253)
          ·
            refine ⟨3494118146330359806414095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9317648390214292817104253 3494118146330359806414095)
            ·
              refine ⟨5241177219495539709621143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494118146330359806414095 5241177219495539709621143)
              ·
                refine ⟨7861765829243309564431715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241177219495539709621143 7861765829243309564431715)
                ·
                  refine ⟨11792648743864964346647573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861765829243309564431715 11792648743864964346647573)
                  ·
                    refine ⟨552780409868670203749105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11792648743864964346647573 552780409868670203749105)
                    ·
                      rfl

theorem cell22_1614804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1614804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614804 prefixEnd_1614804 := by exact prefixLift 1614804
  have htrace : WordTrace (prefixWord ++ tailWord_1614804) baseStart_1614804 baseEnd_1614804 := by
    simpa [prefixWord, tailWord_1614804, baseEnd_1614804] using wordTrace_append hprefix tailTrace_1614804
  have hstable : (prefixWord ++ tailWord_1614804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614804).length < 2 ^ (prefixWord ++ tailWord_1614804).sum := by decide
  have hdescent : baseEnd_1614804 < baseStart_1614804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614806 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1614806 : Nat := 118140960795 + 1614806 * 2 ^ 59
def prefixEnd_1614806 : Nat := 4983230072969 + 3 ^ 40 * 1614806 * 2
def baseEnd_1614806 : Nat := 552781094509542865199099

theorem tailTrace_1614806 : CollatzResearch.WordTrace tailWord_1614806 prefixEnd_1614806 552781094509542865199099 := by
  unfold tailWord_1614806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681050836740070234587017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39264542258560749168928181 3681050836740070234587017)
  ·
    refine ⟨2760788127555052675940263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3681050836740070234587017 2760788127555052675940263)
    ·
      refine ⟨4141182191332579013910395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760788127555052675940263 4141182191332579013910395)
      ·
        refine ⟨6211773286998868520865593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141182191332579013910395 6211773286998868520865593)
        ·
          refine ⟨4658829965249151390649195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6211773286998868520865593 4658829965249151390649195)
          ·
            refine ⟨6988244947873727085973793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658829965249151390649195 6988244947873727085973793)
            ·
              refine ⟨5241183710905295314480345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988244947873727085973793 5241183710905295314480345)
              ·
                refine ⟨3930887783178971485860259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241183710905295314480345 3930887783178971485860259)
                ·
                  refine ⟨5896331674768457228790389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930887783178971485860259 5896331674768457228790389)
                  ·
                    refine ⟨552781094509542865199099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5896331674768457228790389 552781094509542865199099)
                    ·
                      rfl

theorem cell22_1614806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1614806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614806 prefixEnd_1614806 := by exact prefixLift 1614806
  have htrace : WordTrace (prefixWord ++ tailWord_1614806) baseStart_1614806 baseEnd_1614806 := by
    simpa [prefixWord, tailWord_1614806, baseEnd_1614806] using wordTrace_append hprefix tailTrace_1614806
  have hstable : (prefixWord ++ tailWord_1614806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614806).length < 2 ^ (prefixWord ++ tailWord_1614806).sum := by decide
  have hdescent : baseEnd_1614806 < baseStart_1614806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614823 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1614823 : Nat := 118140960795 + 1614823 * 2 ^ 59
def prefixEnd_1614823 : Nat := 4983230072969 + 3 ^ 40 * 1614823 * 2
def baseEnd_1614823 : Nat := 552786913956960487524047

theorem tailTrace_1614823 : CollatzResearch.WordTrace tailWord_1614823 prefixEnd_1614823 552786913956960487524047 := by
  unfold tailWord_1614823
  simp only [CollatzResearch.WordTrace]
  refine ⟨58897433428779535656761123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39264955619186357104507415 58897433428779535656761123)
  ·
    refine ⟨88346150143169303485141685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58897433428779535656761123 88346150143169303485141685)
    ·
      refine ⟨8282451575922122201732033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88346150143169303485141685 8282451575922122201732033)
      ·
        refine ⟨6211838681941591651299025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8282451575922122201732033 6211838681941591651299025)
        ·
          refine ⟨4658879011456193738474269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6211838681941591651299025 4658879011456193738474269)
          ·
            refine ⟨1747079629296072651927851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4658879011456193738474269 1747079629296072651927851)
            ·
              refine ⟨2620619443944108977891777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747079629296072651927851 2620619443944108977891777)
              ·
                refine ⟨1965464582958081733418833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620619443944108977891777 1965464582958081733418833)
                ·
                  refine ⟨1474098437218561300064125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1965464582958081733418833 1474098437218561300064125)
                  ·
                    refine ⟨552786913956960487524047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474098437218561300064125 552786913956960487524047)
                    ·
                      rfl

theorem cell22_1614823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1614823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614823 prefixEnd_1614823 := by exact prefixLift 1614823
  have htrace : WordTrace (prefixWord ++ tailWord_1614823) baseStart_1614823 baseEnd_1614823 := by
    simpa [prefixWord, tailWord_1614823, baseEnd_1614823] using wordTrace_append hprefix tailTrace_1614823
  have hstable : (prefixWord ++ tailWord_1614823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614823).length < 2 ^ (prefixWord ++ tailWord_1614823).sum := by decide
  have hdescent : baseEnd_1614823 < baseStart_1614823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614926 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_1614926 : Nat := 118140960795 + 1614926 * 2 ^ 59
def prefixEnd_1614926 : Nat := 4983230072969 + 3 ^ 40 * 1614926 * 2
def baseEnd_1614926 : Nat := 184274057653967517399577

theorem tailTrace_1614926 : CollatzResearch.WordTrace tailWord_1614926 prefixEnd_1614926 184274057653967517399577 := by
  unfold tailWord_1614926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362648768425798030970079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39267460098270922831840421 7362648768425798030970079)
  ·
    refine ⟨11043973152638697046455119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7362648768425798030970079 11043973152638697046455119)
    ·
      refine ⟨16565959728958045569682679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043973152638697046455119 16565959728958045569682679)
      ·
        refine ⟨24848939593437068354524019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16565959728958045569682679 24848939593437068354524019)
        ·
          refine ⟨37273409390155602531786029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24848939593437068354524019 37273409390155602531786029)
          ·
            refine ⟨13977528521308350949419761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37273409390155602531786029 13977528521308350949419761)
            ·
              refine ⟨10483146390981263212064821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13977528521308350949419761 10483146390981263212064821)
              ·
                refine ⟨982794974154493426131077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10483146390981263212064821 982794974154493426131077)
                ·
                  refine ⟨184274057653967517399577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982794974154493426131077 184274057653967517399577)
                  ·
                    rfl

theorem cell22_1614926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_1614926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614926 prefixEnd_1614926 := by exact prefixLift 1614926
  have htrace : WordTrace (prefixWord ++ tailWord_1614926) baseStart_1614926 baseEnd_1614926 := by
    simpa [prefixWord, tailWord_1614926, baseEnd_1614926] using wordTrace_append hprefix tailTrace_1614926
  have hstable : (prefixWord ++ tailWord_1614926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614926).length < 2 ^ (prefixWord ++ tailWord_1614926).sum := by decide
  have hdescent : baseEnd_1614926 < baseStart_1614926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614958 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1614958 : Nat := 118140960795 + 1614958 * 2 ^ 59
def prefixEnd_1614958 : Nat := 4983230072969 + 3 ^ 40 * 1614958 * 2
def baseEnd_1614958 : Nat := 552833127215865135398633

theorem tailTrace_1614958 : CollatzResearch.WordTrace tailWord_1614958 prefixEnd_1614958 552833127215865135398633 := by
  unfold tailWord_1614958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362794660411306714115691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39268238188860302475283685 7362794660411306714115691)
  ·
    refine ⟨11044191990616960071173537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7362794660411306714115691 11044191990616960071173537)
    ·
      refine ⟨8283143992962720053380153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11044191990616960071173537 8283143992962720053380153)
      ·
        refine ⟨6212357994722040040035115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8283143992962720053380153 6212357994722040040035115)
        ·
          refine ⟨9318536992083060060052673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212357994722040040035115 9318536992083060060052673)
          ·
            refine ⟨6988902744062295045039505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9318536992083060060052673 6988902744062295045039505)
            ·
              refine ⟨5241677058046721283779629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988902744062295045039505 5241677058046721283779629)
              ·
                refine ⟨1965628896767520481417361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5241677058046721283779629 1965628896767520481417361)
                ·
                  refine ⟨1474221672575640361063021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1965628896767520481417361 1474221672575640361063021)
                  ·
                    refine ⟨552833127215865135398633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474221672575640361063021 552833127215865135398633)
                    ·
                      rfl

theorem cell22_1614958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1614958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614958 prefixEnd_1614958 := by exact prefixLift 1614958
  have htrace : WordTrace (prefixWord ++ tailWord_1614958) baseStart_1614958 baseEnd_1614958 := by
    simpa [prefixWord, tailWord_1614958, baseEnd_1614958] using wordTrace_append hprefix tailTrace_1614958
  have hstable : (prefixWord ++ tailWord_1614958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614958).length < 2 ^ (prefixWord ++ tailWord_1614958).sum := by decide
  have hdescent : baseEnd_1614958 < baseStart_1614958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614986 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_1614986 : Nat := 118140960795 + 1614986 * 2 ^ 59
def prefixEnd_1614986 : Nat := 4983230072969 + 3 ^ 40 * 1614986 * 2
def baseEnd_1614986 : Nat := 552842712188082395698547

theorem tailTrace_1614986 : CollatzResearch.WordTrace tailWord_1614986 prefixEnd_1614986 552842712188082395698547 := by
  unfold tailWord_1614986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725844631797253623736203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39268919018126009663296541 14725844631797253623736203)
  ·
    refine ⟨22088766947695880435604305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725844631797253623736203 22088766947695880435604305)
    ·
      refine ⟨16566575210771910326703229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22088766947695880435604305 16566575210771910326703229)
      ·
        refine ⟨6212465704039466372513711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16566575210771910326703229 6212465704039466372513711)
        ·
          refine ⟨9318698556059199558770567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212465704039466372513711 9318698556059199558770567)
          ·
            refine ⟨13978047834088799338155851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318698556059199558770567 13978047834088799338155851)
            ·
              refine ⟨20967071751133199007233777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13978047834088799338155851 20967071751133199007233777)
              ·
                refine ⟨15725303813349899255425333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20967071751133199007233777 15725303813349899255425333)
                ·
                  refine ⟨1474247232501553055196125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15725303813349899255425333 1474247232501553055196125)
                  ·
                    refine ⟨552842712188082395698547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474247232501553055196125 552842712188082395698547)
                    ·
                      rfl

theorem cell22_1614986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_1614986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1614986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1614986 prefixEnd_1614986 := by exact prefixLift 1614986
  have htrace : WordTrace (prefixWord ++ tailWord_1614986) baseStart_1614986 baseEnd_1614986 := by
    simpa [prefixWord, tailWord_1614986, baseEnd_1614986] using wordTrace_append hprefix tailTrace_1614986
  have hstable : (prefixWord ++ tailWord_1614986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614986).length < 2 ^ (prefixWord ++ tailWord_1614986).sum := by decide
  have hdescent : baseEnd_1614986 < baseStart_1614986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615059 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_1615059 : Nat := 118140960795 + 1615059 * 2 ^ 59
def prefixEnd_1615059 : Nat := 4983230072969 + 3 ^ 40 * 1615059 * 2
def baseEnd_1615059 : Nat := 552867701579934538623323

theorem tailTrace_1615059 : CollatzResearch.WordTrace tailWord_1615059 prefixEnd_1615059 552867701579934538623323 := by
  unfold tailWord_1615059
  simp only [CollatzResearch.WordTrace]
  refine ⟨58906041055924547962352231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39270694037283031974901487 58906041055924547962352231)
  ·
    refine ⟨88359061583886821943528347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58906041055924547962352231 88359061583886821943528347)
    ·
      refine ⟨132538592375830232915292521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88359061583886821943528347 132538592375830232915292521)
      ·
        refine ⟨99403944281872674686469391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132538592375830232915292521 99403944281872674686469391)
        ·
          refine ⟨149105916422809012029704087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99403944281872674686469391 149105916422809012029704087)
          ·
            refine ⟨223658874634213518044556131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149105916422809012029704087 223658874634213518044556131)
            ·
              refine ⟨335488311951320277066834197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223658874634213518044556131 335488311951320277066834197)
              ·
                refine ⟨15726014622718137987507853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 335488311951320277066834197 15726014622718137987507853)
                ·
                  refine ⟨5897255483519301745315445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15726014622718137987507853 5897255483519301745315445)
                  ·
                    refine ⟨552867701579934538623323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5897255483519301745315445 552867701579934538623323)
                    ·
                      rfl

theorem cell22_1615059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_1615059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615059 prefixEnd_1615059 := by exact prefixLift 1615059
  have htrace : WordTrace (prefixWord ++ tailWord_1615059) baseStart_1615059 baseEnd_1615059 := by
    simpa [prefixWord, tailWord_1615059, baseEnd_1615059] using wordTrace_append hprefix tailTrace_1615059
  have hstable : (prefixWord ++ tailWord_1615059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615059).length < 2 ^ (prefixWord ++ tailWord_1615059).sum := by decide
  have hdescent : baseEnd_1615059 < baseStart_1615059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615091 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_1615091 : Nat := 118140960795 + 1615091 * 2 ^ 59
def prefixEnd_1615091 : Nat := 4983230072969 + 3 ^ 40 * 1615091 * 2
def baseEnd_1615091 : Nat := 552878655833897121823225

theorem tailTrace_1615091 : CollatzResearch.WordTrace tailWord_1615091 prefixEnd_1615091 552878655833897121823225 := by
  unfold tailWord_1615091
  simp only [CollatzResearch.WordTrace]
  refine ⟨58907208191808617427517127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39271472127872411618344751 58907208191808617427517127)
  ·
    refine ⟨88360812287712926141275691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58907208191808617427517127 88360812287712926141275691)
    ·
      refine ⟨132541218431569389211913537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88360812287712926141275691 132541218431569389211913537)
      ·
        refine ⟨99405913823677041908935153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132541218431569389211913537 99405913823677041908935153)
        ·
          refine ⟨74554435367757781431701365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99405913823677041908935153 74554435367757781431701365)
          ·
            refine ⟨6989478315727292009222003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74554435367757781431701365 6989478315727292009222003)
            ·
              refine ⟨10484217473590938013833005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989478315727292009222003 10484217473590938013833005)
              ·
                refine ⟨3931581552596601755187377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10484217473590938013833005 3931581552596601755187377)
                ·
                  refine ⟨2948686164447451316390533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931581552596601755187377 2948686164447451316390533)
                  ·
                    refine ⟨552878655833897121823225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2948686164447451316390533 552878655833897121823225)
                    ·
                      rfl

theorem cell22_1615091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_1615091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615091 prefixEnd_1615091 := by exact prefixLift 1615091
  have htrace : WordTrace (prefixWord ++ tailWord_1615091) baseStart_1615091 baseEnd_1615091 := by
    simpa [prefixWord, tailWord_1615091, baseEnd_1615091] using wordTrace_append hprefix tailTrace_1615091
  have hstable : (prefixWord ++ tailWord_1615091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615091).length < 2 ^ (prefixWord ++ tailWord_1615091).sum := by decide
  have hdescent : baseEnd_1615091 < baseStart_1615091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615106 : List Nat := [3, 4, 1, 1, 13]
def baseStart_1615106 : Nat := 118140960795 + 1615106 * 2 ^ 59
def prefixEnd_1615106 : Nat := 4983230072969 + 3 ^ 40 * 1615106 * 2
def baseEnd_1615106 : Nat := 2275241936791942727153

theorem tailTrace_1615106 : CollatzResearch.WordTrace tailWord_1615106 prefixEnd_1615106 2275241936791942727153 := by
  unfold tailWord_1615106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726938821688568747328293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39271836857836183326208781 14726938821688568747328293)
  ·
    refine ⟨2761301029066606640124055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14726938821688568747328293 2761301029066606640124055)
    ·
      refine ⟨4141951543599909960186083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761301029066606640124055 4141951543599909960186083)
      ·
        refine ⟨6212927315399864940279125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141951543599909960186083 6212927315399864940279125)
        ·
          refine ⟨2275241936791942727153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6212927315399864940279125 2275241936791942727153)
          ·
            rfl

theorem cell22_1615106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 13].length) (baseStart_1615106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615106 prefixEnd_1615106 := by exact prefixLift 1615106
  have htrace : WordTrace (prefixWord ++ tailWord_1615106) baseStart_1615106 baseEnd_1615106 := by
    simpa [prefixWord, tailWord_1615106, baseEnd_1615106] using wordTrace_append hprefix tailTrace_1615106
  have hstable : (prefixWord ++ tailWord_1615106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615106).length < 2 ^ (prefixWord ++ tailWord_1615106).sum := by decide
  have hdescent : baseEnd_1615106 < baseStart_1615106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615108 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1615108 : Nat := 118140960795 + 1615108 * 2 ^ 59
def prefixEnd_1615108 : Nat := 4983230072969 + 3 ^ 40 * 1615108 * 2
def baseEnd_1615108 : Nat := 552884475281314744148173

theorem tailTrace_1615108 : CollatzResearch.WordTrace tailWord_1615108 prefixEnd_1615108 552884475281314744148173 := by
  unfold tailWord_1615108
  simp only [CollatzResearch.WordTrace]
  refine ⟨29453914116373514665442989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39271885488498019553923985 29453914116373514665442989)
  ·
    refine ⟨11045217793640067999541121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29453914116373514665442989 11045217793640067999541121)
    ·
      refine ⟨8283913345230050999655841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11045217793640067999541121 8283913345230050999655841)
      ·
        refine ⟨6212935008922538249741881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8283913345230050999655841 6212935008922538249741881)
        ·
          refine ⟨4659701256691903687306411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6212935008922538249741881 4659701256691903687306411)
          ·
            refine ⟨6989551885037855530959617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659701256691903687306411 6989551885037855530959617)
            ·
              refine ⟨5242163913778391648219713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989551885037855530959617 5242163913778391648219713)
              ·
                refine ⟨3931622935333793736164785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242163913778391648219713 3931622935333793736164785)
                ·
                  refine ⟨2948717201500345302123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931622935333793736164785 2948717201500345302123589)
                  ·
                    refine ⟨552884475281314744148173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2948717201500345302123589 552884475281314744148173)
                    ·
                      rfl

theorem cell22_1615108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1615108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615108 prefixEnd_1615108 := by exact prefixLift 1615108
  have htrace : WordTrace (prefixWord ++ tailWord_1615108) baseStart_1615108 baseEnd_1615108 := by
    simpa [prefixWord, tailWord_1615108, baseEnd_1615108] using wordTrace_append hprefix tailTrace_1615108
  have hstable : (prefixWord ++ tailWord_1615108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615108).length < 2 ^ (prefixWord ++ tailWord_1615108).sum := by decide
  have hdescent : baseEnd_1615108 < baseStart_1615108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615112 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_1615112 : Nat := 118140960795 + 1615112 * 2 ^ 59
def prefixEnd_1615112 : Nat := 4983230072969 + 3 ^ 40 * 1615112 * 2
def baseEnd_1615112 : Nat := 184295281521020022349387

theorem tailTrace_1615112 : CollatzResearch.WordTrace tailWord_1615112 prefixEnd_1615112 184295281521020022349387 := by
  unfold tailWord_1615112
  simp only [CollatzResearch.WordTrace]
  refine ⟨29453987062366269007015795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39271982749821692009354393 29453987062366269007015795)
  ·
    refine ⟨44180980593549403510523693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29453987062366269007015795 44180980593549403510523693)
    ·
      refine ⟨16567867722581026316446385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44180980593549403510523693 16567867722581026316446385)
      ·
        refine ⟨12425900791935769737334789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16567867722581026316446385 12425900791935769737334789)
        ·
          refine ⟨2329856398487956825750273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12425900791935769737334789 2329856398487956825750273)
          ·
            refine ⟨1747392298865967619312705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329856398487956825750273 1747392298865967619312705)
            ·
              refine ⟨1310544224149475714484529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747392298865967619312705 1310544224149475714484529)
              ·
                refine ⟨982908168112106785863397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310544224149475714484529 982908168112106785863397)
                ·
                  refine ⟨184295281521020022349387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982908168112106785863397 184295281521020022349387)
                  ·
                    rfl

theorem cell22_1615112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_1615112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615112 prefixEnd_1615112 := by exact prefixLift 1615112
  have htrace : WordTrace (prefixWord ++ tailWord_1615112) baseStart_1615112 baseEnd_1615112 := by
    simpa [prefixWord, tailWord_1615112, baseEnd_1615112] using wordTrace_append hprefix tailTrace_1615112
  have hstable : (prefixWord ++ tailWord_1615112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615112).length < 2 ^ (prefixWord ++ tailWord_1615112).sum := by decide
  have hdescent : baseEnd_1615112 < baseStart_1615112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615155 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 1, 3]
def baseStart_1615155 : Nat := 118140960795 + 1615155 * 2 ^ 59
def prefixEnd_1615155 : Nat := 4983230072969 + 3 ^ 40 * 1615155 * 2
def baseEnd_1615155 : Nat := 552900564341822288223029

theorem tailTrace_1615155 : CollatzResearch.WordTrace tailWord_1615155 prefixEnd_1615155 552900564341822288223029 := by
  unfold tailWord_1615155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58909542463576756357846919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39273028309051170905231279 58909542463576756357846919)
  ·
    refine ⟨88364313695365134536770379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58909542463576756357846919 88364313695365134536770379)
    ·
      refine ⟨132546470543047701805155569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88364313695365134536770379 132546470543047701805155569)
      ·
        refine ⟨99409852907285776353866677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132546470543047701805155569 99409852907285776353866677)
        ·
          refine ⟨9319673710058041533175001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99409852907285776353866677 9319673710058041533175001)
          ·
            refine ⟨6989755282543531149881251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319673710058041533175001 6989755282543531149881251)
            ·
              refine ⟨10484632923815296724821877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989755282543531149881251 10484632923815296724821877)
              ·
                refine ⟨982934336607684067952051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10484632923815296724821877 982934336607684067952051)
                ·
                  refine ⟨1474401504911526101928077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982934336607684067952051 1474401504911526101928077)
                  ·
                    refine ⟨552900564341822288223029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474401504911526101928077 552900564341822288223029)
                    ·
                      rfl

theorem cell22_1615155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 3].length) (baseStart_1615155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615155 prefixEnd_1615155 := by exact prefixLift 1615155
  have htrace : WordTrace (prefixWord ++ tailWord_1615155) baseStart_1615155 baseEnd_1615155 := by
    simpa [prefixWord, tailWord_1615155, baseEnd_1615155] using wordTrace_append hprefix tailTrace_1615155
  have hstable : (prefixWord ++ tailWord_1615155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615155).length < 2 ^ (prefixWord ++ tailWord_1615155).sum := by decide
  have hdescent : baseEnd_1615155 < baseStart_1615155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615172 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1615172 : Nat := 118140960795 + 1615172 * 2 ^ 59
def prefixEnd_1615172 : Nat := 4983230072969 + 3 ^ 40 * 1615172 * 2
def baseEnd_1615172 : Nat := 552906383789239910547977

theorem tailTrace_1615172 : CollatzResearch.WordTrace tailWord_1615172 prefixEnd_1615172 552906383789239910547977 := by
  unfold tailWord_1615172
  simp only [CollatzResearch.WordTrace]
  refine ⟨29455081252257584130607885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39273441669676778840810513 29455081252257584130607885)
  ·
    refine ⟨11045655469596594048977957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29455081252257584130607885 11045655469596594048977957)
    ·
      refine ⟨2071060400549361384183367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11045655469596594048977957 2071060400549361384183367)
      ·
        refine ⟨3106590600824042076275051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071060400549361384183367 3106590600824042076275051)
        ·
          refine ⟨4659885901236063114412577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106590600824042076275051 4659885901236063114412577)
          ·
            refine ⟨3494914425927047335809433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4659885901236063114412577 3494914425927047335809433)
            ·
              refine ⟨2621185819445285501857075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494914425927047335809433 2621185819445285501857075)
              ·
                refine ⟨3931778729167928252785613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621185819445285501857075 3931778729167928252785613)
                ·
                  refine ⟨1474417023437973094794605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3931778729167928252785613 1474417023437973094794605)
                  ·
                    refine ⟨552906383789239910547977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474417023437973094794605 552906383789239910547977)
                    ·
                      rfl

theorem cell22_1615172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1615172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615172 prefixEnd_1615172 := by exact prefixLift 1615172
  have htrace : WordTrace (prefixWord ++ tailWord_1615172) baseStart_1615172 baseEnd_1615172 := by
    simpa [prefixWord, tailWord_1615172, baseEnd_1615172] using wordTrace_append hprefix tailTrace_1615172
  have hstable : (prefixWord ++ tailWord_1615172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615172).length < 2 ^ (prefixWord ++ tailWord_1615172).sum := by decide
  have hdescent : baseEnd_1615172 < baseStart_1615172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
