import V185TrunkScan23Chunk0171

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1017273 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 5]
def baseStart_1017273 : Nat := 118140960795 + 1017273 * 2 ^ 59
def prefixEnd_1017273 : Nat := 4983230072969 + 3 ^ 40 * 1017273 * 2
def baseEnd_1017273 : Nat := 58038889537922627601017

theorem tailTrace_1017273 : CollatzResearch.WordTrace tailWord_1017273 prefixEnd_1017273 58038889537922627601017 := by
  unfold tailWord_1017273
  simp only [CollatzResearch.WordTrace]
  refine ⟨37102994443601132241648473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24735329629067421494432315 37102994443601132241648473)
  ·
    refine ⟨27827245832700849181236355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37102994443601132241648473 27827245832700849181236355)
    ·
      refine ⟨41740868749051273771854533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27827245832700849181236355 41740868749051273771854533)
      ·
        refine ⟨7826412890447113832222725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41740868749051273771854533 7826412890447113832222725)
        ·
          refine ⟨1467452416958833843541761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7826412890447113832222725 1467452416958833843541761)
          ·
            refine ⟨1100589312719125382656321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467452416958833843541761 1100589312719125382656321)
            ·
              refine ⟨825441984539344036992241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100589312719125382656321 825441984539344036992241)
              ·
                refine ⟨619081488404508027744181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825441984539344036992241 619081488404508027744181)
                ·
                  refine ⟨58038889537922627601017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 619081488404508027744181 58038889537922627601017)
                  ·
                    rfl

theorem cell23_1017273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 5].length) (baseStart_1017273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017273 prefixEnd_1017273 := by exact prefixLift 1017273
  have htrace : WordTrace (prefixWord ++ tailWord_1017273) baseStart_1017273 baseEnd_1017273 := by
    simpa [prefixWord, tailWord_1017273, baseEnd_1017273] using wordTrace_append hprefix tailTrace_1017273
  have hstable : (prefixWord ++ tailWord_1017273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017273).length < 2 ^ (prefixWord ++ tailWord_1017273).sum := by decide
  have hdescent : baseEnd_1017273 < baseStart_1017273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017306 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_1017306 : Nat := 118140960795 + 1017306 * 2 ^ 59
def prefixEnd_1017306 : Nat := 4983230072969 + 3 ^ 40 * 1017306 * 2
def baseEnd_1017306 : Nat := 522366950702902019296501

theorem tailTrace_1017306 : CollatzResearch.WordTrace tailWord_1017306 prefixEnd_1017306 522366950702902019296501 := by
  unfold tailWord_1017306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276049513120394719399943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24736132034987719251733181 9276049513120394719399943)
  ·
    refine ⟨13914074269680592079099915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276049513120394719399943 13914074269680592079099915)
    ·
      refine ⟨20871111404520888118649873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13914074269680592079099915 20871111404520888118649873)
      ·
        refine ⟨15653333553390666088987405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20871111404520888118649873 15653333553390666088987405)
        ·
          refine ⟨5870000082521499783370277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15653333553390666088987405 5870000082521499783370277)
          ·
            refine ⟨1100625015472781209381927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5870000082521499783370277 1100625015472781209381927)
            ·
              refine ⟨1650937523209171814072891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100625015472781209381927 1650937523209171814072891)
              ·
                refine ⟨2476406284813757721109337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650937523209171814072891 2476406284813757721109337)
                ·
                  refine ⟨1857304713610318290832003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476406284813757721109337 1857304713610318290832003)
                  ·
                    refine ⟨2785957070415477436248005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1857304713610318290832003 2785957070415477436248005)
                    ·
                      refine ⟨522366950702902019296501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2785957070415477436248005 522366950702902019296501)
                      ·
                        rfl

theorem cell23_1017306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_1017306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017306 prefixEnd_1017306 := by exact prefixLift 1017306
  have htrace : WordTrace (prefixWord ++ tailWord_1017306) baseStart_1017306 baseEnd_1017306 := by
    simpa [prefixWord, tailWord_1017306, baseEnd_1017306] using wordTrace_append hprefix tailTrace_1017306
  have hstable : (prefixWord ++ tailWord_1017306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017306).length < 2 ^ (prefixWord ++ tailWord_1017306).sum := by decide
  have hdescent : baseEnd_1017306 < baseStart_1017306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017329 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 6]
def baseStart_1017329 : Nat := 118140960795 + 1017329 * 2 ^ 59
def prefixEnd_1017329 : Nat := 4983230072969 + 3 ^ 40 * 1017329 * 2
def baseEnd_1017329 : Nat := 58042084528661714367655

theorem tailTrace_1017329 : CollatzResearch.WordTrace tailWord_1017329 prefixEnd_1017329 58042084528661714367655 := by
  unfold tailWord_1017329
  simp only [CollatzResearch.WordTrace]
  refine ⟨37105036931398253805687041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736691287598835870458027 37105036931398253805687041)
  ·
    refine ⟨27828777698548690354265281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37105036931398253805687041 27828777698548690354265281)
    ·
      refine ⟨20871583273911517765698961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27828777698548690354265281 20871583273911517765698961)
      ·
        refine ⟨15653687455433638324274221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20871583273911517765698961 15653687455433638324274221)
        ·
          refine ⟨5870132795787614371602833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15653687455433638324274221 5870132795787614371602833)
          ·
            refine ⟨4402599596840710778702125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870132795787614371602833 4402599596840710778702125)
            ·
              refine ⟨1650974848815266542013297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4402599596840710778702125 1650974848815266542013297)
              ·
                refine ⟨1238231136611449906509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650974848815266542013297 1238231136611449906509973)
                ·
                  refine ⟨58042084528661714367655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1238231136611449906509973 58042084528661714367655)
                  ·
                    rfl

theorem cell23_1017329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_1017329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017329 prefixEnd_1017329 := by exact prefixLift 1017329
  have htrace : WordTrace (prefixWord ++ tailWord_1017329) baseStart_1017329 baseEnd_1017329 := by
    simpa [prefixWord, tailWord_1017329, baseEnd_1017329] using wordTrace_append hprefix tailTrace_1017329
  have hstable : (prefixWord ++ tailWord_1017329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017329).length < 2 ^ (prefixWord ++ tailWord_1017329).sum := by decide
  have hdescent : baseEnd_1017329 < baseStart_1017329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017333 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1017333 : Nat := 118140960795 + 1017333 * 2 ^ 59
def prefixEnd_1017333 : Nat := 4983230072969 + 3 ^ 40 * 1017333 * 2
def baseEnd_1017333 : Nat := 174126938226857804552959

theorem tailTrace_1017333 : CollatzResearch.WordTrace tailWord_1017333 prefixEnd_1017333 174126938226857804552959 := by
  unfold tailWord_1017333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37105182823383762488832653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736788548922508325888435 37105182823383762488832653)
  ·
    refine ⟨13914443558768910933312245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37105182823383762488832653 13914443558768910933312245)
    ·
      refine ⟨1304479083634585399998023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13914443558768910933312245 1304479083634585399998023)
      ·
        refine ⟨1956718625451878099997035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304479083634585399998023 1956718625451878099997035)
        ·
          refine ⟨2935077938177817149995553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956718625451878099997035 2935077938177817149995553)
          ·
            refine ⟨2201308453633362862496665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2935077938177817149995553 2201308453633362862496665)
            ·
              refine ⟨1650981340225022146872499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201308453633362862496665 1650981340225022146872499)
              ·
                refine ⟨2476472010337533220308749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650981340225022146872499 2476472010337533220308749)
                ·
                  refine ⟨928677003876574957615781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2476472010337533220308749 928677003876574957615781)
                  ·
                    refine ⟨174126938226857804552959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928677003876574957615781 174126938226857804552959)
                    ·
                      rfl

theorem cell23_1017333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1017333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017333 prefixEnd_1017333 := by exact prefixLift 1017333
  have htrace : WordTrace (prefixWord ++ tailWord_1017333) baseStart_1017333 baseEnd_1017333 := by
    simpa [prefixWord, tailWord_1017333, baseEnd_1017333] using wordTrace_append hprefix tailTrace_1017333
  have hstable : (prefixWord ++ tailWord_1017333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017333).length < 2 ^ (prefixWord ++ tailWord_1017333).sum := by decide
  have hdescent : baseEnd_1017333 < baseStart_1017333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017339 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 3]
def baseStart_1017339 : Nat := 118140960795 + 1017339 * 2 ^ 59
def prefixEnd_1017339 : Nat := 4983230072969 + 3 ^ 40 * 1017339 * 2
def baseEnd_1017339 : Nat := 522383895564500390183849

theorem tailTrace_1017339 : CollatzResearch.WordTrace tailWord_1017339 prefixEnd_1017339 522383895564500390183849 := by
  unfold tailWord_1017339
  simp only [CollatzResearch.WordTrace]
  refine ⟨37105401661362025513551071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736934440908017009034047 37105401661362025513551071)
  ·
    refine ⟨55658102492043038270326607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37105401661362025513551071 55658102492043038270326607)
    ·
      refine ⟨83487153738064557405489911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55658102492043038270326607 83487153738064557405489911)
      ·
        refine ⟨125230730607096836108234867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83487153738064557405489911 125230730607096836108234867)
        ·
          refine ⟨187846095910645254162352301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125230730607096836108234867 187846095910645254162352301)
          ·
            refine ⟨70442285966491970310882113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187846095910645254162352301 70442285966491970310882113)
            ·
              refine ⟨52831714474868977733161585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70442285966491970310882113 52831714474868977733161585)
              ·
                refine ⟨39623785856151733299871189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52831714474868977733161585 39623785856151733299871189)
                ·
                  refine ⟨928682481003556249215731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39623785856151733299871189 928682481003556249215731)
                  ·
                    refine ⟨1393023721505334373823597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928682481003556249215731 1393023721505334373823597)
                    ·
                      refine ⟨522383895564500390183849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1393023721505334373823597 522383895564500390183849)
                      ·
                        rfl

theorem cell23_1017339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 3].length) (baseStart_1017339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017339 prefixEnd_1017339 := by exact prefixLift 1017339
  have htrace : WordTrace (prefixWord ++ tailWord_1017339) baseStart_1017339 baseEnd_1017339 := by
    simpa [prefixWord, tailWord_1017339, baseEnd_1017339] using wordTrace_append hprefix tailTrace_1017339
  have hstable : (prefixWord ++ tailWord_1017339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017339).length < 2 ^ (prefixWord ++ tailWord_1017339).sum := by decide
  have hdescent : baseEnd_1017339 < baseStart_1017339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017352 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1017352 : Nat := 118140960795 + 1017352 * 2 ^ 59
def prefixEnd_1017352 : Nat := 4983230072969 + 3 ^ 40 * 1017352 * 2
def baseEnd_1017352 : Nat := 522390570813008839321289

theorem tailTrace_1017352 : CollatzResearch.WordTrace tailWord_1017352 prefixEnd_1017352 522390570813008839321289 := by
  unfold tailWord_1017352
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552937905157464366887155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24737250540209952489182873 18552937905157464366887155)
  ·
    refine ⟨27829406857736196550330733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18552937905157464366887155 27829406857736196550330733)
    ·
      refine ⟨10436027571651073706374025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27829406857736196550330733 10436027571651073706374025)
      ·
        refine ⟨7827020678738305279780519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10436027571651073706374025 7827020678738305279780519)
        ·
          refine ⟨11740531018107457919670779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827020678738305279780519 11740531018107457919670779)
          ·
            refine ⟨17610796527161186879506169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740531018107457919670779 17610796527161186879506169)
            ·
              refine ⟨13208097395370890159629627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17610796527161186879506169 13208097395370890159629627)
              ·
                refine ⟨19812146093056335239444441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13208097395370890159629627 19812146093056335239444441)
                ·
                  refine ⟨14859109569792251429583331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19812146093056335239444441 14859109569792251429583331)
                  ·
                    refine ⟨22288664354688377144374997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14859109569792251429583331 22288664354688377144374997)
                    ·
                      refine ⟨522390570813008839321289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22288664354688377144374997 522390570813008839321289)
                      ·
                        rfl

theorem cell23_1017352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1017352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017352 prefixEnd_1017352 := by exact prefixLift 1017352
  have htrace : WordTrace (prefixWord ++ tailWord_1017352) baseStart_1017352 baseEnd_1017352 := by
    simpa [prefixWord, tailWord_1017352, baseEnd_1017352] using wordTrace_append hprefix tailTrace_1017352
  have hstable : (prefixWord ++ tailWord_1017352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017352).length < 2 ^ (prefixWord ++ tailWord_1017352).sum := by decide
  have hdescent : baseEnd_1017352 < baseStart_1017352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017376 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_1017376 : Nat := 118140960795 + 1017376 * 2 ^ 59
def prefixEnd_1017376 : Nat := 4983230072969 + 3 ^ 40 * 1017376 * 2
def baseEnd_1017376 : Nat := 174134298116238915140393

theorem tailTrace_1017376 : CollatzResearch.WordTrace tailWord_1017376 prefixEnd_1017376 174134298116238915140393 := by
  unfold tailWord_1017376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553375581113990416323991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24737834108151987221765321 18553375581113990416323991)
  ·
    refine ⟨27830063371670985624485987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553375581113990416323991 27830063371670985624485987)
    ·
      refine ⟨41745095057506478436728981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27830063371670985624485987 41745095057506478436728981)
      ·
        refine ⟨1956801330820616176721671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41745095057506478436728981 1956801330820616176721671)
        ·
          refine ⟨2935201996230924265082507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956801330820616176721671 2935201996230924265082507)
          ·
            refine ⟨4402802994346386397623761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935201996230924265082507 4402802994346386397623761)
            ·
              refine ⟨3302102245759789798217821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402802994346386397623761 3302102245759789798217821)
              ·
                refine ⟨1238288342159921174331683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3302102245759789798217821 1238288342159921174331683)
                ·
                  refine ⟨1857432513239881761497525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238288342159921174331683 1857432513239881761497525)
                  ·
                    refine ⟨174134298116238915140393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1857432513239881761497525 174134298116238915140393)
                    ·
                      rfl

theorem cell23_1017376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_1017376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017376 prefixEnd_1017376 := by exact prefixLift 1017376
  have htrace : WordTrace (prefixWord ++ tailWord_1017376) baseStart_1017376 baseEnd_1017376 := by
    simpa [prefixWord, tailWord_1017376, baseEnd_1017376] using wordTrace_append hprefix tailTrace_1017376
  have hstable : (prefixWord ++ tailWord_1017376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017376).length < 2 ^ (prefixWord ++ tailWord_1017376).sum := by decide
  have hdescent : baseEnd_1017376 < baseStart_1017376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017390 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1017390 : Nat := 118140960795 + 1017390 * 2 ^ 59
def prefixEnd_1017390 : Nat := 4983230072969 + 3 ^ 40 * 1017390 * 2
def baseEnd_1017390 : Nat := 522410083077879690646115

theorem tailTrace_1017390 : CollatzResearch.WordTrace tailWord_1017390 prefixEnd_1017390 522410083077879690646115 := by
  unfold tailWord_1017390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638407723022157652957203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24738174522784840815771749 4638407723022157652957203)
  ·
    refine ⟨6957611584533236479435805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4638407723022157652957203 6957611584533236479435805)
    ·
      refine ⟨2609104344199963679788427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6957611584533236479435805 2609104344199963679788427)
      ·
        refine ⟨3913656516299945519682641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609104344199963679788427 3913656516299945519682641)
        ·
          refine ⟨2935242387224959139761981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3913656516299945519682641 2935242387224959139761981)
          ·
            refine ⟨1100715895209359677410743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2935242387224959139761981 1100715895209359677410743)
            ·
              refine ⟨1651073842814039516116115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100715895209359677410743 1651073842814039516116115)
              ·
                refine ⟨2476610764221059274174173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651073842814039516116115 2476610764221059274174173)
                ·
                  refine ⟨928729036582897227815315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2476610764221059274174173 928729036582897227815315)
                  ·
                    refine ⟨1393093554874345841722973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928729036582897227815315 1393093554874345841722973)
                    ·
                      refine ⟨522410083077879690646115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1393093554874345841722973 522410083077879690646115)
                      ·
                        rfl

theorem cell23_1017390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1017390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017390 prefixEnd_1017390 := by exact prefixLift 1017390
  have htrace : WordTrace (prefixWord ++ tailWord_1017390) baseStart_1017390 baseEnd_1017390 := by
    simpa [prefixWord, tailWord_1017390, baseEnd_1017390] using wordTrace_append hprefix tailTrace_1017390
  have hstable : (prefixWord ++ tailWord_1017390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017390).length < 2 ^ (prefixWord ++ tailWord_1017390).sum := by decide
  have hdescent : baseEnd_1017390 < baseStart_1017390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017399 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1017399 : Nat := 118140960795 + 1017399 * 2 ^ 59
def prefixEnd_1017399 : Nat := 4983230072969 + 3 ^ 40 * 1017399 * 2
def baseEnd_1017399 : Nat := 522414704403770155433573

theorem tailTrace_1017399 : CollatzResearch.WordTrace tailWord_1017399 prefixEnd_1017399 522414704403770155433573 := by
  unfold tailWord_1017399
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107590041144655760735251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24738393360763103840490167 37107590041144655760735251)
  ·
    refine ⟨55661385061716983641102877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37107590041144655760735251 55661385061716983641102877)
    ·
      refine ⟨20873019398143868865413579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55661385061716983641102877 20873019398143868865413579)
      ·
        refine ⟨31309529097215803298120369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873019398143868865413579 31309529097215803298120369)
        ·
          refine ⟨23482146822911852473590277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31309529097215803298120369 23482146822911852473590277)
          ·
            refine ⟨4402902529295972338798177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23482146822911852473590277 4402902529295972338798177)
            ·
              refine ⟨3302176896971979254098633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402902529295972338798177 3302176896971979254098633)
              ·
                refine ⟨2476632672728984440573975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302176896971979254098633 2476632672728984440573975)
                ·
                  refine ⟨3714949009093476660860963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476632672728984440573975 3714949009093476660860963)
                  ·
                    refine ⟨5572423513640214991291445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3714949009093476660860963 5572423513640214991291445)
                    ·
                      refine ⟨522414704403770155433573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5572423513640214991291445 522414704403770155433573)
                      ·
                        rfl

theorem cell23_1017399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1017399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017399 prefixEnd_1017399 := by exact prefixLift 1017399
  have htrace : WordTrace (prefixWord ++ tailWord_1017399) baseStart_1017399 baseEnd_1017399 := by
    simpa [prefixWord, tailWord_1017399, baseEnd_1017399] using wordTrace_append hprefix tailTrace_1017399
  have hstable : (prefixWord ++ tailWord_1017399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017399).length < 2 ^ (prefixWord ++ tailWord_1017399).sum := by decide
  have hdescent : baseEnd_1017399 < baseStart_1017399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017409 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1017409 : Nat := 118140960795 + 1017409 * 2 ^ 59
def prefixEnd_1017409 : Nat := 4983230072969 + 3 ^ 40 * 1017409 * 2
def baseEnd_1017409 : Nat := 522419839210315116308527

theorem tailTrace_1017409 : CollatzResearch.WordTrace tailWord_1017409 prefixEnd_1017409 522419839210315116308527 := by
  unfold tailWord_1017409
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107954771108427468599281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24738636514072284979066187 37107954771108427468599281)
  ·
    refine ⟨27830966078331320601449461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37107954771108427468599281 27830966078331320601449461)
    ·
      refine ⟨2609153069843561306385887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27830966078331320601449461 2609153069843561306385887)
      ·
        refine ⟨3913729604765341959578831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609153069843561306385887 3913729604765341959578831)
        ·
          refine ⟨5870594407148012939368247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913729604765341959578831 5870594407148012939368247)
          ·
            refine ⟨8805891610722019409052371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870594407148012939368247 8805891610722019409052371)
            ·
              refine ⟨13208837416083029113578557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805891610722019409052371 13208837416083029113578557)
              ·
                refine ⟨4953314031031135917591959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13208837416083029113578557 4953314031031135917591959)
                ·
                  refine ⟨7429971046546703876387939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953314031031135917591959 7429971046546703876387939)
                  ·
                    refine ⟨11144956569820055814581909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7429971046546703876387939 11144956569820055814581909)
                    ·
                      refine ⟨522419839210315116308527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11144956569820055814581909 522419839210315116308527)
                      ·
                        rfl

theorem cell23_1017409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1017409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017409 prefixEnd_1017409 := by exact prefixLift 1017409
  have htrace : WordTrace (prefixWord ++ tailWord_1017409) baseStart_1017409 baseEnd_1017409 := by
    simpa [prefixWord, tailWord_1017409, baseEnd_1017409] using wordTrace_append hprefix tailTrace_1017409
  have hstable : (prefixWord ++ tailWord_1017409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017409).length < 2 ^ (prefixWord ++ tailWord_1017409).sum := by decide
  have hdescent : baseEnd_1017409 < baseStart_1017409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017426 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1017426 : Nat := 118140960795 + 1017426 * 2 ^ 59
def prefixEnd_1017426 : Nat := 4983230072969 + 3 ^ 40 * 1017426 * 2
def baseEnd_1017426 : Nat := 522428568381441549795949

theorem tailTrace_1017426 : CollatzResearch.WordTrace tailWord_1017426 prefixEnd_1017426 522428568381441549795949 := by
  unfold tailWord_1017426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277143703011709842992033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24739049874697892914645421 9277143703011709842992033)
  ·
    refine ⟨6957857777258782382244025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9277143703011709842992033 6957857777258782382244025)
    ·
      refine ⟨5218393332944086786683019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6957857777258782382244025 5218393332944086786683019)
      ·
        refine ⟨7827589999416130180024529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218393332944086786683019 7827589999416130180024529)
        ·
          refine ⟨5870692499562097635018397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7827589999416130180024529 5870692499562097635018397)
          ·
            refine ⟨2201509687335786613131899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870692499562097635018397 2201509687335786613131899)
            ·
              refine ⟨3302264531003679919697849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201509687335786613131899 3302264531003679919697849)
              ·
                refine ⟨2476698398252759939773387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302264531003679919697849 2476698398252759939773387)
                ·
                  refine ⟨3715047597379139909660081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476698398252759939773387 3715047597379139909660081)
                  ·
                    refine ⟨2786285698034354932245061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3715047597379139909660081 2786285698034354932245061)
                    ·
                      refine ⟨522428568381441549795949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2786285698034354932245061 522428568381441549795949)
                      ·
                        rfl

theorem cell23_1017426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1017426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017426 prefixEnd_1017426 := by exact prefixLift 1017426
  have htrace : WordTrace (prefixWord ++ tailWord_1017426) baseStart_1017426 baseEnd_1017426 := by
    simpa [prefixWord, tailWord_1017426, baseEnd_1017426] using wordTrace_append hprefix tailTrace_1017426
  have hstable : (prefixWord ++ tailWord_1017426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017426).length < 2 ^ (prefixWord ++ tailWord_1017426).sum := by decide
  have hdescent : baseEnd_1017426 < baseStart_1017426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017447 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_1017447 : Nat := 118140960795 + 1017447 * 2 ^ 59
def prefixEnd_1017447 : Nat := 4983230072969 + 3 ^ 40 * 1017447 * 2
def baseEnd_1017447 : Nat := 522439351475185967633353

theorem tailTrace_1017447 : CollatzResearch.WordTrace tailWord_1017447 prefixEnd_1017447 522439351475185967633353 := by
  unfold tailWord_1017447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109340744970759958482595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24739560496647173305655063 37109340744970759958482595)
  ·
    refine ⟨55664011117456139937723893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37109340744970759958482595 55664011117456139937723893)
    ·
      refine ⟨5218501042261513119161615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55664011117456139937723893 5218501042261513119161615)
      ·
        refine ⟨7827751563392269678742423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218501042261513119161615 7827751563392269678742423)
        ·
          refine ⟨11741627345088404518113635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827751563392269678742423 11741627345088404518113635)
          ·
            refine ⟨17612441017632606777170453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741627345088404518113635 17612441017632606777170453)
            ·
              refine ⟨825583172701528442679865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17612441017632606777170453 825583172701528442679865)
              ·
                refine ⟨619187379526146332009899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825583172701528442679865 619187379526146332009899)
                ·
                  refine ⟨928781069289219498014849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619187379526146332009899 928781069289219498014849)
                  ·
                    refine ⟨696585801966914623511137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928781069289219498014849 696585801966914623511137)
                    ·
                      refine ⟨522439351475185967633353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696585801966914623511137 522439351475185967633353)
                      ·
                        rfl

theorem cell23_1017447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_1017447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017447 prefixEnd_1017447 := by exact prefixLift 1017447
  have htrace : WordTrace (prefixWord ++ tailWord_1017447) baseStart_1017447 baseEnd_1017447 := by
    simpa [prefixWord, tailWord_1017447, baseEnd_1017447] using wordTrace_append hprefix tailTrace_1017447
  have hstable : (prefixWord ++ tailWord_1017447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017447).length < 2 ^ (prefixWord ++ tailWord_1017447).sum := by decide
  have hdescent : baseEnd_1017447 < baseStart_1017447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017453 : List Nat := [1, 5, 1, 1, 5, 1, 1, 8]
def baseStart_1017453 : Nat := 118140960795 + 1017453 * 2 ^ 59
def prefixEnd_1017453 : Nat := 4983230072969 + 3 ^ 40 * 1017453 * 2
def baseEnd_1017453 : Nat := 19349719717004183116975

theorem tailTrace_1017453 : CollatzResearch.WordTrace tailWord_1017453 prefixEnd_1017453 19349719717004183116975 := by
  unfold tailWord_1017453
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109559582949022983201013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24739706388632681988800675 37109559582949022983201013)
  ·
    refine ⟨3479021210901470904675095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37109559582949022983201013 3479021210901470904675095)
    ·
      refine ⟨5218531816352206357012643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479021210901470904675095 5218531816352206357012643)
      ·
        refine ⟨7827797724528309535518965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218531816352206357012643 7827797724528309535518965)
        ·
          refine ⟨733856036674529018954903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7827797724528309535518965 733856036674529018954903)
          ·
            refine ⟨1100784055011793528432355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733856036674529018954903 1100784055011793528432355)
            ·
              refine ⟨1651176082517690292648533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100784055011793528432355 1651176082517690292648533)
              ·
                refine ⟨19349719717004183116975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1651176082517690292648533 19349719717004183116975)
                ·
                  rfl

theorem cell23_1017453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 8].length) (baseStart_1017453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017453 prefixEnd_1017453 := by exact prefixLift 1017453
  have htrace : WordTrace (prefixWord ++ tailWord_1017453) baseStart_1017453 baseEnd_1017453 := by
    simpa [prefixWord, tailWord_1017453, baseEnd_1017453] using wordTrace_append hprefix tailTrace_1017453
  have hstable : (prefixWord ++ tailWord_1017453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017453).length < 2 ^ (prefixWord ++ tailWord_1017453).sum := by decide
  have hdescent : baseEnd_1017453 < baseStart_1017453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017473 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_1017473 : Nat := 118140960795 + 1017473 * 2 ^ 59
def prefixEnd_1017473 : Nat := 4983230072969 + 3 ^ 40 * 1017473 * 2
def baseEnd_1017473 : Nat := 522452701972202865908233

theorem tailTrace_1017473 : CollatzResearch.WordTrace tailWord_1017473 prefixEnd_1017473 522452701972202865908233 := by
  unfold tailWord_1017473
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110289042876566398929073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24740192695251044265952715 37110289042876566398929073)
  ·
    refine ⟨27832716782157424799196805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37110289042876566398929073 27832716782157424799196805)
    ·
      refine ⟨5218634396654517149849401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27832716782157424799196805 5218634396654517149849401)
      ·
        refine ⟨3913975797490887862387051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5218634396654517149849401 3913975797490887862387051)
        ·
          refine ⟨5870963696236331793580577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913975797490887862387051 5870963696236331793580577)
          ·
            refine ⟨4403222772177248845185433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870963696236331793580577 4403222772177248845185433)
            ·
              refine ⟨3302417079132936633889075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403222772177248845185433 3302417079132936633889075)
              ·
                refine ⟨4953625618699404950833613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302417079132936633889075 4953625618699404950833613)
                ·
                  refine ⟨1857609607012276856562605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4953625618699404950833613 1857609607012276856562605)
                  ·
                    refine ⟨696603602629603821210977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857609607012276856562605 696603602629603821210977)
                    ·
                      refine ⟨522452701972202865908233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696603602629603821210977 522452701972202865908233)
                      ·
                        rfl

theorem cell23_1017473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_1017473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017473 prefixEnd_1017473 := by exact prefixLift 1017473
  have htrace : WordTrace (prefixWord ++ tailWord_1017473) baseStart_1017473 baseEnd_1017473 := by
    simpa [prefixWord, tailWord_1017473, baseEnd_1017473] using wordTrace_append hprefix tailTrace_1017473
  have hstable : (prefixWord ++ tailWord_1017473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017473).length < 2 ^ (prefixWord ++ tailWord_1017473).sum := by decide
  have hdescent : baseEnd_1017473 < baseStart_1017473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017489 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_1017489 : Nat := 118140960795 + 1017489 * 2 ^ 59
def prefixEnd_1017489 : Nat := 4983230072969 + 3 ^ 40 * 1017489 * 2
def baseEnd_1017489 : Nat := 522460917662674803308159

theorem tailTrace_1017489 : CollatzResearch.WordTrace tailWord_1017489 prefixEnd_1017489 522460917662674803308159 := by
  unfold tailWord_1017489
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110872610818601131511521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24740581740545734087674347 37110872610818601131511521)
  ·
    refine ⟨27833154458113950848633641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37110872610818601131511521 27833154458113950848633641)
    ·
      refine ⟨20874865843585463136475231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27833154458113950848633641 20874865843585463136475231)
      ·
        refine ⟨31312298765378194704712847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20874865843585463136475231 31312298765378194704712847)
        ·
          refine ⟨46968448148067292057069271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31312298765378194704712847 46968448148067292057069271)
          ·
            refine ⟨70452672222100938085603907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46968448148067292057069271 70452672222100938085603907)
            ·
              refine ⟨105679008333151407128405861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70452672222100938085603907 105679008333151407128405861)
              ·
                refine ⟨19814814062465888836576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105679008333151407128405861 19814814062465888836576099)
                ·
                  refine ⟨29722221093698833254864149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19814814062465888836576099 29722221093698833254864149)
                  ·
                    refine ⟨1393229113767132808821757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29722221093698833254864149 1393229113767132808821757)
                    ·
                      refine ⟨522460917662674803308159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1393229113767132808821757 522460917662674803308159)
                      ·
                        rfl

theorem cell23_1017489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_1017489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017489 prefixEnd_1017489 := by exact prefixLift 1017489
  have htrace : WordTrace (prefixWord ++ tailWord_1017489) baseStart_1017489 baseEnd_1017489 := by
    simpa [prefixWord, tailWord_1017489, baseEnd_1017489] using wordTrace_append hprefix tailTrace_1017489
  have hstable : (prefixWord ++ tailWord_1017489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017489).length < 2 ^ (prefixWord ++ tailWord_1017489).sum := by decide
  have hdescent : baseEnd_1017489 < baseStart_1017489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017509 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 7]
def baseStart_1017509 : Nat := 118140960795 + 1017509 * 2 ^ 59
def prefixEnd_1017509 : Nat := 4983230072969 + 3 ^ 40 * 1017509 * 2
def baseEnd_1017509 : Nat := 58052354141751636117563

theorem tailTrace_1017509 : CollatzResearch.WordTrace tailWord_1017509 prefixEnd_1017509 58052354141751636117563 := by
  unfold tailWord_1017509
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111602070746144547239581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741068047164096364826387 37111602070746144547239581)
  ·
    refine ⟨13916850776529804205214843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37111602070746144547239581 13916850776529804205214843)
    ·
      refine ⟨20875276164794706307822265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13916850776529804205214843 20875276164794706307822265)
      ·
        refine ⟨15656457123596029730866699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20875276164794706307822265 15656457123596029730866699)
        ·
          refine ⟨23484685685394044596300049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656457123596029730866699 23484685685394044596300049)
          ·
            refine ⟨17613514264045533447225037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23484685685394044596300049 17613514264045533447225037)
            ·
              refine ⟨6605067849017075042709389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17613514264045533447225037 6605067849017075042709389)
              ·
                refine ⟨2476900443381403141016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6605067849017075042709389 2476900443381403141016021)
                ·
                  refine ⟨58052354141751636117563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2476900443381403141016021 58052354141751636117563)
                  ·
                    rfl

theorem cell23_1017509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_1017509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017509 prefixEnd_1017509 := by exact prefixLift 1017509
  have htrace : WordTrace (prefixWord ++ tailWord_1017509) baseStart_1017509 baseEnd_1017509 := by
    simpa [prefixWord, tailWord_1017509, baseEnd_1017509] using wordTrace_append hprefix tailTrace_1017509
  have hstable : (prefixWord ++ tailWord_1017509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017509).length < 2 ^ (prefixWord ++ tailWord_1017509).sum := by decide
  have hdescent : baseEnd_1017509 < baseStart_1017509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017539 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 8, 5]
def baseStart_1017539 : Nat := 118140960795 + 1017539 * 2 ^ 59
def prefixEnd_1017539 : Nat := 4983230072969 + 3 ^ 40 * 1017539 * 2
def baseEnd_1017539 : Nat := 174162197231799869227643

theorem tailTrace_1017539 : CollatzResearch.WordTrace tailWord_1017539 prefixEnd_1017539 174162197231799869227643 := by
  unfold tailWord_1017539
  simp only [CollatzResearch.WordTrace]
  refine ⟨37112696260637459670831671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741797507091639780554447 37112696260637459670831671)
  ·
    refine ⟨55669044390956189506247507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37112696260637459670831671 55669044390956189506247507)
    ·
      refine ⟨83503566586434284259371261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55669044390956189506247507 83503566586434284259371261)
      ·
        refine ⟨31313837469912856597264223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83503566586434284259371261 31313837469912856597264223)
        ·
          refine ⟨46970756204869284895896335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31313837469912856597264223 46970756204869284895896335)
          ·
            refine ⟨70456134307303927343844503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46970756204869284895896335 70456134307303927343844503)
            ·
              refine ⟨105684201460955891015766755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70456134307303927343844503 105684201460955891015766755)
              ·
                refine ⟨158526302191433836523650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105684201460955891015766755 158526302191433836523650133)
                ·
                  refine ⟨1857730103805865271761525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 158526302191433836523650133 1857730103805865271761525)
                  ·
                    refine ⟨174162197231799869227643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1857730103805865271761525 174162197231799869227643)
                    ·
                      rfl

theorem cell23_1017539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 5].length) (baseStart_1017539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017539 prefixEnd_1017539 := by exact prefixLift 1017539
  have htrace : WordTrace (prefixWord ++ tailWord_1017539) baseStart_1017539 baseEnd_1017539 := by
    simpa [prefixWord, tailWord_1017539, baseEnd_1017539] using wordTrace_append hprefix tailTrace_1017539
  have hstable : (prefixWord ++ tailWord_1017539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017539).length < 2 ^ (prefixWord ++ tailWord_1017539).sum := by decide
  have hdescent : baseEnd_1017539 < baseStart_1017539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017571 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1017571 : Nat := 118140960795 + 1017571 * 2 ^ 59
def prefixEnd_1017571 : Nat := 4983230072969 + 3 ^ 40 * 1017571 * 2
def baseEnd_1017571 : Nat := 522503023076343482482783

theorem tailTrace_1017571 : CollatzResearch.WordTrace tailWord_1017571 prefixEnd_1017571 522503023076343482482783 := by
  unfold tailWord_1017571
  simp only [CollatzResearch.WordTrace]
  refine ⟨37113863396521529135996567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24742575597681019423997711 37113863396521529135996567)
  ·
    refine ⟨55670795094782293703994851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37113863396521529135996567 55670795094782293703994851)
    ·
      refine ⟨83506192642173440555992277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55670795094782293703994851 83506192642173440555992277)
      ·
        refine ⟨1957176390050940013031069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 83506192642173440555992277 1957176390050940013031069)
        ·
          refine ⟨733941146269102504886651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1957176390050940013031069 733941146269102504886651)
          ·
            refine ⟨1100911719403653757329977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733941146269102504886651 1100911719403653757329977)
            ·
              refine ⟨825683789552740317997483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100911719403653757329977 825683789552740317997483)
              ·
                refine ⟨1238525684329110476996225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825683789552740317997483 1238525684329110476996225)
                ·
                  refine ⟨928894263246832857747169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238525684329110476996225 928894263246832857747169)
                  ·
                    refine ⟨696670697435124643310377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928894263246832857747169 696670697435124643310377)
                    ·
                      refine ⟨522503023076343482482783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696670697435124643310377 522503023076343482482783)
                      ·
                        rfl

theorem cell23_1017571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1017571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017571 prefixEnd_1017571 := by exact prefixLift 1017571
  have htrace : WordTrace (prefixWord ++ tailWord_1017571) baseStart_1017571 baseEnd_1017571 := by
    simpa [prefixWord, tailWord_1017571, baseEnd_1017571] using wordTrace_append hprefix tailTrace_1017571
  have hstable : (prefixWord ++ tailWord_1017571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017571).length < 2 ^ (prefixWord ++ tailWord_1017571).sum := by decide
  have hdescent : baseEnd_1017571 < baseStart_1017571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017599 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 10]
def baseStart_1017599 : Nat := 118140960795 + 1017599 * 2 ^ 59
def prefixEnd_1017599 : Nat := 4983230072969 + 3 ^ 40 * 1017599 * 2
def baseEnd_1017599 : Nat := 58057488948296596992517

theorem tailTrace_1017599 : CollatzResearch.WordTrace tailWord_1017599 prefixEnd_1017599 58057488948296596992517 := by
  unfold tailWord_1017599
  simp only [CollatzResearch.WordTrace]
  refine ⟨37114884640420089918015851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24743256426946726612010567 37114884640420089918015851)
  ·
    refine ⟨55672326960630134877023777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37114884640420089918015851 55672326960630134877023777)
    ·
      refine ⟨41754245220472601157767833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55672326960630134877023777 41754245220472601157767833)
      ·
        refine ⟨31315683915354450868325875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41754245220472601157767833 31315683915354450868325875)
        ·
          refine ⟨46973525873031676302488813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31315683915354450868325875 46973525873031676302488813)
          ·
            refine ⟨17615072202386878613433305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46973525873031676302488813 17615072202386878613433305)
            ·
              refine ⟨13211304151790158960074979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17615072202386878613433305 13211304151790158960074979)
              ·
                refine ⟨19816956227685238440112469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13211304151790158960074979 19816956227685238440112469)
                ·
                  refine ⟨58057488948296596992517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19816956227685238440112469 58057488948296596992517)
                  ·
                    rfl

theorem cell23_1017599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 10].length) (baseStart_1017599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017599 prefixEnd_1017599 := by exact prefixLift 1017599
  have htrace : WordTrace (prefixWord ++ tailWord_1017599) baseStart_1017599 baseEnd_1017599 := by
    simpa [prefixWord, tailWord_1017599, baseEnd_1017599] using wordTrace_append hprefix tailTrace_1017599
  have hstable : (prefixWord ++ tailWord_1017599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017599).length < 2 ^ (prefixWord ++ tailWord_1017599).sum := by decide
  have hdescent : baseEnd_1017599 < baseStart_1017599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017654 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1017654 : Nat := 118140960795 + 1017654 * 2 ^ 59
def prefixEnd_1017654 : Nat := 4983230072969 + 3 ^ 40 * 1017654 * 2
def baseEnd_1017654 : Nat := 174181880656888885914967

theorem tailTrace_1017654 : CollatzResearch.WordTrace tailWord_1017654 prefixEnd_1017654 174181880656888885914967 := by
  unfold tailWord_1017654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319805665951302144454251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24744593770147222874178677 2319805665951302144454251)
  ·
    refine ⟨3479708498926953216681377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319805665951302144454251 3479708498926953216681377)
    ·
      refine ⟨2609781374195214912511033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479708498926953216681377 2609781374195214912511033)
      ·
        refine ⟨1957336030646411184383275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2609781374195214912511033 1957336030646411184383275)
        ·
          refine ⟨2936004045969616776574913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957336030646411184383275 2936004045969616776574913)
          ·
            refine ⟨2202003034477212582431185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936004045969616776574913 2202003034477212582431185)
            ·
              refine ⟨1651502275857909436823389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202003034477212582431185 1651502275857909436823389)
              ·
                refine ⟨619313353446716038808771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1651502275857909436823389 619313353446716038808771)
                ·
                  refine ⟨928970030170074058213157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619313353446716038808771 928970030170074058213157)
                  ·
                    refine ⟨174181880656888885914967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928970030170074058213157 174181880656888885914967)
                    ·
                      rfl

theorem cell23_1017654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1017654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017654 prefixEnd_1017654 := by exact prefixLift 1017654
  have htrace : WordTrace (prefixWord ++ tailWord_1017654) baseStart_1017654 baseEnd_1017654 := by
    simpa [prefixWord, tailWord_1017654, baseEnd_1017654] using wordTrace_append hprefix tailTrace_1017654
  have hstable : (prefixWord ++ tailWord_1017654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017654).length < 2 ^ (prefixWord ++ tailWord_1017654).sum := by decide
  have hdescent : baseEnd_1017654 < baseStart_1017654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017670 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1017670 : Nat := 118140960795 + 1017670 * 2 ^ 59
def prefixEnd_1017670 : Nat := 4983230072969 + 3 ^ 40 * 1017670 * 2
def baseEnd_1017670 : Nat := 522553857661138595144827

theorem tailTrace_1017670 : CollatzResearch.WordTrace tailWord_1017670 prefixEnd_1017670 522553857661138595144827 := by
  unfold tailWord_1017670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159921069473839657620327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24744982815441912695900309 1159921069473839657620327)
  ·
    refine ⟨1739881604210759486430491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1159921069473839657620327 1739881604210759486430491)
    ·
      refine ⟨2609822406316139229645737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739881604210759486430491 2609822406316139229645737)
      ·
        refine ⟨1957366804737104422234303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2609822406316139229645737 1957366804737104422234303)
        ·
          refine ⟨2936050207105656633351455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957366804737104422234303 2936050207105656633351455)
          ·
            refine ⟨4404075310658484950027183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936050207105656633351455 4404075310658484950027183)
            ·
              refine ⟨6606112965987727425040775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404075310658484950027183 6606112965987727425040775)
              ·
                refine ⟨9909169448981591137561163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606112965987727425040775 9909169448981591137561163)
                ·
                  refine ⟨14863754173472386706341745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909169448981591137561163 14863754173472386706341745)
                  ·
                    refine ⟨11147815630104290029756309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14863754173472386706341745 11147815630104290029756309)
                    ·
                      refine ⟨522553857661138595144827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11147815630104290029756309 522553857661138595144827)
                      ·
                        rfl

theorem cell23_1017670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1017670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017670 prefixEnd_1017670 := by exact prefixLift 1017670
  have htrace : WordTrace (prefixWord ++ tailWord_1017670) baseStart_1017670 baseEnd_1017670 := by
    simpa [prefixWord, tailWord_1017670, baseEnd_1017670] using wordTrace_append hprefix tailTrace_1017670
  have hstable : (prefixWord ++ tailWord_1017670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017670).length < 2 ^ (prefixWord ++ tailWord_1017670).sum := by decide
  have hdescent : baseEnd_1017670 < baseStart_1017670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017677 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1017677 : Nat := 118140960795 + 1017677 * 2 ^ 59
def prefixEnd_1017677 : Nat := 4983230072969 + 3 ^ 40 * 1017677 * 2
def baseEnd_1017677 : Nat := 522557452025720067757295

theorem tailTrace_1017677 : CollatzResearch.WordTrace tailWord_1017677 prefixEnd_1017677 522557452025720067757295 := by
  unfold tailWord_1017677
  simp only [CollatzResearch.WordTrace]
  refine ⟨37117729534137509239355285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24745153022758339492903523 37117729534137509239355285)
  ·
    refine ⟨1739893571912695745594779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37117729534137509239355285 1739893571912695745594779)
    ·
      refine ⟨2609840357869043618392169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739893571912695745594779 2609840357869043618392169)
      ·
        refine ⟨1957380268401782713794127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2609840357869043618392169 1957380268401782713794127)
        ·
          refine ⟨2936070402602674070691191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957380268401782713794127 2936070402602674070691191)
          ·
            refine ⟨4404105603904011106036787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936070402602674070691191 4404105603904011106036787)
            ·
              refine ⟨6606158405856016659055181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404105603904011106036787 6606158405856016659055181)
              ·
                refine ⟨2477309402196006247145693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6606158405856016659055181 2477309402196006247145693)
                ·
                  refine ⟨928991025823502342679635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2477309402196006247145693 928991025823502342679635)
                  ·
                    refine ⟨1393486538735253514019453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 928991025823502342679635 1393486538735253514019453)
                    ·
                      refine ⟨522557452025720067757295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1393486538735253514019453 522557452025720067757295)
                      ·
                        rfl

theorem cell23_1017677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1017677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017677 prefixEnd_1017677 := by exact prefixLift 1017677
  have htrace : WordTrace (prefixWord ++ tailWord_1017677) baseStart_1017677 baseEnd_1017677 := by
    simpa [prefixWord, tailWord_1017677, baseEnd_1017677] using wordTrace_append hprefix tailTrace_1017677
  have hstable : (prefixWord ++ tailWord_1017677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017677).length < 2 ^ (prefixWord ++ tailWord_1017677).sum := by decide
  have hdescent : baseEnd_1017677 < baseStart_1017677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017710 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1017710 : Nat := 118140960795 + 1017710 * 2 ^ 59
def prefixEnd_1017710 : Nat := 4983230072969 + 3 ^ 40 * 1017710 * 2
def baseEnd_1017710 : Nat := 174191465629106146214881

theorem tailTrace_1017710 : CollatzResearch.WordTrace tailWord_1017710 prefixEnd_1017710 174191465629106146214881 := by
  unfold tailWord_1017710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639866642877244484413323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24745955428678637250204389 4639866642877244484413323)
  ·
    refine ⟨6959799964315866726619985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4639866642877244484413323 6959799964315866726619985)
    ·
      refine ⟨5219849973236900044964989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6959799964315866726619985 5219849973236900044964989)
      ·
        refine ⟨1957443739963837516861871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5219849973236900044964989 1957443739963837516861871)
        ·
          refine ⟨2936165609945756275292807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957443739963837516861871 2936165609945756275292807)
          ·
            refine ⟨4404248414918634412939211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936165609945756275292807 4404248414918634412939211)
            ·
              refine ⟨6606372622377951619408817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404248414918634412939211 6606372622377951619408817)
              ·
                refine ⟨4954779466783463714556613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606372622377951619408817 4954779466783463714556613)
                ·
                  refine ⟨929021150021899446479365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4954779466783463714556613 929021150021899446479365)
                  ·
                    refine ⟨174191465629106146214881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929021150021899446479365 174191465629106146214881)
                    ·
                      rfl

theorem cell23_1017710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1017710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017710 prefixEnd_1017710 := by exact prefixLift 1017710
  have htrace : WordTrace (prefixWord ++ tailWord_1017710) baseStart_1017710 baseEnd_1017710 := by
    simpa [prefixWord, tailWord_1017710, baseEnd_1017710] using wordTrace_append hprefix tailTrace_1017710
  have hstable : (prefixWord ++ tailWord_1017710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017710).length < 2 ^ (prefixWord ++ tailWord_1017710).sum := by decide
  have hdescent : baseEnd_1017710 < baseStart_1017710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017803 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_1017803 : Nat := 118140960795 + 1017803 * 2 ^ 59
def prefixEnd_1017803 : Nat := 4983230072969 + 3 ^ 40 * 1017803 * 2
def baseEnd_1017803 : Nat := 522622150588186574781715

theorem tailTrace_1017803 : CollatzResearch.WordTrace tailWord_1017803 prefixEnd_1017803 522622150588186574781715 := by
  unfold tailWord_1017803
  simp only [CollatzResearch.WordTrace]
  refine ⟨37122325131681032758442063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24748216754454021838961375 37122325131681032758442063)
  ·
    refine ⟨55683487697521549137663095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37122325131681032758442063 55683487697521549137663095)
    ·
      refine ⟨83525231546282323706494643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55683487697521549137663095 83525231546282323706494643)
      ·
        refine ⟨125287847319423485559741965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83525231546282323706494643 125287847319423485559741965)
        ·
          refine ⟨46982942744783807084903237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125287847319423485559741965 46982942744783807084903237)
          ·
            refine ⟨8809301764646963828419357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46982942744783807084903237 8809301764646963828419357)
            ·
              refine ⟨3303488161742611435657259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8809301764646963828419357 3303488161742611435657259)
              ·
                refine ⟨4955232242613917153485889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303488161742611435657259 4955232242613917153485889)
                ·
                  refine ⟨3716424181960437865114417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955232242613917153485889 3716424181960437865114417)
                  ·
                    refine ⟨2787318136470328398835813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716424181960437865114417 2787318136470328398835813)
                    ·
                      refine ⟨522622150588186574781715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2787318136470328398835813 522622150588186574781715)
                      ·
                        rfl

theorem cell23_1017803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_1017803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017803 prefixEnd_1017803 := by exact prefixLift 1017803
  have htrace : WordTrace (prefixWord ++ tailWord_1017803) baseStart_1017803 baseEnd_1017803 := by
    simpa [prefixWord, tailWord_1017803, baseEnd_1017803] using wordTrace_append hprefix tailTrace_1017803
  have hstable : (prefixWord ++ tailWord_1017803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017803).length < 2 ^ (prefixWord ++ tailWord_1017803).sum := by decide
  have hdescent : baseEnd_1017803 < baseStart_1017803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017807 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 2, 2, 2]
def baseStart_1017807 : Nat := 118140960795 + 1017807 * 2 ^ 59
def prefixEnd_1017807 : Nat := 4983230072969 + 3 ^ 40 * 1017807 * 2
def baseEnd_1017807 : Nat := 522624204510804559131697

theorem tailTrace_1017807 : CollatzResearch.WordTrace tailWord_1017807 prefixEnd_1017807 522624204510804559131697 := by
  unfold tailWord_1017807
  simp only [CollatzResearch.WordTrace]
  refine ⟨37122471023666541441587675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24748314015777694294391783 37122471023666541441587675)
  ·
    refine ⟨55683706535499812162381513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37122471023666541441587675 55683706535499812162381513)
    ·
      refine ⟨41762779901624859121786135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55683706535499812162381513 41762779901624859121786135)
      ·
        refine ⟨62644169852437288682679203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41762779901624859121786135 62644169852437288682679203)
        ·
          refine ⟨93966254778655933024018805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62644169852437288682679203 93966254778655933024018805)
          ·
            refine ⟨8809336385498993721001763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93966254778655933024018805 8809336385498993721001763)
            ·
              refine ⟨13214004578248490581502645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809336385498993721001763 13214004578248490581502645)
              ·
                refine ⟨1238812929210795992015873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13214004578248490581502645 1238812929210795992015873)
                ·
                  refine ⟨929109696908096994011905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238812929210795992015873 929109696908096994011905)
                  ·
                    refine ⟨696832272681072745508929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929109696908096994011905 696832272681072745508929)
                    ·
                      refine ⟨522624204510804559131697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696832272681072745508929 522624204510804559131697)
                      ·
                        rfl

theorem cell23_1017807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2, 2].length) (baseStart_1017807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017807 prefixEnd_1017807 := by exact prefixLift 1017807
  have htrace : WordTrace (prefixWord ++ tailWord_1017807) baseStart_1017807 baseEnd_1017807 := by
    simpa [prefixWord, tailWord_1017807, baseEnd_1017807] using wordTrace_append hprefix tailTrace_1017807
  have hstable : (prefixWord ++ tailWord_1017807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017807).length < 2 ^ (prefixWord ++ tailWord_1017807).sum := by decide
  have hdescent : baseEnd_1017807 < baseStart_1017807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017813 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 9]
def baseStart_1017813 : Nat := 118140960795 + 1017813 * 2 ^ 59
def prefixEnd_1017813 : Nat := 4983230072969 + 3 ^ 40 * 1017813 * 2
def baseEnd_1017813 : Nat := 58069698377192392850741

theorem tailTrace_1017813 : CollatzResearch.WordTrace tailWord_1017813 prefixEnd_1017813 58069698377192392850741 := by
  unfold tailWord_1017813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37122689861644804466306093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24748459907763202977537395 37122689861644804466306093)
  ·
    refine ⟨13921008698116801674864785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37122689861644804466306093 13921008698116801674864785)
    ·
      refine ⟨10440756523587601256148589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13921008698116801674864785 10440756523587601256148589)
      ·
        refine ⟨3915283696345350471055721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10440756523587601256148589 3915283696345350471055721)
        ·
          refine ⟨2936462772259012853291791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915283696345350471055721 2936462772259012853291791)
          ·
            refine ⟨4404694158388519279937687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936462772259012853291791 4404694158388519279937687)
            ·
              refine ⟨6607041237582778919906531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404694158388519279937687 6607041237582778919906531)
              ·
                refine ⟨9910561856374168379859797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607041237582778919906531 9910561856374168379859797)
                ·
                  refine ⟨58069698377192392850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9910561856374168379859797 58069698377192392850741)
                  ·
                    rfl

theorem cell23_1017813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_1017813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017813 prefixEnd_1017813 := by exact prefixLift 1017813
  have htrace : WordTrace (prefixWord ++ tailWord_1017813) baseStart_1017813 baseEnd_1017813 := by
    simpa [prefixWord, tailWord_1017813, baseEnd_1017813] using wordTrace_append hprefix tailTrace_1017813
  have hstable : (prefixWord ++ tailWord_1017813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017813).length < 2 ^ (prefixWord ++ tailWord_1017813).sum := by decide
  have hdescent : baseEnd_1017813 < baseStart_1017813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017841 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_1017841 : Nat := 118140960795 + 1017841 * 2 ^ 59
def prefixEnd_1017841 : Nat := 4983230072969 + 3 ^ 40 * 1017841 * 2
def baseEnd_1017841 : Nat := 522641662853057426106541

theorem tailTrace_1017841 : CollatzResearch.WordTrace tailWord_1017841 prefixEnd_1017841 522641662853057426106541 := by
  unfold tailWord_1017841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37123711105543365248325377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24749140737028910165550251 37123711105543365248325377)
  ·
    refine ⟨27842783329157523936244033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37123711105543365248325377 27842783329157523936244033)
    ·
      refine ⟨20882087496868142952183025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27842783329157523936244033 20882087496868142952183025)
      ·
        refine ⟨15661565622651107214137269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20882087496868142952183025 15661565622651107214137269)
        ·
          refine ⟨1468271777123541301325369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15661565622651107214137269 1468271777123541301325369)
          ·
            refine ⟨1101203832842655975994027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468271777123541301325369 1101203832842655975994027)
            ·
              refine ⟨1651805749263983963991041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101203832842655975994027 1651805749263983963991041)
              ·
                refine ⟨1238854311947987972993281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651805749263983963991041 1238854311947987972993281)
                ·
                  refine ⟨929140733960990979744961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238854311947987972993281 929140733960990979744961)
                  ·
                    refine ⟨696855550470743234808721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929140733960990979744961 696855550470743234808721)
                    ·
                      refine ⟨522641662853057426106541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696855550470743234808721 522641662853057426106541)
                      ·
                        rfl

theorem cell23_1017841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_1017841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017841 prefixEnd_1017841 := by exact prefixLift 1017841
  have htrace : WordTrace (prefixWord ++ tailWord_1017841) baseStart_1017841 baseEnd_1017841 := by
    simpa [prefixWord, tailWord_1017841, baseEnd_1017841] using wordTrace_append hprefix tailTrace_1017841
  have hstable : (prefixWord ++ tailWord_1017841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017841).length < 2 ^ (prefixWord ++ tailWord_1017841).sum := by decide
  have hdescent : baseEnd_1017841 < baseStart_1017841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017843 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 2, 5]
def baseStart_1017843 : Nat := 118140960795 + 1017843 * 2 ^ 59
def prefixEnd_1017843 : Nat := 4983230072969 + 3 ^ 40 * 1017843 * 2
def baseEnd_1017843 : Nat := 174214229938122139427177

theorem tailTrace_1017843 : CollatzResearch.WordTrace tailWord_1017843 prefixEnd_1017843 174214229938122139427177 := by
  unfold tailWord_1017843
  simp only [CollatzResearch.WordTrace]
  refine ⟨37123784051536119589898183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24749189367690746393265455 37123784051536119589898183)
  ·
    refine ⟨55685676077304179384847275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37123784051536119589898183 55685676077304179384847275)
    ·
      refine ⟨83528514115956269077270913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55685676077304179384847275 83528514115956269077270913)
      ·
        refine ⟨62646385586967201807953185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83528514115956269077270913 62646385586967201807953185)
        ·
          refine ⟨46984789190225401355964889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62646385586967201807953185 46984789190225401355964889)
          ·
            refine ⟨35238591892669051016973667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46984789190225401355964889 35238591892669051016973667)
            ·
              refine ⟨52857887839003576525460501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35238591892669051016973667 52857887839003576525460501)
              ·
                refine ⟨2477713492453292649630961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52857887839003576525460501 2477713492453292649630961)
                ·
                  refine ⟨1858285119339969487223221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477713492453292649630961 1858285119339969487223221)
                  ·
                    refine ⟨174214229938122139427177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1858285119339969487223221 174214229938122139427177)
                    ·
                      rfl

theorem cell23_1017843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 5].length) (baseStart_1017843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017843 prefixEnd_1017843 := by exact prefixLift 1017843
  have htrace : WordTrace (prefixWord ++ tailWord_1017843) baseStart_1017843 baseEnd_1017843 := by
    simpa [prefixWord, tailWord_1017843, baseEnd_1017843] using wordTrace_append hprefix tailTrace_1017843
  have hstable : (prefixWord ++ tailWord_1017843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017843).length < 2 ^ (prefixWord ++ tailWord_1017843).sum := by decide
  have hdescent : baseEnd_1017843 < baseStart_1017843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017853 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1017853 : Nat := 118140960795 + 1017853 * 2 ^ 59
def prefixEnd_1017853 : Nat := 4983230072969 + 3 ^ 40 * 1017853 * 2
def baseEnd_1017853 : Nat := 522647824620911379156485

theorem tailTrace_1017853 : CollatzResearch.WordTrace tailWord_1017853 prefixEnd_1017853 522647824620911379156485 := by
  unfold tailWord_1017853
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124148781499891297762213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24749432520999927531841475 37124148781499891297762213)
  ·
    refine ⟨6960777896531229618330415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37124148781499891297762213 6960777896531229618330415)
    ·
      refine ⟨10441166844796844427495623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6960777896531229618330415 10441166844796844427495623)
      ·
        refine ⟨15661750267195266641243435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10441166844796844427495623 15661750267195266641243435)
        ·
          refine ⟨23492625400792899961865153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15661750267195266641243435 23492625400792899961865153)
          ·
            refine ⟨17619469050594674971398865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23492625400792899961865153 17619469050594674971398865)
            ·
              refine ⟨13214601787946006228549149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17619469050594674971398865 13214601787946006228549149)
              ·
                refine ⟨4955475670479752335705931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13214601787946006228549149 4955475670479752335705931)
                ·
                  refine ⟨7433213505719628503558897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955475670479752335705931 7433213505719628503558897)
                  ·
                    refine ⟨5574910129289721377669173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433213505719628503558897 5574910129289721377669173)
                    ·
                      refine ⟨522647824620911379156485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5574910129289721377669173 522647824620911379156485)
                      ·
                        rfl

theorem cell23_1017853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1017853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017853 prefixEnd_1017853 := by exact prefixLift 1017853
  have htrace : WordTrace (prefixWord ++ tailWord_1017853) baseStart_1017853 baseEnd_1017853 := by
    simpa [prefixWord, tailWord_1017853, baseEnd_1017853] using wordTrace_append hprefix tailTrace_1017853
  have hstable : (prefixWord ++ tailWord_1017853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017853).length < 2 ^ (prefixWord ++ tailWord_1017853).sum := by decide
  have hdescent : baseEnd_1017853 < baseStart_1017853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017880 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1017880 : Nat := 118140960795 + 1017880 * 2 ^ 59
def prefixEnd_1017880 : Nat := 4983230072969 + 3 ^ 40 * 1017880 * 2
def baseEnd_1017880 : Nat := 522661688598582773518861

theorem tailTrace_1017880 : CollatzResearch.WordTrace tailWord_1017880 prefixEnd_1017880 522661688598582773518861 := by
  unfold tailWord_1017880
  simp only [CollatzResearch.WordTrace]
  refine ⟨18562566776201037454497547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24750089034934716605996729 18562566776201037454497547)
  ·
    refine ⟨27843850164301556181746321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18562566776201037454497547 27843850164301556181746321)
    ·
      refine ⟨20882887623226167136309741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27843850164301556181746321 20882887623226167136309741)
      ·
        refine ⟨7831082858709812676116153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20882887623226167136309741 7831082858709812676116153)
        ·
          refine ⟨5873312144032359507087115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831082858709812676116153 5873312144032359507087115)
          ·
            refine ⟨8809968216048539260630673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873312144032359507087115 8809968216048539260630673)
            ·
              refine ⟨6607476162036404445473005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8809968216048539260630673 6607476162036404445473005)
              ·
                refine ⟨2477803560763651667052377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6607476162036404445473005 2477803560763651667052377)
                ·
                  refine ⟨1858352670572738750289283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477803560763651667052377 1858352670572738750289283)
                  ·
                    refine ⟨2787529005859108125433925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858352670572738750289283 2787529005859108125433925)
                    ·
                      refine ⟨522661688598582773518861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2787529005859108125433925 522661688598582773518861)
                      ·
                        rfl

theorem cell23_1017880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1017880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017880 prefixEnd_1017880 := by exact prefixLift 1017880
  have htrace : WordTrace (prefixWord ++ tailWord_1017880) baseStart_1017880 baseEnd_1017880 := by
    simpa [prefixWord, tailWord_1017880, baseEnd_1017880] using wordTrace_append hprefix tailTrace_1017880
  have hstable : (prefixWord ++ tailWord_1017880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017880).length < 2 ^ (prefixWord ++ tailWord_1017880).sum := by decide
  have hdescent : baseEnd_1017880 < baseStart_1017880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017907 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 1, 4]
def baseStart_1017907 : Nat := 118140960795 + 1017907 * 2 ^ 59
def prefixEnd_1017907 : Nat := 4983230072969 + 3 ^ 40 * 1017907 * 2
def baseEnd_1017907 : Nat := 174225184192084722627079

theorem tailTrace_1017907 : CollatzResearch.WordTrace tailWord_1017907 prefixEnd_1017907 174225184192084722627079 := by
  unfold tailWord_1017907
  simp only [CollatzResearch.WordTrace]
  refine ⟨37126118323304258520227975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24750745548869505680151983 37126118323304258520227975)
  ·
    refine ⟨55689177484956387780341963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37126118323304258520227975 55689177484956387780341963)
    ·
      refine ⟨83533766227434581670512945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55689177484956387780341963 83533766227434581670512945)
      ·
        refine ⟨62650324670575936252884709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83533766227434581670512945 62650324670575936252884709)
        ·
          refine ⟨11746935875732988047415883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62650324670575936252884709 11746935875732988047415883)
          ·
            refine ⟨17620403813599482071123825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746935875732988047415883 17620403813599482071123825)
            ·
              refine ⟨13215302860199611553342869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620403813599482071123825 13215302860199611553342869)
              ·
                refine ⟨619467321571856791562947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13215302860199611553342869 619467321571856791562947)
                ·
                  refine ⟨929200982357785187344421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619467321571856791562947 929200982357785187344421)
                  ·
                    refine ⟨174225184192084722627079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929200982357785187344421 174225184192084722627079)
                    ·
                      rfl

theorem cell23_1017907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 4].length) (baseStart_1017907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017907 prefixEnd_1017907 := by exact prefixLift 1017907
  have htrace : WordTrace (prefixWord ++ tailWord_1017907) baseStart_1017907 baseEnd_1017907 := by
    simpa [prefixWord, tailWord_1017907, baseEnd_1017907] using wordTrace_append hprefix tailTrace_1017907
  have hstable : (prefixWord ++ tailWord_1017907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017907).length < 2 ^ (prefixWord ++ tailWord_1017907).sum := by decide
  have hdescent : baseEnd_1017907 < baseStart_1017907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017920 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 6]
def baseStart_1017920 : Nat := 118140960795 + 1017920 * 2 ^ 59
def prefixEnd_1017920 : Nat := 4983230072969 + 3 ^ 40 * 1017920 * 2
def baseEnd_1017920 : Nat := 58075803091640290779853

theorem tailTrace_1017920 : CollatzResearch.WordTrace tailWord_1017920 prefixEnd_1017920 58075803091640290779853 := by
  unfold tailWord_1017920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18563296236128580870225607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24751061648171441160300809 18563296236128580870225607)
  ·
    refine ⟨27844944354192871305338411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18563296236128580870225607 27844944354192871305338411)
    ·
      refine ⟨41767416531289306958007617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27844944354192871305338411 41767416531289306958007617)
      ·
        refine ⟨31325562398466980218505713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41767416531289306958007617 31325562398466980218505713)
        ·
          refine ⟨23494171798850235163879285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31325562398466980218505713 23494171798850235163879285)
          ·
            refine ⟨2202578606142209546613683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23494171798850235163879285 2202578606142209546613683)
            ·
              refine ⟨3303867909213314319920525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202578606142209546613683 3303867909213314319920525)
              ·
                refine ⟨1238950465954992869970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3303867909213314319920525 1238950465954992869970197)
                ·
                  refine ⟨58075803091640290779853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1238950465954992869970197 58075803091640290779853)
                  ·
                    rfl

theorem cell23_1017920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_1017920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017920 prefixEnd_1017920 := by exact prefixLift 1017920
  have htrace : WordTrace (prefixWord ++ tailWord_1017920) baseStart_1017920 baseEnd_1017920 := by
    simpa [prefixWord, tailWord_1017920, baseEnd_1017920] using wordTrace_append hprefix tailTrace_1017920
  have hstable : (prefixWord ++ tailWord_1017920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017920).length < 2 ^ (prefixWord ++ tailWord_1017920).sum := by decide
  have hdescent : baseEnd_1017920 < baseStart_1017920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017954 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1017954 : Nat := 118140960795 + 1017954 * 2 ^ 59
def prefixEnd_1017954 : Nat := 4983230072969 + 3 ^ 40 * 1017954 * 2
def baseEnd_1017954 : Nat := 58077742907446164888169

theorem tailTrace_1017954 : CollatzResearch.WordTrace tailWord_1017954 prefixEnd_1017954 58077742907446164888169 := by
  unfold tailWord_1017954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281958138533496386797229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24751888369422657031459277 9281958138533496386797229)
  ·
    refine ⟨3480734301950061145048961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9281958138533496386797229 3480734301950061145048961)
    ·
      refine ⟨2610550726462545858786721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3480734301950061145048961 2610550726462545858786721)
      ·
        refine ⟨1957913044846909394090041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610550726462545858786721 1957913044846909394090041)
        ·
          refine ⟨1468434783635182045567531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1957913044846909394090041 1468434783635182045567531)
          ·
            refine ⟨2202652175452773068351297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468434783635182045567531 2202652175452773068351297)
            ·
              refine ⟨1651989131589579801263473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202652175452773068351297 1651989131589579801263473)
              ·
                refine ⟨1238991848692184850947605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651989131589579801263473 1238991848692184850947605)
                ·
                  refine ⟨58077742907446164888169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1238991848692184850947605 58077742907446164888169)
                  ·
                    rfl

theorem cell23_1017954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1017954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017954 prefixEnd_1017954 := by exact prefixLift 1017954
  have htrace : WordTrace (prefixWord ++ tailWord_1017954) baseStart_1017954 baseEnd_1017954 := by
    simpa [prefixWord, tailWord_1017954, baseEnd_1017954] using wordTrace_append hprefix tailTrace_1017954
  have hstable : (prefixWord ++ tailWord_1017954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017954).length < 2 ^ (prefixWord ++ tailWord_1017954).sum := by decide
  have hdescent : baseEnd_1017954 < baseStart_1017954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017980 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1017980 : Nat := 118140960795 + 1017980 * 2 ^ 59
def prefixEnd_1017980 : Nat := 4983230072969 + 3 ^ 40 * 1017980 * 2
def baseEnd_1017980 : Nat := 174237678888010794089467

theorem tailTrace_1017980 : CollatzResearch.WordTrace tailWord_1017980 prefixEnd_1017980 174237678888010794089467 := by
  unfold tailWord_1017980
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564390426019895993817697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24752520568026527991756929 18564390426019895993817697)
  ·
    refine ⟨13923292819514921995363273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18564390426019895993817697 13923292819514921995363273)
    ·
      refine ⟨10442469614636191496522455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13923292819514921995363273 10442469614636191496522455)
      ·
        refine ⟨15663704421954287244783683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442469614636191496522455 15663704421954287244783683)
        ·
          refine ⟨23495556632931430867175525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663704421954287244783683 23495556632931430867175525)
          ·
            refine ⟨4405416868674643287595411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23495556632931430867175525 4405416868674643287595411)
            ·
              refine ⟨6608125303011964931393117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405416868674643287595411 6608125303011964931393117)
              ·
                refine ⟨2478046988629486849272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608125303011964931393117 2478046988629486849272419)
                ·
                  refine ⟨3717070482944230273908629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478046988629486849272419 3717070482944230273908629)
                  ·
                    refine ⟨174237678888010794089467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3717070482944230273908629 174237678888010794089467)
                    ·
                      rfl

theorem cell23_1017980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1017980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017980 prefixEnd_1017980 := by exact prefixLift 1017980
  have htrace : WordTrace (prefixWord ++ tailWord_1017980) baseStart_1017980 baseEnd_1017980 := by
    simpa [prefixWord, tailWord_1017980, baseEnd_1017980] using wordTrace_append hprefix tailTrace_1017980
  have hstable : (prefixWord ++ tailWord_1017980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017980).length < 2 ^ (prefixWord ++ tailWord_1017980).sum := by decide
  have hdescent : baseEnd_1017980 < baseStart_1017980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017998 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1017998 : Nat := 118140960795 + 1017998 * 2 ^ 59
def prefixEnd_1017998 : Nat := 4983230072969 + 3 ^ 40 * 1017998 * 2
def baseEnd_1017998 : Nat := 522722279315813311843319

theorem tailTrace_1017998 : CollatzResearch.WordTrace tailWord_1017998 prefixEnd_1017998 522722279315813311843319 := by
  unfold tailWord_1017998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641179670746822632723831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24752958243983054041193765 4641179670746822632723831)
  ·
    refine ⟨6961769506120233949085747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641179670746822632723831 6961769506120233949085747)
    ·
      refine ⟨10442654259180350923628621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961769506120233949085747 10442654259180350923628621)
      ·
        refine ⟨3915995347192631596360733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10442654259180350923628621 3915995347192631596360733)
        ·
          refine ⟨1468498255197236848635275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3915995347192631596360733 1468498255197236848635275)
          ·
            refine ⟨2202747382795855272952913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468498255197236848635275 2202747382795855272952913)
            ·
              refine ⟨1652060537096891454714685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202747382795855272952913 1652060537096891454714685)
              ·
                refine ⟨619522701411334295518007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1652060537096891454714685 619522701411334295518007)
                ·
                  refine ⟨929284052117001443277011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619522701411334295518007 929284052117001443277011)
                  ·
                    refine ⟨1393926078175502164915517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 929284052117001443277011 1393926078175502164915517)
                    ·
                      refine ⟨522722279315813311843319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1393926078175502164915517 522722279315813311843319)
                      ·
                        rfl

theorem cell23_1017998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1017998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1017998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1017998 prefixEnd_1017998 := by exact prefixLift 1017998
  have htrace : WordTrace (prefixWord ++ tailWord_1017998) baseStart_1017998 baseEnd_1017998 := by
    simpa [prefixWord, tailWord_1017998, baseEnd_1017998] using wordTrace_append hprefix tailTrace_1017998
  have hstable : (prefixWord ++ tailWord_1017998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017998).length < 2 ^ (prefixWord ++ tailWord_1017998).sum := by decide
  have hdescent : baseEnd_1017998 < baseStart_1017998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018000 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_1018000 : Nat := 118140960795 + 1018000 * 2 ^ 59
def prefixEnd_1018000 : Nat := 4983230072969 + 3 ^ 40 * 1018000 * 2
def baseEnd_1018000 : Nat := 522723306277122304018309

theorem tailTrace_1018000 : CollatzResearch.WordTrace tailWord_1018000 prefixEnd_1018000 522723306277122304018309 := by
  unfold tailWord_1018000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564755155983667701681727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24753006874644890268908969 18564755155983667701681727)
  ·
    refine ⟨27847132733975501552522591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18564755155983667701681727 27847132733975501552522591)
    ·
      refine ⟨41770699100963252328783887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27847132733975501552522591 41770699100963252328783887)
      ·
        refine ⟨62656048651444878493175831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41770699100963252328783887 62656048651444878493175831)
        ·
          refine ⟨93984072977167317739763747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62656048651444878493175831 93984072977167317739763747)
          ·
            refine ⟨140976109465750976609645621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93984072977167317739763747 140976109465750976609645621)
            ·
              refine ⟨13216510262414154057154277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140976109465750976609645621 13216510262414154057154277)
              ·
                refine ⟨2478095674202653885716427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13216510262414154057154277 2478095674202653885716427)
                ·
                  refine ⟨3717143511303980828574641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478095674202653885716427 3717143511303980828574641)
                  ·
                    refine ⟨2787857633477985621430981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3717143511303980828574641 2787857633477985621430981)
                    ·
                      refine ⟨522723306277122304018309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2787857633477985621430981 522723306277122304018309)
                      ·
                        rfl

theorem cell23_1018000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_1018000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018000 prefixEnd_1018000 := by exact prefixLift 1018000
  have htrace : WordTrace (prefixWord ++ tailWord_1018000) baseStart_1018000 baseEnd_1018000 := by
    simpa [prefixWord, tailWord_1018000, baseEnd_1018000] using wordTrace_append hprefix tailTrace_1018000
  have hstable : (prefixWord ++ tailWord_1018000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018000).length < 2 ^ (prefixWord ++ tailWord_1018000).sum := by decide
  have hdescent : baseEnd_1018000 < baseStart_1018000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018021 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 1, 2, 2]
def baseStart_1018021 : Nat := 118140960795 + 1018021 * 2 ^ 59
def prefixEnd_1018021 : Nat := 4983230072969 + 3 ^ 40 * 1018021 * 2
def baseEnd_1018021 : Nat := 522734089370866721855713

theorem tailTrace_1018021 : CollatzResearch.WordTrace tailWord_1018021 prefixEnd_1018021 522734089370866721855713 := by
  unfold tailWord_1018021
  simp only [CollatzResearch.WordTrace]
  refine ⟨37130276244891255989877917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24753517496594170659918611 37130276244891255989877917)
  ·
    refine ⟨13923853591834220996204219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37130276244891255989877917 13923853591834220996204219)
    ·
      refine ⟨20885780387751331494306329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923853591834220996204219 20885780387751331494306329)
      ·
        refine ⟨15664335290813498620729747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20885780387751331494306329 15664335290813498620729747)
        ·
          refine ⟨23496502936220247931094621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15664335290813498620729747 23496502936220247931094621)
          ·
            refine ⟨8811188601082592974160483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23496502936220247931094621 8811188601082592974160483)
            ·
              refine ⟨13216782901623889461240725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811188601082592974160483 13216782901623889461240725)
              ·
                refine ⟨619536698513619818495659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13216782901623889461240725 619536698513619818495659)
                ·
                  refine ⟨929305047770429727743489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619536698513619818495659 929305047770429727743489)
                  ·
                    refine ⟨696978785827822295807617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929305047770429727743489 696978785827822295807617)
                    ·
                      refine ⟨522734089370866721855713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 696978785827822295807617 522734089370866721855713)
                      ·
                        rfl

theorem cell23_1018021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_1018021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018021 prefixEnd_1018021 := by exact prefixLift 1018021
  have htrace : WordTrace (prefixWord ++ tailWord_1018021) baseStart_1018021 baseEnd_1018021 := by
    simpa [prefixWord, tailWord_1018021, baseEnd_1018021] using wordTrace_append hprefix tailTrace_1018021
  have hstable : (prefixWord ++ tailWord_1018021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018021).length < 2 ^ (prefixWord ++ tailWord_1018021).sum := by decide
  have hdescent : baseEnd_1018021 < baseStart_1018021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018044 : List Nat := [2, 2, 2, 3, 3, 2, 2, 7]
def baseStart_1018044 : Nat := 118140960795 + 1018044 * 2 ^ 59
def prefixEnd_1018044 : Nat := 4983230072969 + 3 ^ 40 * 1018044 * 2
def baseEnd_1018044 : Nat := 19360959237997041921041

theorem tailTrace_1018044 : CollatzResearch.WordTrace tailWord_1018044 prefixEnd_1018044 19360959237997041921041 := by
  unfold tailWord_1018044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565557561903965458982593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24754076749205287278643457 18565557561903965458982593)
  ·
    refine ⟨13924168171427974094236945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18565557561903965458982593 13924168171427974094236945)
    ·
      refine ⟨10443126128570980570677709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13924168171427974094236945 10443126128570980570677709)
      ·
        refine ⟨3916172298214117714004141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10443126128570980570677709 3916172298214117714004141)
        ·
          refine ⟨1468564611830294142751553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3916172298214117714004141 1468564611830294142751553)
          ·
            refine ⟨1101423458872720607063665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468564611830294142751553 1101423458872720607063665)
            ·
              refine ⟨826067594154540455297749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101423458872720607063665 826067594154540455297749)
              ·
                refine ⟨19360959237997041921041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 826067594154540455297749 19360959237997041921041)
                ·
                  rfl

theorem cell23_1018044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 7].length) (baseStart_1018044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018044 prefixEnd_1018044 := by exact prefixLift 1018044
  have htrace : WordTrace (prefixWord ++ tailWord_1018044) baseStart_1018044 baseEnd_1018044 := by
    simpa [prefixWord, tailWord_1018044, baseEnd_1018044] using wordTrace_append hprefix tailTrace_1018044
  have hstable : (prefixWord ++ tailWord_1018044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018044).length < 2 ^ (prefixWord ++ tailWord_1018044).sum := by decide
  have hdescent : baseEnd_1018044 < baseStart_1018044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018080 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1018080 : Nat := 118140960795 + 1018080 * 2 ^ 59
def prefixEnd_1018080 : Nat := 4983230072969 + 3 ^ 40 * 1018080 * 2
def baseEnd_1018080 : Nat := 522764384729481991017941

theorem tailTrace_1018080 : CollatzResearch.WordTrace tailWord_1018080 prefixEnd_1018080 522764384729481991017941 := by
  unfold tailWord_1018080
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566214075838754533137847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24754952101118339377517129 18566214075838754533137847)
  ·
    refine ⟨27849321113758131799706771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18566214075838754533137847 27849321113758131799706771)
    ·
      refine ⟨41773981670637197699560157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27849321113758131799706771 41773981670637197699560157)
      ·
        refine ⟨15665243126488949137335059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41773981670637197699560157 15665243126488949137335059)
        ·
          refine ⟨23497864689733423706002589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15665243126488949137335059 23497864689733423706002589)
          ·
            refine ⟨8811699258650033889750971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23497864689733423706002589 8811699258650033889750971)
            ·
              refine ⟨13217548887975050834626457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811699258650033889750971 13217548887975050834626457)
              ·
                refine ⟨9913161665981288125969843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13217548887975050834626457 9913161665981288125969843)
                ·
                  refine ⟨14869742498971932188954765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913161665981288125969843 14869742498971932188954765)
                  ·
                    refine ⟨5576153437114474570858037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14869742498971932188954765 5576153437114474570858037)
                    ·
                      refine ⟨522764384729481991017941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5576153437114474570858037 522764384729481991017941)
                      ·
                        rfl

theorem cell23_1018080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1018080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018080 prefixEnd_1018080 := by exact prefixLift 1018080
  have htrace : WordTrace (prefixWord ++ tailWord_1018080) baseStart_1018080 baseEnd_1018080 := by
    simpa [prefixWord, tailWord_1018080, baseEnd_1018080] using wordTrace_append hprefix tailTrace_1018080
  have hstable : (prefixWord ++ tailWord_1018080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018080).length < 2 ^ (prefixWord ++ tailWord_1018080).sum := by decide
  have hdescent : baseEnd_1018080 < baseStart_1018080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018082 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1018082 : Nat := 118140960795 + 1018082 * 2 ^ 59
def prefixEnd_1018082 : Nat := 4983230072969 + 3 ^ 40 * 1018082 * 2
def baseEnd_1018082 : Nat := 174255137230263661064311

theorem tailTrace_1018082 : CollatzResearch.WordTrace tailWord_1018082 prefixEnd_1018082 174255137230263661064311 := by
  unfold tailWord_1018082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283125274417565851962125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24755000731780175605232333 9283125274417565851962125)
  ·
    refine ⟨3481171977906587194485797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9283125274417565851962125 3481171977906587194485797)
    ·
      refine ⟨652719745857485098966087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3481171977906587194485797 652719745857485098966087)
      ·
        refine ⟨979079618786227648449131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652719745857485098966087 979079618786227648449131)
        ·
          refine ⟨1468619428179341472673697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979079618786227648449131 1468619428179341472673697)
          ·
            refine ⟨1101464571134506104505273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468619428179341472673697 1101464571134506104505273)
            ·
              refine ⟨826098428350879578378955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101464571134506104505273 826098428350879578378955)
              ·
                refine ⟨1239147642526319367568433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826098428350879578378955 1239147642526319367568433)
                ·
                  refine ⟨929360731894739525676325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239147642526319367568433 929360731894739525676325)
                  ·
                    refine ⟨174255137230263661064311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929360731894739525676325 174255137230263661064311)
                    ·
                      rfl

theorem cell23_1018082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1018082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018082 prefixEnd_1018082 := by exact prefixLift 1018082
  have htrace : WordTrace (prefixWord ++ tailWord_1018082) baseStart_1018082 baseEnd_1018082 := by
    simpa [prefixWord, tailWord_1018082, baseEnd_1018082] using wordTrace_append hprefix tailTrace_1018082
  have hstable : (prefixWord ++ tailWord_1018082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018082).length < 2 ^ (prefixWord ++ tailWord_1018082).sum := by decide
  have hdescent : baseEnd_1018082 < baseStart_1018082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018088 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1018088 : Nat := 118140960795 + 1018088 * 2 ^ 59
def prefixEnd_1018088 : Nat := 4983230072969 + 3 ^ 40 * 1018088 * 2
def baseEnd_1018088 : Nat := 522768492574717959717905

theorem tailTrace_1018088 : CollatzResearch.WordTrace tailWord_1018088 prefixEnd_1018088 522768492574717959717905 := by
  unfold tailWord_1018088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566359967824263216283459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24755146623765684288377945 18566359967824263216283459)
  ·
    refine ⟨27849539951736394824425189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18566359967824263216283459 27849539951736394824425189)
    ·
      refine ⟨5221788740950574029579723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27849539951736394824425189 5221788740950574029579723)
      ·
        refine ⟨7832683111425861044369585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221788740950574029579723 7832683111425861044369585)
        ·
          refine ⟨5874512333569395783277189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7832683111425861044369585 5874512333569395783277189)
          ·
            refine ⟨1101471062544261709364473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5874512333569395783277189 1101471062544261709364473)
            ·
              refine ⟨826103296908196282023355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101471062544261709364473 826103296908196282023355)
              ·
                refine ⟨1239154945362294423035033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826103296908196282023355 1239154945362294423035033)
                ·
                  refine ⟨929366209021720817276275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239154945362294423035033 929366209021720817276275)
                  ·
                    refine ⟨1394049313532581225914413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 929366209021720817276275 1394049313532581225914413)
                    ·
                      refine ⟨522768492574717959717905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394049313532581225914413 522768492574717959717905)
                      ·
                        rfl

theorem cell23_1018088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1018088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018088 prefixEnd_1018088 := by exact prefixLift 1018088
  have htrace : WordTrace (prefixWord ++ tailWord_1018088) baseStart_1018088 baseEnd_1018088 := by
    simpa [prefixWord, tailWord_1018088, baseEnd_1018088] using wordTrace_append hprefix tailTrace_1018088
  have hstable : (prefixWord ++ tailWord_1018088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018088).length < 2 ^ (prefixWord ++ tailWord_1018088).sum := by decide
  have hdescent : baseEnd_1018088 < baseStart_1018088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018094 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_1018094 : Nat := 118140960795 + 1018094 * 2 ^ 59
def prefixEnd_1018094 : Nat := 4983230072969 + 3 ^ 40 * 1018094 * 2
def baseEnd_1018094 : Nat := 522771573458644936242877

theorem tailTrace_1018094 : CollatzResearch.WordTrace tailWord_1018094 prefixEnd_1018094 522771573458644936242877 := by
  unfold tailWord_1018094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641617346703348682160667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24755292515751192971523557 4641617346703348682160667)
  ·
    refine ⟨6962426020055023023241001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641617346703348682160667 6962426020055023023241001)
    ·
      refine ⟨5221819515041267267430751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6962426020055023023241001 5221819515041267267430751)
      ·
        refine ⟨7832729272561900901146127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221819515041267267430751 7832729272561900901146127)
        ·
          refine ⟨11749093908842851351719191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832729272561900901146127 11749093908842851351719191)
          ·
            refine ⟨17623640863264277027578787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749093908842851351719191 17623640863264277027578787)
            ·
              refine ⟨26435461294896415541368181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623640863264277027578787 26435461294896415541368181)
              ·
                refine ⟨2478324496396538957003267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26435461294896415541368181 2478324496396538957003267)
                ·
                  refine ⟨3717486744594808435504901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478324496396538957003267 3717486744594808435504901)
                  ·
                    refine ⟨697028764611526581657169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3717486744594808435504901 697028764611526581657169)
                    ·
                      refine ⟨522771573458644936242877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697028764611526581657169 522771573458644936242877)
                      ·
                        rfl

theorem cell23_1018094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_1018094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018094 prefixEnd_1018094 := by exact prefixLift 1018094
  have htrace : WordTrace (prefixWord ++ tailWord_1018094) baseStart_1018094 baseEnd_1018094 := by
    simpa [prefixWord, tailWord_1018094, baseEnd_1018094] using wordTrace_append hprefix tailTrace_1018094
  have hstable : (prefixWord ++ tailWord_1018094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018094).length < 2 ^ (prefixWord ++ tailWord_1018094).sum := by decide
  have hdescent : baseEnd_1018094 < baseStart_1018094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018098 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1018098 : Nat := 118140960795 + 1018098 * 2 ^ 59
def prefixEnd_1018098 : Nat := 4983230072969 + 3 ^ 40 * 1018098 * 2
def baseEnd_1018098 : Nat := 522773627381262920592859

theorem tailTrace_1018098 : CollatzResearch.WordTrace tailWord_1018098 prefixEnd_1018098 522773627381262920592859 := by
  unfold tailWord_1018098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283271166403074535107737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24755389777074865426953965 9283271166403074535107737)
  ·
    refine ⟨6962453374802305901330803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9283271166403074535107737 6962453374802305901330803)
    ·
      refine ⟨10443680062203458851996205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6962453374802305901330803 10443680062203458851996205)
      ·
        refine ⟨3916380023326297069498577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10443680062203458851996205 3916380023326297069498577)
        ·
          refine ⟨2937285017494722802123933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916380023326297069498577 2937285017494722802123933)
          ·
            refine ⟨1101481881560521050796475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2937285017494722802123933 1101481881560521050796475)
            ·
              refine ⟨1652222822340781576194713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101481881560521050796475 1652222822340781576194713)
              ·
                refine ⟨1239167116755586182146035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652222822340781576194713 1239167116755586182146035)
                ·
                  refine ⟨1858750675133379273219053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239167116755586182146035 1858750675133379273219053)
                  ·
                    refine ⟨697031503175017227457145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1858750675133379273219053 697031503175017227457145)
                    ·
                      refine ⟨522773627381262920592859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697031503175017227457145 522773627381262920592859)
                      ·
                        rfl

theorem cell23_1018098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1018098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018098 prefixEnd_1018098 := by exact prefixLift 1018098
  have htrace : WordTrace (prefixWord ++ tailWord_1018098) baseStart_1018098 baseEnd_1018098 := by
    simpa [prefixWord, tailWord_1018098, baseEnd_1018098] using wordTrace_append hprefix tailTrace_1018098
  have hstable : (prefixWord ++ tailWord_1018098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018098).length < 2 ^ (prefixWord ++ tailWord_1018098).sum := by decide
  have hdescent : baseEnd_1018098 < baseStart_1018098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018114 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1018114 : Nat := 118140960795 + 1018114 * 2 ^ 59
def prefixEnd_1018114 : Nat := 4983230072969 + 3 ^ 40 * 1018114 * 2
def baseEnd_1018114 : Nat := 522781843071734857992785

theorem tailTrace_1018114 : CollatzResearch.WordTrace tailWord_1018114 prefixEnd_1018114 522781843071734857992785 := by
  unfold tailWord_1018114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283417058388583218253349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24755778822369555248675597 9283417058388583218253349)
  ·
    refine ⟨1740640698447859353422503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9283417058388583218253349 1740640698447859353422503)
    ·
      refine ⟨2610961047671789030133755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740640698447859353422503 2610961047671789030133755)
      ·
        refine ⟨3916441571507683545200633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610961047671789030133755 3916441571507683545200633)
        ·
          refine ⟨2937331178630762658900475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916441571507683545200633 2937331178630762658900475)
          ·
            refine ⟨4405996767946143988350713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937331178630762658900475 4405996767946143988350713)
            ·
              refine ⟨3304497575959607991263035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405996767946143988350713 3304497575959607991263035)
              ·
                refine ⟨4956746363939411986894553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304497575959607991263035 4956746363939411986894553)
                ·
                  refine ⟨3717559772954558990170915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956746363939411986894553 3717559772954558990170915)
                  ·
                    refine ⟨5576339659431838485256373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3717559772954558990170915 5576339659431838485256373)
                    ·
                      refine ⟨522781843071734857992785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5576339659431838485256373 522781843071734857992785)
                      ·
                        rfl

theorem cell23_1018114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1018114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018114 prefixEnd_1018114 := by exact prefixLift 1018114
  have htrace : WordTrace (prefixWord ++ tailWord_1018114) baseStart_1018114 baseEnd_1018114 := by
    simpa [prefixWord, tailWord_1018114, baseEnd_1018114] using wordTrace_append hprefix tailTrace_1018114
  have hstable : (prefixWord ++ tailWord_1018114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018114).length < 2 ^ (prefixWord ++ tailWord_1018114).sum := by decide
  have hdescent : baseEnd_1018114 < baseStart_1018114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018144 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1018144 : Nat := 118140960795 + 1018144 * 2 ^ 59
def prefixEnd_1018144 : Nat := 4983230072969 + 3 ^ 40 * 1018144 * 2
def baseEnd_1018144 : Nat := 522797247491369740617647

theorem tailTrace_1018144 : CollatzResearch.WordTrace tailWord_1018144 prefixEnd_1018144 522797247491369740617647 := by
  unfold tailWord_1018144
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567381211722823998302743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24756508282297098664403657 18567381211722823998302743)
  ·
    refine ⟨27851071817584235997454115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18567381211722823998302743 27851071817584235997454115)
    ·
      refine ⟨41776607726376353996181173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27851071817584235997454115 41776607726376353996181173)
      ·
        refine ⟨3916556974347783187141985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41776607726376353996181173 3916556974347783187141985)
        ·
          refine ⟨2937417730760837390356489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916556974347783187141985 2937417730760837390356489)
          ·
            refine ⟨2203063298070628042767367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937417730760837390356489 2203063298070628042767367)
            ·
              refine ⟨3304594947105942064151051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203063298070628042767367 3304594947105942064151051)
              ·
                refine ⟨4956892420658913096226577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304594947105942064151051 4956892420658913096226577)
                ·
                  refine ⟨3717669315494184822169933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956892420658913096226577 3717669315494184822169933)
                  ·
                    refine ⟨1394125993310319308313725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717669315494184822169933 1394125993310319308313725)
                    ·
                      refine ⟨522797247491369740617647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394125993310319308313725 522797247491369740617647)
                      ·
                        rfl

theorem cell23_1018144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1018144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018144 prefixEnd_1018144 := by exact prefixLift 1018144
  have htrace : WordTrace (prefixWord ++ tailWord_1018144) baseStart_1018144 baseEnd_1018144 := by
    simpa [prefixWord, tailWord_1018144, baseEnd_1018144] using wordTrace_append hprefix tailTrace_1018144
  have hstable : (prefixWord ++ tailWord_1018144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018144).length < 2 ^ (prefixWord ++ tailWord_1018144).sum := by decide
  have hdescent : baseEnd_1018144 < baseStart_1018144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018160 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_1018160 : Nat := 118140960795 + 1018160 * 2 ^ 59
def prefixEnd_1018160 : Nat := 4983230072969 + 3 ^ 40 * 1018160 * 2
def baseEnd_1018160 : Nat := 174268487727280559339191

theorem tailTrace_1018160 : CollatzResearch.WordTrace tailWord_1018160 prefixEnd_1018160 174268487727280559339191 := by
  unfold tailWord_1018160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567672995693841364593967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24756897327591788486125289 18567672995693841364593967)
  ·
    refine ⟨27851509493540762046890951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18567672995693841364593967 27851509493540762046890951)
    ·
      refine ⟨41777264240311143070336427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27851509493540762046890951 41777264240311143070336427)
      ·
        refine ⟨62665896360466714605504641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41777264240311143070336427 62665896360466714605504641)
        ·
          refine ⟨46999422270350035954128481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62665896360466714605504641 46999422270350035954128481)
          ·
            refine ⟨35249566702762526965596361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46999422270350035954128481 35249566702762526965596361)
            ·
              refine ⟨26437175027071895224197271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35249566702762526965596361 26437175027071895224197271)
              ·
                refine ⟨39655762540607842836295907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26437175027071895224197271 39655762540607842836295907)
                ·
                  refine ⟨59483643810911764254443861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39655762540607842836295907 59483643810911764254443861)
                  ·
                    refine ⟨174268487727280559339191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 59483643810911764254443861 174268487727280559339191)
                    ·
                      rfl

theorem cell23_1018160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_1018160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018160 prefixEnd_1018160 := by exact prefixLift 1018160
  have htrace : WordTrace (prefixWord ++ tailWord_1018160) baseStart_1018160 baseEnd_1018160 := by
    simpa [prefixWord, tailWord_1018160, baseEnd_1018160] using wordTrace_append hprefix tailTrace_1018160
  have hstable : (prefixWord ++ tailWord_1018160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018160).length < 2 ^ (prefixWord ++ tailWord_1018160).sum := by decide
  have hdescent : baseEnd_1018160 < baseStart_1018160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018164 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1018164 : Nat := 118140960795 + 1018164 * 2 ^ 59
def prefixEnd_1018164 : Nat := 4983230072969 + 3 ^ 40 * 1018164 * 2
def baseEnd_1018164 : Nat := 174269172368153220789185

theorem tailTrace_1018164 : CollatzResearch.WordTrace tailWord_1018164 prefixEnd_1018164 174269172368153220789185 := by
  unfold tailWord_1018164
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567745941686595706166773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24756994588915460941555697 18567745941686595706166773)
  ·
    refine ⟨1740726182033118347453135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18567745941686595706166773 1740726182033118347453135)
    ·
      refine ⟨2611089273049677521179703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740726182033118347453135 2611089273049677521179703)
      ·
        refine ⟨3916633909574516281769555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611089273049677521179703 3916633909574516281769555)
        ·
          refine ⟨5874950864361774422654333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916633909574516281769555 5874950864361774422654333)
          ·
            refine ⟨2203106574135665408495375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5874950864361774422654333 2203106574135665408495375)
            ·
              refine ⟨3304659861203498112743063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203106574135665408495375 3304659861203498112743063)
              ·
                refine ⟨4956989791805247169114595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304659861203498112743063 4956989791805247169114595)
                ·
                  refine ⟨7435484687707870753671893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956989791805247169114595 7435484687707870753671893)
                  ·
                    refine ⟨174269172368153220789185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7435484687707870753671893 174269172368153220789185)
                    ·
                      rfl

theorem cell23_1018164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1018164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018164 prefixEnd_1018164 := by exact prefixLift 1018164
  have htrace : WordTrace (prefixWord ++ tailWord_1018164) baseStart_1018164 baseEnd_1018164 := by
    simpa [prefixWord, tailWord_1018164, baseEnd_1018164] using wordTrace_append hprefix tailTrace_1018164
  have hstable : (prefixWord ++ tailWord_1018164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018164).length < 2 ^ (prefixWord ++ tailWord_1018164).sum := by decide
  have hdescent : baseEnd_1018164 < baseStart_1018164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018184 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_1018184 : Nat := 118140960795 + 1018184 * 2 ^ 59
def prefixEnd_1018184 : Nat := 4983230072969 + 3 ^ 40 * 1018184 * 2
def baseEnd_1018184 : Nat := 522817786717549584117463

theorem tailTrace_1018184 : CollatzResearch.WordTrace tailWord_1018184 prefixEnd_1018184 522817786717549584117463 := by
  unfold tailWord_1018184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568110671650367414030803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24757480895533823218707737 18568110671650367414030803)
  ·
    refine ⟨27852166007475551121046205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18568110671650367414030803 27852166007475551121046205)
    ·
      refine ⟨10444562252803331670392327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27852166007475551121046205 10444562252803331670392327)
      ·
        refine ⟨15666843379204997505588491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10444562252803331670392327 15666843379204997505588491)
        ·
          refine ⟨23500265068807496258382737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666843379204997505588491 23500265068807496258382737)
          ·
            refine ⟨17625198801605622193787053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500265068807496258382737 17625198801605622193787053)
            ·
              refine ⟨6609449550602108322670145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17625198801605622193787053 6609449550602108322670145)
              ·
                refine ⟨4957087162951581242002609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609449550602108322670145 4957087162951581242002609)
                ·
                  refine ⟨3717815372213685931501957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957087162951581242002609 3717815372213685931501957)
                  ·
                    refine ⟨697090382290066112156617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3717815372213685931501957 697090382290066112156617)
                    ·
                      refine ⟨522817786717549584117463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697090382290066112156617 522817786717549584117463)
                      ·
                        rfl

theorem cell23_1018184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_1018184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018184 prefixEnd_1018184 := by exact prefixLift 1018184
  have htrace : WordTrace (prefixWord ++ tailWord_1018184) baseStart_1018184 baseEnd_1018184 := by
    simpa [prefixWord, tailWord_1018184, baseEnd_1018184] using wordTrace_append hprefix tailTrace_1018184
  have hstable : (prefixWord ++ tailWord_1018184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018184).length < 2 ^ (prefixWord ++ tailWord_1018184).sum := by decide
  have hdescent : baseEnd_1018184 < baseStart_1018184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018194 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1018194 : Nat := 118140960795 + 1018194 * 2 ^ 59
def prefixEnd_1018194 : Nat := 4983230072969 + 3 ^ 40 * 1018194 * 2
def baseEnd_1018194 : Nat := 174274307174698181664139

theorem tailTrace_1018194 : CollatzResearch.WordTrace tailWord_1018194 prefixEnd_1018194 174274307174698181664139 := by
  unfold tailWord_1018194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284146518316126633981409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24757724048843004357283757 9284146518316126633981409)
  ·
    refine ⟨6963109888737094975486057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9284146518316126633981409 6963109888737094975486057)
    ·
      refine ⟨5222332416552821231614543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6963109888737094975486057 5222332416552821231614543)
      ·
        refine ⟨7833498624829231847421815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222332416552821231614543 7833498624829231847421815)
        ·
          refine ⟨11750247937243847771132723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833498624829231847421815 11750247937243847771132723)
          ·
            refine ⟨17625371905865771656699085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750247937243847771132723 17625371905865771656699085)
            ·
              refine ⟨6609514464699664371262157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17625371905865771656699085 6609514464699664371262157)
              ·
                refine ⟨2478567924262374139223309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6609514464699664371262157 2478567924262374139223309)
                ·
                  refine ⟨929462971598390302208741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2478567924262374139223309 929462971598390302208741)
                  ·
                    refine ⟨174274307174698181664139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929462971598390302208741 174274307174698181664139)
                    ·
                      rfl

theorem cell23_1018194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1018194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018194 prefixEnd_1018194 := by exact prefixLift 1018194
  have htrace : WordTrace (prefixWord ++ tailWord_1018194) baseStart_1018194 baseEnd_1018194 := by
    simpa [prefixWord, tailWord_1018194, baseEnd_1018194] using wordTrace_append hprefix tailTrace_1018194
  have hstable : (prefixWord ++ tailWord_1018194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018194).length < 2 ^ (prefixWord ++ tailWord_1018194).sum := by decide
  have hdescent : baseEnd_1018194 < baseStart_1018194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018207 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 6]
def baseStart_1018207 : Nat := 118140960795 + 1018207 * 2 ^ 59
def prefixEnd_1018207 : Nat := 4983230072969 + 3 ^ 40 * 1018207 * 2
def baseEnd_1018207 : Nat := 58092177419178110458873

theorem tailTrace_1018207 : CollatzResearch.WordTrace tailWord_1018207 prefixEnd_1018207 58092177419178110458873 := by
  unfold tailWord_1018207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137060222217409756148875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24758040148144939837432583 37137060222217409756148875)
  ·
    refine ⟨55705590333326114634223313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37137060222217409756148875 55705590333326114634223313)
    ·
      refine ⟨41779192749994585975667485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55705590333326114634223313 41779192749994585975667485)
      ·
        refine ⟨15667197281247969740875307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41779192749994585975667485 15667197281247969740875307)
        ·
          refine ⟨23500795921871954611312961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667197281247969740875307 23500795921871954611312961)
          ·
            refine ⟨17625596941403965958484721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500795921871954611312961 17625596941403965958484721)
            ·
              refine ⟨13219197706052974468863541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17625596941403965958484721 13219197706052974468863541)
              ·
                refine ⟨1239299784942466356455957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13219197706052974468863541 1239299784942466356455957)
                ·
                  refine ⟨58092177419178110458873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1239299784942466356455957 58092177419178110458873)
                  ·
                    rfl

theorem cell23_1018207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 6].length) (baseStart_1018207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018207 prefixEnd_1018207 := by exact prefixLift 1018207
  have htrace : WordTrace (prefixWord ++ tailWord_1018207) baseStart_1018207 baseEnd_1018207 := by
    simpa [prefixWord, tailWord_1018207, baseEnd_1018207] using wordTrace_append hprefix tailTrace_1018207
  have hstable : (prefixWord ++ tailWord_1018207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018207).length < 2 ^ (prefixWord ++ tailWord_1018207).sum := by decide
  have hdescent : baseEnd_1018207 < baseStart_1018207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018217 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_1018217 : Nat := 118140960795 + 1018217 * 2 ^ 59
def prefixEnd_1018217 : Nat := 4983230072969 + 3 ^ 40 * 1018217 * 2
def baseEnd_1018217 : Nat := 522834731579147955004811

theorem tailTrace_1018217 : CollatzResearch.WordTrace tailWord_1018217 prefixEnd_1018217 522834731579147955004811 := by
  unfold tailWord_1018217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137424952181181464012905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24758283301454120976008603 37137424952181181464012905)
  ·
    refine ⟨27853068714135886098009679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37137424952181181464012905 27853068714135886098009679)
    ·
      refine ⟨41779603071203829147014519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27853068714135886098009679 41779603071203829147014519)
      ·
        refine ⟨62669404606805743720521779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41779603071203829147014519 62669404606805743720521779)
        ·
          refine ⟨94004106910208615580782669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62669404606805743720521779 94004106910208615580782669)
          ·
            refine ⟨35251540091328230842793501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94004106910208615580782669 35251540091328230842793501)
            ·
              refine ⟨13219327534248086566047563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35251540091328230842793501 13219327534248086566047563)
              ·
                refine ⟨19828991301372129849071345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13219327534248086566047563 19828991301372129849071345)
                ·
                  refine ⟨14871743476029097386803509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19828991301372129849071345 14871743476029097386803509)
                  ·
                    refine ⟨1394225950877727880012829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14871743476029097386803509 1394225950877727880012829)
                    ·
                      refine ⟨522834731579147955004811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394225950877727880012829 522834731579147955004811)
                      ·
                        rfl

theorem cell23_1018217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_1018217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018217 prefixEnd_1018217 := by exact prefixLift 1018217
  have htrace : WordTrace (prefixWord ++ tailWord_1018217) baseStart_1018217 baseEnd_1018217 := by
    simpa [prefixWord, tailWord_1018217, baseEnd_1018217] using wordTrace_append hprefix tailTrace_1018217
  have hstable : (prefixWord ++ tailWord_1018217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018217).length < 2 ^ (prefixWord ++ tailWord_1018217).sum := by decide
  have hdescent : baseEnd_1018217 < baseStart_1018217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018251 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 3]
def baseStart_1018251 : Nat := 118140960795 + 1018251 * 2 ^ 59
def prefixEnd_1018251 : Nat := 4983230072969 + 3 ^ 40 * 1018251 * 2
def baseEnd_1018251 : Nat := 522852189921400821979655

theorem tailTrace_1018251 : CollatzResearch.WordTrace tailWord_1018251 prefixEnd_1018251 522852189921400821979655 := by
  unfold tailWord_1018251
  simp only [CollatzResearch.WordTrace]
  refine ⟨37138665034058005270750607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24759110022705336847167071 37138665034058005270750607)
  ·
    refine ⟨55707997551087007906125911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37138665034058005270750607 55707997551087007906125911)
    ·
      refine ⟨83561996326630511859188867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55707997551087007906125911 83561996326630511859188867)
      ·
        refine ⟨125342994489945767788783301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83561996326630511859188867 125342994489945767788783301)
        ·
          refine ⟨23501811466864831460396869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125342994489945767788783301 23501811466864831460396869)
          ·
            refine ⟨4406589650037155898824413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23501811466864831460396869 4406589650037155898824413)
            ·
              refine ⟨1652471118763933462059155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4406589650037155898824413 1652471118763933462059155)
              ·
                refine ⟨2478706678145900193088733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652471118763933462059155 2478706678145900193088733)
                ·
                  refine ⟨929515004304712572408275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2478706678145900193088733 929515004304712572408275)
                  ·
                    refine ⟨1394272506457068858612413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 929515004304712572408275 1394272506457068858612413)
                    ·
                      refine ⟨522852189921400821979655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394272506457068858612413 522852189921400821979655)
                      ·
                        rfl

theorem cell23_1018251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 3].length) (baseStart_1018251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018251 prefixEnd_1018251 := by exact prefixLift 1018251
  have htrace : WordTrace (prefixWord ++ tailWord_1018251) baseStart_1018251 baseEnd_1018251 := by
    simpa [prefixWord, tailWord_1018251, baseEnd_1018251] using wordTrace_append hprefix tailTrace_1018251
  have hstable : (prefixWord ++ tailWord_1018251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018251).length < 2 ^ (prefixWord ++ tailWord_1018251).sum := by decide
  have hdescent : baseEnd_1018251 < baseStart_1018251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018297 : List Nat := [1, 2, 1, 4, 3, 12]
def baseStart_1018297 : Nat := 118140960795 + 1018297 * 2 ^ 59
def prefixEnd_1018297 : Nat := 4983230072969 + 3 ^ 40 * 1018297 * 2
def baseEnd_1018297 : Nat := 2151752304656410049401

theorem tailTrace_1018297 : CollatzResearch.WordTrace tailWord_1018297 prefixEnd_1018297 2151752304656410049401 := by
  unfold tailWord_1018297
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140342791891355126925145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24760228527927570084616763 37140342791891355126925145)
  ·
    refine ⟨27855257093918516345193859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37140342791891355126925145 27855257093918516345193859)
    ·
      refine ⟨41782885640877774517790789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27855257093918516345193859 41782885640877774517790789)
      ·
        refine ⟨7834291057664582722085773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41782885640877774517790789 7834291057664582722085773)
        ·
          refine ⟨2937859146624218520782165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7834291057664582722085773 2937859146624218520782165)
          ·
            refine ⟨2151752304656410049401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2937859146624218520782165 2151752304656410049401)
            ·
              rfl

theorem cell23_1018297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 12].length) (baseStart_1018297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018297 prefixEnd_1018297 := by exact prefixLift 1018297
  have htrace : WordTrace (prefixWord ++ tailWord_1018297) baseStart_1018297 baseEnd_1018297 := by
    simpa [prefixWord, tailWord_1018297, baseEnd_1018297] using wordTrace_append hprefix tailTrace_1018297
  have hstable : (prefixWord ++ tailWord_1018297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018297).length < 2 ^ (prefixWord ++ tailWord_1018297).sum := by decide
  have hdescent : baseEnd_1018297 < baseStart_1018297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018301 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1018301 : Nat := 118140960795 + 1018301 * 2 ^ 59
def prefixEnd_1018301 : Nat := 4983230072969 + 3 ^ 40 * 1018301 * 2
def baseEnd_1018301 : Nat := 174292621318041875451475

theorem tailTrace_1018301 : CollatzResearch.WordTrace tailWord_1018301 prefixEnd_1018301 174292621318041875451475 := by
  unfold tailWord_1018301
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140488683876863810070757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24760325789251242540047171 37140488683876863810070757)
  ·
    refine ⟨6963841628226911964388267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37140488683876863810070757 6963841628226911964388267)
    ·
      refine ⟨10445762442340367946582401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6963841628226911964388267 10445762442340367946582401)
      ·
        refine ⟨7834321831755275959936801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10445762442340367946582401 7834321831755275959936801)
        ·
          refine ⟨5875741373816456969952601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7834321831755275959936801 5875741373816456969952601)
          ·
            refine ⟨4406806030362342727464451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5875741373816456969952601 4406806030362342727464451)
            ·
              refine ⟨6610209045543514091196677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406806030362342727464451 6610209045543514091196677)
              ·
                refine ⟨1239414196039408892099377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6610209045543514091196677 1239414196039408892099377)
                ·
                  refine ⟨929560647029556669074533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239414196039408892099377 929560647029556669074533)
                  ·
                    refine ⟨174292621318041875451475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929560647029556669074533 174292621318041875451475)
                    ·
                      rfl

theorem cell23_1018301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1018301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018301 prefixEnd_1018301 := by exact prefixLift 1018301
  have htrace : WordTrace (prefixWord ++ tailWord_1018301) baseStart_1018301 baseEnd_1018301 := by
    simpa [prefixWord, tailWord_1018301, baseEnd_1018301] using wordTrace_append hprefix tailTrace_1018301
  have hstable : (prefixWord ++ tailWord_1018301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018301).length < 2 ^ (prefixWord ++ tailWord_1018301).sum := by decide
  have hdescent : baseEnd_1018301 < baseStart_1018301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018358 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1018358 : Nat := 118140960795 + 1018358 * 2 ^ 59
def prefixEnd_1018358 : Nat := 4983230072969 + 3 ^ 40 * 1018358 * 2
def baseEnd_1018358 : Nat := 522907132351431903341663

theorem tailTrace_1018358 : CollatzResearch.WordTrace tailWord_1018358 prefixEnd_1018358 522907132351431903341663 := by
  unfold tailWord_1018358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321410477791897659055983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24761711763113575029930485 2321410477791897659055983)
  ·
    refine ⟨3482115716687846488583975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2321410477791897659055983 3482115716687846488583975)
    ·
      refine ⟨5223173575031769732875963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3482115716687846488583975 5223173575031769732875963)
      ·
        refine ⟨7834760362547654599313945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223173575031769732875963 7834760362547654599313945)
        ·
          refine ⟨5876070271910740949485459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7834760362547654599313945 5876070271910740949485459)
          ·
            refine ⟨8814105407866111424228189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876070271910740949485459 8814105407866111424228189)
            ·
              refine ⟨3305289527949791784085571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8814105407866111424228189 3305289527949791784085571)
              ·
                refine ⟨4957934291924687676128357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305289527949791784085571 4957934291924687676128357)
                ·
                  refine ⟨929612679735878939274067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4957934291924687676128357 929612679735878939274067)
                  ·
                    refine ⟨1394419019603818408911101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 929612679735878939274067 1394419019603818408911101)
                    ·
                      refine ⟨522907132351431903341663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394419019603818408911101 522907132351431903341663)
                      ·
                        rfl

theorem cell23_1018358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1018358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018358 prefixEnd_1018358 := by exact prefixLift 1018358
  have htrace : WordTrace (prefixWord ++ tailWord_1018358) baseStart_1018358 baseEnd_1018358 := by
    simpa [prefixWord, tailWord_1018358, baseEnd_1018358] using wordTrace_append hprefix tailTrace_1018358
  have hstable : (prefixWord ++ tailWord_1018358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018358).length < 2 ^ (prefixWord ++ tailWord_1018358).sum := by decide
  have hdescent : baseEnd_1018358 < baseStart_1018358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018375 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_1018375 : Nat := 118140960795 + 1018375 * 2 ^ 59
def prefixEnd_1018375 : Nat := 4983230072969 + 3 ^ 40 * 1018375 * 2
def baseEnd_1018375 : Nat := 522915861522558336829085

theorem tailTrace_1018375 : CollatzResearch.WordTrace tailWord_1018375 prefixEnd_1018375 522915861522558336829085 := by
  unfold tailWord_1018375
  simp only [CollatzResearch.WordTrace]
  refine ⟨37143187685608774448264579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24762125123739182965509719 37143187685608774448264579)
  ·
    refine ⟨55714781528413161672396869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37143187685608774448264579 55714781528413161672396869)
    ·
      refine ⟨10446521536577467813574413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55714781528413161672396869 10446521536577467813574413)
      ·
        refine ⟨3917445576216550430090405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10446521536577467813574413 3917445576216550430090405)
        ·
          refine ⟨734521045540603205641951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3917445576216550430090405 734521045540603205641951)
          ·
            refine ⟨1101781568310904808462927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734521045540603205641951 1101781568310904808462927)
            ·
              refine ⟨1652672352466357212694391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101781568310904808462927 1652672352466357212694391)
              ·
                refine ⟨2479008528699535819041587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652672352466357212694391 2479008528699535819041587)
                ·
                  refine ⟨3718512793049303728562381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479008528699535819041587 3718512793049303728562381)
                  ·
                    refine ⟨1394442297393488898210893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718512793049303728562381 1394442297393488898210893)
                    ·
                      refine ⟨522915861522558336829085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394442297393488898210893 522915861522558336829085)
                      ·
                        rfl

theorem cell23_1018375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_1018375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018375 prefixEnd_1018375 := by exact prefixLift 1018375
  have htrace : WordTrace (prefixWord ++ tailWord_1018375) baseStart_1018375 baseEnd_1018375 := by
    simpa [prefixWord, tailWord_1018375, baseEnd_1018375] using wordTrace_append hprefix tailTrace_1018375
  have hstable : (prefixWord ++ tailWord_1018375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018375).length < 2 ^ (prefixWord ++ tailWord_1018375).sum := by decide
  have hdescent : baseEnd_1018375 < baseStart_1018375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018394 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1018394 : Nat := 118140960795 + 1018394 * 2 ^ 59
def prefixEnd_1018394 : Nat := 4983230072969 + 3 ^ 40 * 1018394 * 2
def baseEnd_1018394 : Nat := 522925617654993762491497

theorem tailTrace_1018394 : CollatzResearch.WordTrace tailWord_1018394 prefixEnd_1018394 522925617654993762491497 := by
  unfold tailWord_1018394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285970168134985173301559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24762587115026627128804157 9285970168134985173301559)
  ·
    refine ⟨13928955252202477759952339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9285970168134985173301559 13928955252202477759952339)
    ·
      refine ⟨20893432878303716639928509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13928955252202477759952339 20893432878303716639928509)
      ·
        refine ⟨7835037329363893739973191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20893432878303716639928509 7835037329363893739973191)
        ·
          refine ⟨11752555994045840609959787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835037329363893739973191 11752555994045840609959787)
          ·
            refine ⟨17628833991068760914939681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752555994045840609959787 17628833991068760914939681)
            ·
              refine ⟨13221625493301570686204761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17628833991068760914939681 13221625493301570686204761)
              ·
                refine ⟨9916219119976178014653571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13221625493301570686204761 9916219119976178014653571)
                ·
                  refine ⟨14874328679964267021980357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916219119976178014653571 14874328679964267021980357)
                  ·
                    refine ⟨2788936627493300066621317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14874328679964267021980357 2788936627493300066621317)
                    ·
                      refine ⟨522925617654993762491497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2788936627493300066621317 522925617654993762491497)
                      ·
                        rfl

theorem cell23_1018394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1018394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018394 prefixEnd_1018394 := by exact prefixLift 1018394
  have htrace : WordTrace (prefixWord ++ tailWord_1018394) baseStart_1018394 baseEnd_1018394 := by
    simpa [prefixWord, tailWord_1018394, baseEnd_1018394] using wordTrace_append hprefix tailTrace_1018394
  have hstable : (prefixWord ++ tailWord_1018394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018394).length < 2 ^ (prefixWord ++ tailWord_1018394).sum := by decide
  have hdescent : baseEnd_1018394 < baseStart_1018394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018436 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1018436 : Nat := 118140960795 + 1018436 * 2 ^ 59
def prefixEnd_1018436 : Nat := 4983230072969 + 3 ^ 40 * 1018436 * 2
def baseEnd_1018436 : Nat := 522947183842482598166305

theorem tailTrace_1018436 : CollatzResearch.WordTrace tailWord_1018436 prefixEnd_1018436 522947183842482598166305 := by
  unfold tailWord_1018436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572706269193890933117581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24763608358925187910823441 18572706269193890933117581)
  ·
    refine ⟨6964764850947709099919093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18572706269193890933117581 6964764850947709099919093)
    ·
      refine ⟨652946704776347728117415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6964764850947709099919093 652946704776347728117415)
      ·
        refine ⟨979420057164521592176123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652946704776347728117415 979420057164521592176123)
        ·
          refine ⟨1469130085746782388264185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979420057164521592176123 1469130085746782388264185)
          ·
            refine ⟨1101847564310086791198139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469130085746782388264185 1101847564310086791198139)
            ·
              refine ⟨1652771346465130186797209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101847564310086791198139 1652771346465130186797209)
              ·
                refine ⟨1239578509848847640097907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652771346465130186797209 1239578509848847640097907)
                ·
                  refine ⟨1859367764773271460146861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239578509848847640097907 1859367764773271460146861)
                  ·
                    refine ⟨697262911789976797555073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859367764773271460146861 697262911789976797555073)
                    ·
                      refine ⟨522947183842482598166305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697262911789976797555073 522947183842482598166305)
                      ·
                        rfl

theorem cell23_1018436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1018436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018436 prefixEnd_1018436 := by exact prefixLift 1018436
  have htrace : WordTrace (prefixWord ++ tailWord_1018436) baseStart_1018436 baseEnd_1018436 := by
    simpa [prefixWord, tailWord_1018436, baseEnd_1018436] using wordTrace_append hprefix tailTrace_1018436
  have hstable : (prefixWord ++ tailWord_1018436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018436).length < 2 ^ (prefixWord ++ tailWord_1018436).sum := by decide
  have hdescent : baseEnd_1018436 < baseStart_1018436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018444 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1018444 : Nat := 118140960795 + 1018444 * 2 ^ 59
def prefixEnd_1018444 : Nat := 4983230072969 + 3 ^ 40 * 1018444 * 2
def baseEnd_1018444 : Nat := 522951291687718566866267

theorem tailTrace_1018444 : CollatzResearch.WordTrace tailWord_1018444 prefixEnd_1018444 522951291687718566866267 := by
  unfold tailWord_1018444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572852161179399616263193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24763802881572532821684257 18572852161179399616263193)
  ·
    refine ⟨13929639120884549712197395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18572852161179399616263193 13929639120884549712197395)
    ·
      refine ⟨20894458681326824568296093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13929639120884549712197395 20894458681326824568296093)
      ·
        refine ⟨7835422005497559213111035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20894458681326824568296093 7835422005497559213111035)
        ·
          refine ⟨11753133008246338819666553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835422005497559213111035 11753133008246338819666553)
          ·
            refine ⟨8814849756184754114749915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753133008246338819666553 8814849756184754114749915)
            ·
              refine ⟨13222274634277131172124873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814849756184754114749915 13222274634277131172124873)
              ·
                refine ⟨9916705975707848379093655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222274634277131172124873 9916705975707848379093655)
                ·
                  refine ⟨14875058963561772568640483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916705975707848379093655 14875058963561772568640483)
                  ·
                    refine ⟨22312588445342658852960725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14875058963561772568640483 22312588445342658852960725)
                    ·
                      refine ⟨522951291687718566866267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22312588445342658852960725 522951291687718566866267)
                      ·
                        rfl

theorem cell23_1018444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1018444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018444 prefixEnd_1018444 := by exact prefixLift 1018444
  have htrace : WordTrace (prefixWord ++ tailWord_1018444) baseStart_1018444 baseEnd_1018444 := by
    simpa [prefixWord, tailWord_1018444, baseEnd_1018444] using wordTrace_append hprefix tailTrace_1018444
  have hstable : (prefixWord ++ tailWord_1018444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018444).length < 2 ^ (prefixWord ++ tailWord_1018444).sum := by decide
  have hdescent : baseEnd_1018444 < baseStart_1018444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018472 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 5]
def baseStart_1018472 : Nat := 118140960795 + 1018472 * 2 ^ 59
def prefixEnd_1018472 : Nat := 4983230072969 + 3 ^ 40 * 1018472 * 2
def baseEnd_1018472 : Nat := 58107296571782717479571

theorem tailTrace_1018472 : CollatzResearch.WordTrace tailWord_1018472 prefixEnd_1018472 58107296571782717479571 := by
  unfold tailWord_1018472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573362783128680007272835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24764483710838240009697113 18573362783128680007272835)
  ·
    refine ⟨27860044174693020010909253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18573362783128680007272835 27860044174693020010909253)
    ·
      refine ⟨5223758282754941252045485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27860044174693020010909253 5223758282754941252045485)
      ·
        refine ⟨1958909356033102969517057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5223758282754941252045485 1958909356033102969517057)
        ·
          refine ⟨1469182017024827227137793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958909356033102969517057 1469182017024827227137793)
          ·
            refine ⟨1101886512768620420353345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469182017024827227137793 1101886512768620420353345)
            ·
              refine ⟨826414884576465315265009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101886512768620420353345 826414884576465315265009)
              ·
                refine ⟨619811163432348986448757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826414884576465315265009 619811163432348986448757)
                ·
                  refine ⟨58107296571782717479571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 619811163432348986448757 58107296571782717479571)
                  ·
                    rfl

theorem cell23_1018472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 5].length) (baseStart_1018472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018472 prefixEnd_1018472 := by exact prefixLift 1018472
  have htrace : WordTrace (prefixWord ++ tailWord_1018472) baseStart_1018472 baseEnd_1018472 := by
    simpa [prefixWord, tailWord_1018472, baseEnd_1018472] using wordTrace_append hprefix tailTrace_1018472
  have hstable : (prefixWord ++ tailWord_1018472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018472).length < 2 ^ (prefixWord ++ tailWord_1018472).sum := by decide
  have hdescent : baseEnd_1018472 < baseStart_1018472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018591 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1018591 : Nat := 118140960795 + 1018591 * 2 ^ 59
def prefixEnd_1018591 : Nat := 4983230072969 + 3 ^ 40 * 1018591 * 2
def baseEnd_1018591 : Nat := 523026773343929491728091

theorem tailTrace_1018591 : CollatzResearch.WordTrace tailWord_1018591 prefixEnd_1018591 523026773343929491728091 := by
  unfold tailWord_1018591
  simp only [CollatzResearch.WordTrace]
  refine ⟨37151065852826243338127627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24767377235217495558751751 37151065852826243338127627)
  ·
    refine ⟨55726598779239365007191441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37151065852826243338127627 55726598779239365007191441)
    ·
      refine ⟨41794949084429523755393581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55726598779239365007191441 41794949084429523755393581)
      ·
        refine ⟨15673105906661071408272593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41794949084429523755393581 15673105906661071408272593)
        ·
          refine ⟨11754829429995803556204445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15673105906661071408272593 11754829429995803556204445)
          ·
            refine ⟨4408061036248426333576667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11754829429995803556204445 4408061036248426333576667)
            ·
              refine ⟨6612091554372639500365001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408061036248426333576667 6612091554372639500365001)
              ·
                refine ⟨4959068665779479625273751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612091554372639500365001 4959068665779479625273751)
                ·
                  refine ⟨7438602998669219437910627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959068665779479625273751 7438602998669219437910627)
                  ·
                    refine ⟨11157904498003829156865941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438602998669219437910627 11157904498003829156865941)
                    ·
                      refine ⟨523026773343929491728091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11157904498003829156865941 523026773343929491728091)
                      ·
                        rfl

theorem cell23_1018591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1018591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018591 prefixEnd_1018591 := by exact prefixLift 1018591
  have htrace : WordTrace (prefixWord ++ tailWord_1018591) baseStart_1018591 baseEnd_1018591 := by
    simpa [prefixWord, tailWord_1018591, baseEnd_1018591] using wordTrace_append hprefix tailTrace_1018591
  have hstable : (prefixWord ++ tailWord_1018591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018591).length < 2 ^ (prefixWord ++ tailWord_1018591).sum := by decide
  have hdescent : baseEnd_1018591 < baseStart_1018591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018605 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1018605 : Nat := 118140960795 + 1018605 * 2 ^ 59
def prefixEnd_1018605 : Nat := 4983230072969 + 3 ^ 40 * 1018605 * 2
def baseEnd_1018605 : Nat := 174344654024364145651009

theorem tailTrace_1018605 : CollatzResearch.WordTrace tailWord_1018605 prefixEnd_1018605 174344654024364145651009 := by
  unfold tailWord_1018605
  simp only [CollatzResearch.WordTrace]
  refine ⟨37151576474775523729137269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24767717649850349152758179 37151576474775523729137269)
  ·
    refine ⟨3482960294510205349606619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37151576474775523729137269 3482960294510205349606619)
    ·
      refine ⟨5224440441765308024409929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3482960294510205349606619 5224440441765308024409929)
      ·
        refine ⟨3918330331323981018307447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5224440441765308024409929 3918330331323981018307447)
        ·
          refine ⟨5877495496985971527461171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918330331323981018307447 5877495496985971527461171)
          ·
            refine ⟨8816243245478957291191757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877495496985971527461171 8816243245478957291191757)
            ·
              refine ⟨3306091217054608984196909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8816243245478957291191757 3306091217054608984196909)
              ·
                refine ⟨1239784206395478369073841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3306091217054608984196909 1239784206395478369073841)
                ·
                  refine ⟨929838154796608776805381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239784206395478369073841 929838154796608776805381)
                  ·
                    refine ⟨174344654024364145651009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929838154796608776805381 174344654024364145651009)
                    ·
                      rfl

theorem cell23_1018605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1018605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018605 prefixEnd_1018605 := by exact prefixLift 1018605
  have htrace : WordTrace (prefixWord ++ tailWord_1018605) baseStart_1018605 baseEnd_1018605 := by
    simpa [prefixWord, tailWord_1018605, baseEnd_1018605] using wordTrace_append hprefix tailTrace_1018605
  have hstable : (prefixWord ++ tailWord_1018605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018605).length < 2 ^ (prefixWord ++ tailWord_1018605).sum := by decide
  have hdescent : baseEnd_1018605 < baseStart_1018605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018632 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_1018632 : Nat := 118140960795 + 1018632 * 2 ^ 59
def prefixEnd_1018632 : Nat := 4983230072969 + 3 ^ 40 * 1018632 * 2
def baseEnd_1018632 : Nat := 523047826050763831315403

theorem tailTrace_1018632 : CollatzResearch.WordTrace tailWord_1018632 prefixEnd_1018632 523047826050763831315403 := by
  unfold tailWord_1018632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18576280622838853670185075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24768374163785138226913433 18576280622838853670185075)
  ·
    refine ⟨27864420934258280505277613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18576280622838853670185075 27864420934258280505277613)
    ·
      refine ⟨10449157850346855189479105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27864420934258280505277613 10449157850346855189479105)
      ·
        refine ⟨7836868387760141392109329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10449157850346855189479105 7836868387760141392109329)
        ·
          refine ⟨5877651290820106044081997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7836868387760141392109329 5877651290820106044081997)
          ·
            refine ⟨2204119234057539766530749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5877651290820106044081997 2204119234057539766530749)
            ·
              refine ⟨826544712771577412449031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2204119234057539766530749 826544712771577412449031)
              ·
                refine ⟨1239817069157366118673547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826544712771577412449031 1239817069157366118673547)
                ·
                  refine ⟨1859725603736049178010321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239817069157366118673547 1859725603736049178010321)
                  ·
                    refine ⟨1394794202802036883507741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859725603736049178010321 1394794202802036883507741)
                    ·
                      refine ⟨523047826050763831315403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1394794202802036883507741 523047826050763831315403)
                      ·
                        rfl

theorem cell23_1018632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_1018632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018632 prefixEnd_1018632 := by exact prefixLift 1018632
  have htrace : WordTrace (prefixWord ++ tailWord_1018632) baseStart_1018632 baseEnd_1018632 := by
    simpa [prefixWord, tailWord_1018632, baseEnd_1018632] using wordTrace_append hprefix tailTrace_1018632
  have hstable : (prefixWord ++ tailWord_1018632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018632).length < 2 ^ (prefixWord ++ tailWord_1018632).sum := by decide
  have hdescent : baseEnd_1018632 < baseStart_1018632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018641 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_1018641 : Nat := 118140960795 + 1018641 * 2 ^ 59
def prefixEnd_1018641 : Nat := 4983230072969 + 3 ^ 40 * 1018641 * 2
def baseEnd_1018641 : Nat := 523052447376654296102861

theorem tailTrace_1018641 : CollatzResearch.WordTrace tailWord_1018641 prefixEnd_1018641 523052447376654296102861 := by
  unfold tailWord_1018641
  simp only [CollatzResearch.WordTrace]
  refine ⟨37152889502645101877447777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24768593001763401251631851 37152889502645101877447777)
  ·
    refine ⟨27864667126983826408085833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37152889502645101877447777 27864667126983826408085833)
    ·
      refine ⟨20898500345237869806064375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27864667126983826408085833 20898500345237869806064375)
      ·
        refine ⟨31347750517856804709096563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20898500345237869806064375 31347750517856804709096563)
        ·
          refine ⟨47021625776785207063644845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31347750517856804709096563 47021625776785207063644845)
          ·
            refine ⟨17633109666294452648866817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47021625776785207063644845 17633109666294452648866817)
            ·
              refine ⟨13224832249720839486650113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17633109666294452648866817 13224832249720839486650113)
              ·
                refine ⟨9918624187290629614987585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13224832249720839486650113 9918624187290629614987585)
                ·
                  refine ⟨7438968140467972211240689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9918624187290629614987585 7438968140467972211240689)
                  ·
                    refine ⟨5579226105350979158430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438968140467972211240689 5579226105350979158430517)
                    ·
                      refine ⟨523052447376654296102861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5579226105350979158430517 523052447376654296102861)
                      ·
                        rfl

theorem cell23_1018641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_1018641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018641 prefixEnd_1018641 := by exact prefixLift 1018641
  have htrace : WordTrace (prefixWord ++ tailWord_1018641) baseStart_1018641 baseEnd_1018641 := by
    simpa [prefixWord, tailWord_1018641, baseEnd_1018641] using wordTrace_append hprefix tailTrace_1018641
  have hstable : (prefixWord ++ tailWord_1018641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018641).length < 2 ^ (prefixWord ++ tailWord_1018641).sum := by decide
  have hdescent : baseEnd_1018641 < baseStart_1018641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018655 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 3, 3, 2]
def baseStart_1018655 : Nat := 118140960795 + 1018655 * 2 ^ 59
def prefixEnd_1018655 : Nat := 4983230072969 + 3 ^ 40 * 1018655 * 2
def baseEnd_1018655 : Nat := 523059636105817241327797

theorem tailTrace_1018655 : CollatzResearch.WordTrace tailWord_1018655 prefixEnd_1018655 523059636105817241327797 := by
  unfold tailWord_1018655
  simp only [CollatzResearch.WordTrace]
  refine ⟨37153400124594382268457419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24768933416396254845638279 37153400124594382268457419)
  ·
    refine ⟨55730100186891573402686129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37153400124594382268457419 55730100186891573402686129)
    ·
      refine ⟨41797575140168680052014597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55730100186891573402686129 41797575140168680052014597)
      ·
        refine ⟨7837045338781627509752737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41797575140168680052014597 7837045338781627509752737)
        ·
          refine ⟨5877784004086220632314553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7837045338781627509752737 5877784004086220632314553)
          ·
            refine ⟨4408338003064665474235915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5877784004086220632314553 4408338003064665474235915)
            ·
              refine ⟨6612507004596998211353873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408338003064665474235915 6612507004596998211353873)
              ·
                refine ⟨4959380253447748658515405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612507004596998211353873 4959380253447748658515405)
                ·
                  refine ⟨1859767595042905746943277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4959380253447748658515405 1859767595042905746943277)
                  ·
                    refine ⟨697412848141089655103729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1859767595042905746943277 697412848141089655103729)
                    ·
                      refine ⟨523059636105817241327797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697412848141089655103729 523059636105817241327797)
                      ·
                        rfl

theorem cell23_1018655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_1018655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018655 prefixEnd_1018655 := by exact prefixLift 1018655
  have htrace : WordTrace (prefixWord ++ tailWord_1018655) baseStart_1018655 baseEnd_1018655 := by
    simpa [prefixWord, tailWord_1018655, baseEnd_1018655] using wordTrace_append hprefix tailTrace_1018655
  have hstable : (prefixWord ++ tailWord_1018655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018655).length < 2 ^ (prefixWord ++ tailWord_1018655).sum := by decide
  have hdescent : baseEnd_1018655 < baseStart_1018655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018691 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 9]
def baseStart_1018691 : Nat := 118140960795 + 1018691 * 2 ^ 59
def prefixEnd_1018691 : Nat := 4983230072969 + 3 ^ 40 * 1018691 * 2
def baseEnd_1018691 : Nat := 58119791267708788941959

theorem tailTrace_1018691 : CollatzResearch.WordTrace tailWord_1018691 prefixEnd_1018691 58119791267708788941959 := by
  unfold tailWord_1018691
  simp only [CollatzResearch.WordTrace]
  refine ⟨37154713152463960416767927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24769808768309306944511951 37154713152463960416767927)
  ·
    refine ⟨55732069728695940625151891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37154713152463960416767927 55732069728695940625151891)
    ·
      refine ⟨83598104593043910937727837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55732069728695940625151891 83598104593043910937727837)
      ·
        refine ⟨31349289222391466601647939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83598104593043910937727837 31349289222391466601647939)
        ·
          refine ⟨47023933833587199902471909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31349289222391466601647939 47023933833587199902471909)
          ·
            refine ⟨8816987593797599981713483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47023933833587199902471909 8816987593797599981713483)
            ·
              refine ⟨13225481390696399972570225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816987593797599981713483 13225481390696399972570225)
              ·
                refine ⟨9919111043022299979427669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13225481390696399972570225 9919111043022299979427669)
                ·
                  refine ⟨58119791267708788941959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9919111043022299979427669 58119791267708788941959)
                  ·
                    rfl

theorem cell23_1018691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 9].length) (baseStart_1018691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018691 prefixEnd_1018691 := by exact prefixLift 1018691
  have htrace : WordTrace (prefixWord ++ tailWord_1018691) baseStart_1018691 baseEnd_1018691 := by
    simpa [prefixWord, tailWord_1018691, baseEnd_1018691] using wordTrace_append hprefix tailTrace_1018691
  have hstable : (prefixWord ++ tailWord_1018691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018691).length < 2 ^ (prefixWord ++ tailWord_1018691).sum := by decide
  have hdescent : baseEnd_1018691 < baseStart_1018691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018719 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 2, 2, 2]
def baseStart_1018719 : Nat := 118140960795 + 1018719 * 2 ^ 59
def prefixEnd_1018719 : Nat := 4983230072969 + 3 ^ 40 * 1018719 * 2
def baseEnd_1018719 : Nat := 523092498867704990927503

theorem tailTrace_1018719 : CollatzResearch.WordTrace tailWord_1018719 prefixEnd_1018719 523092498867704990927503 := by
  unfold tailWord_1018719
  simp only [CollatzResearch.WordTrace]
  refine ⟨37155734396362521198787211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24770489597575014132524807 37155734396362521198787211)
  ·
    refine ⟨55733601594543781798180817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37155734396362521198787211 55733601594543781798180817)
    ·
      refine ⟨41800201195907836348635613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55733601594543781798180817 41800201195907836348635613)
      ·
        refine ⟨15675075448465438630738355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41800201195907836348635613 15675075448465438630738355)
        ·
          refine ⟨23512613172698157946107533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15675075448465438630738355 23512613172698157946107533)
          ·
            refine ⟨8817229939761809229790325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23512613172698157946107533 8817229939761809229790325)
            ·
              refine ⟨826615306852669615292843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8817229939761809229790325 826615306852669615292843)
              ·
                refine ⟨1239922960279004422939265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826615306852669615292843 1239922960279004422939265)
                ·
                  refine ⟨929942220209253317204449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239922960279004422939265 929942220209253317204449)
                  ·
                    refine ⟨697456665156939987903337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929942220209253317204449 697456665156939987903337)
                    ·
                      refine ⟨523092498867704990927503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697456665156939987903337 523092498867704990927503)
                      ·
                        rfl

theorem cell23_1018719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_1018719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018719 prefixEnd_1018719 := by exact prefixLift 1018719
  have htrace : WordTrace (prefixWord ++ tailWord_1018719) baseStart_1018719 baseEnd_1018719 := by
    simpa [prefixWord, tailWord_1018719, baseEnd_1018719] using wordTrace_append hprefix tailTrace_1018719
  have hstable : (prefixWord ++ tailWord_1018719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018719).length < 2 ^ (prefixWord ++ tailWord_1018719).sum := by decide
  have hdescent : baseEnd_1018719 < baseStart_1018719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018738 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1018738 : Nat := 118140960795 + 1018738 * 2 ^ 59
def prefixEnd_1018738 : Nat := 4983230072969 + 3 ^ 40 * 1018738 * 2
def baseEnd_1018738 : Nat := 174367418333380138863305

theorem tailTrace_1018738 : CollatzResearch.WordTrace tailWord_1018738 prefixEnd_1018738 174367418333380138863305 := by
  unfold tailWord_1018738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289106845823421860932217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24770951588862458295819245 9289106845823421860932217)
  ·
    refine ⟨6966830134367566395699163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9289106845823421860932217 6966830134367566395699163)
    ·
      refine ⟨10450245201551349593548745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6966830134367566395699163 10450245201551349593548745)
      ·
        refine ⟨7837683901163512195161559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10450245201551349593548745 7837683901163512195161559)
        ·
          refine ⟨11756525851745268292742339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837683901163512195161559 11756525851745268292742339)
          ·
            refine ⟨17634788777617902439113509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11756525851745268292742339 17634788777617902439113509)
            ·
              refine ⟨3306522895803356707333783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17634788777617902439113509 3306522895803356707333783)
              ·
                refine ⟨4959784343705035061000675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306522895803356707333783 4959784343705035061000675)
                ·
                  refine ⟨7439676515557552591501013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959784343705035061000675 7439676515557552591501013)
                  ·
                    refine ⟨174367418333380138863305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7439676515557552591501013 174367418333380138863305)
                    ·
                      rfl

theorem cell23_1018738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1018738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018738 prefixEnd_1018738 := by exact prefixLift 1018738
  have htrace : WordTrace (prefixWord ++ tailWord_1018738) baseStart_1018738 baseEnd_1018738 := by
    simpa [prefixWord, tailWord_1018738, baseEnd_1018738] using wordTrace_append hprefix tailTrace_1018738
  have hstable : (prefixWord ++ tailWord_1018738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018738).length < 2 ^ (prefixWord ++ tailWord_1018738).sum := by decide
  have hdescent : baseEnd_1018738 < baseStart_1018738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018770 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1018770 : Nat := 118140960795 + 1018770 * 2 ^ 59
def prefixEnd_1018770 : Nat := 4983230072969 + 3 ^ 40 * 1018770 * 2
def baseEnd_1018770 : Nat := 523118686381084291389769

theorem tailTrace_1018770 : CollatzResearch.WordTrace tailWord_1018770 prefixEnd_1018770 523118686381084291389769 := by
  unfold tailWord_1018770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289398629794439227223441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24771729679451837939262509 9289398629794439227223441)
  ·
    refine ⟨6967048972345829420417581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9289398629794439227223441 6967048972345829420417581)
    ·
      refine ⟨2612643364629686032656593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6967048972345829420417581 2612643364629686032656593)
      ·
        refine ⟨1959482523472264524492445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2612643364629686032656593 1959482523472264524492445)
        ·
          refine ⟨734805946302099196684667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1959482523472264524492445 734805946302099196684667)
          ·
            refine ⟨1102208919453148795027001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734805946302099196684667 1102208919453148795027001)
            ·
              refine ⟨826656689589861596270251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102208919453148795027001 826656689589861596270251)
              ·
                refine ⟨1239985034384792394405377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826656689589861596270251 1239985034384792394405377)
                ·
                  refine ⟨929988775788594295804033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239985034384792394405377 929988775788594295804033)
                  ·
                    refine ⟨697491581841445721853025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929988775788594295804033 697491581841445721853025)
                    ·
                      refine ⟨523118686381084291389769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697491581841445721853025 523118686381084291389769)
                      ·
                        rfl

theorem cell23_1018770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1018770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018770 prefixEnd_1018770 := by exact prefixLift 1018770
  have htrace : WordTrace (prefixWord ++ tailWord_1018770) baseStart_1018770 baseEnd_1018770 := by
    simpa [prefixWord, tailWord_1018770, baseEnd_1018770] using wordTrace_append hprefix tailTrace_1018770
  have hstable : (prefixWord ++ tailWord_1018770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018770).length < 2 ^ (prefixWord ++ tailWord_1018770).sum := by decide
  have hdescent : baseEnd_1018770 < baseStart_1018770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018775 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_1018775 : Nat := 118140960795 + 1018775 * 2 ^ 59
def prefixEnd_1018775 : Nat := 4983230072969 + 3 ^ 40 * 1018775 * 2
def baseEnd_1018775 : Nat := 523121253784356771827245

theorem tailTrace_1018775 : CollatzResearch.WordTrace tailWord_1018775 prefixEnd_1018775 523121253784356771827245 := by
  unfold tailWord_1018775
  simp only [CollatzResearch.WordTrace]
  refine ⟨37157776884159642762825779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24771851256106428508550519 37157776884159642762825779)
  ·
    refine ⟨55736665326239464144238669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37157776884159642762825779 55736665326239464144238669)
    ·
      refine ⟨20901249497339799054089501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55736665326239464144238669 20901249497339799054089501)
      ·
        refine ⟨7837968561502424645283563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20901249497339799054089501 7837968561502424645283563)
        ·
          refine ⟨11756952842253636967925345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837968561502424645283563 11756952842253636967925345)
          ·
            refine ⟨8817714631690227725944009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11756952842253636967925345 8817714631690227725944009)
            ·
              refine ⟨6613285973767670794458007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8817714631690227725944009 6613285973767670794458007)
              ·
                refine ⟨9919928960651506191687011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613285973767670794458007 9919928960651506191687011)
                ·
                  refine ⟨14879893440977259287530517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919928960651506191687011 14879893440977259287530517)
                  ·
                    refine ⟨697495005045809029102993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14879893440977259287530517 697495005045809029102993)
                    ·
                      refine ⟨523121253784356771827245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697495005045809029102993 523121253784356771827245)
                      ·
                        rfl

theorem cell23_1018775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_1018775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018775 prefixEnd_1018775 := by exact prefixLift 1018775
  have htrace : WordTrace (prefixWord ++ tailWord_1018775) baseStart_1018775 baseEnd_1018775 := by
    simpa [prefixWord, tailWord_1018775, baseEnd_1018775] using wordTrace_append hprefix tailTrace_1018775
  have hstable : (prefixWord ++ tailWord_1018775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018775).length < 2 ^ (prefixWord ++ tailWord_1018775).sum := by decide
  have hdescent : baseEnd_1018775 < baseStart_1018775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018842 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_1018842 : Nat := 118140960795 + 1018842 * 2 ^ 59
def prefixEnd_1018842 : Nat := 4983230072969 + 3 ^ 40 * 1018842 * 2
def baseEnd_1018842 : Nat := 523155656988208009689437

theorem tailTrace_1018842 : CollatzResearch.WordTrace tailWord_1018842 prefixEnd_1018842 523155656988208009689437 := by
  unfold tailWord_1018842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290055143729228301378695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24773480383277942137009853 9290055143729228301378695)
  ·
    refine ⟨13935082715593842452068043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290055143729228301378695 13935082715593842452068043)
    ·
      refine ⟨20902624073390763678102065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13935082715593842452068043 20902624073390763678102065)
      ·
        refine ⟨15676968055043072758576549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20902624073390763678102065 15676968055043072758576549)
        ·
          refine ⟨2939431510320576142233103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15676968055043072758576549 2939431510320576142233103)
          ·
            refine ⟨4409147265480864213349655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939431510320576142233103 4409147265480864213349655)
            ·
              refine ⟨6613720898221296320024483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409147265480864213349655 6613720898221296320024483)
              ·
                refine ⟨9920581347331944480036725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613720898221296320024483 9920581347331944480036725)
                ·
                  refine ⟨930054501312369795003443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9920581347331944480036725 930054501312369795003443)
                  ·
                    refine ⟨1395081751968554692505165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930054501312369795003443 1395081751968554692505165)
                    ·
                      refine ⟨523155656988208009689437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395081751968554692505165 523155656988208009689437)
                      ·
                        rfl

theorem cell23_1018842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_1018842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018842 prefixEnd_1018842 := by exact prefixLift 1018842
  have htrace : WordTrace (prefixWord ++ tailWord_1018842) baseStart_1018842 baseEnd_1018842 := by
    simpa [prefixWord, tailWord_1018842, baseEnd_1018842] using wordTrace_append hprefix tailTrace_1018842
  have hstable : (prefixWord ++ tailWord_1018842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018842).length < 2 ^ (prefixWord ++ tailWord_1018842).sum := by decide
  have hdescent : baseEnd_1018842 < baseStart_1018842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018852 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_1018852 : Nat := 118140960795 + 1018852 * 2 ^ 59
def prefixEnd_1018852 : Nat := 4983230072969 + 3 ^ 40 * 1018852 * 2
def baseEnd_1018852 : Nat := 523160791794752970564391

theorem tailTrace_1018852 : CollatzResearch.WordTrace tailWord_1018852 prefixEnd_1018852 523160791794752970564391 := by
  unfold tailWord_1018852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18580292652440342456689405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24773723536587123275585873 18580292652440342456689405)
  ·
    refine ⟨6967609744665128421258527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18580292652440342456689405 6967609744665128421258527)
    ·
      refine ⟨10451414616997692631887791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967609744665128421258527 10451414616997692631887791)
      ·
        refine ⟨15677121925496538947831687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451414616997692631887791 15677121925496538947831687)
        ·
          refine ⟨23515682888244808421747531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677121925496538947831687 23515682888244808421747531)
          ·
            refine ⟨35273524332367212632621297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23515682888244808421747531 35273524332367212632621297)
            ·
              refine ⟨26455143249275409474465973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35273524332367212632621297 26455143249275409474465973)
              ·
                refine ⟨2480169679619569638231185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26455143249275409474465973 2480169679619569638231185)
                ·
                  refine ⟨1860127259714677228673389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480169679619569638231185 1860127259714677228673389)
                  ·
                    refine ⟨697547722393003960752521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860127259714677228673389 697547722393003960752521)
                    ·
                      refine ⟨523160791794752970564391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697547722393003960752521 523160791794752970564391)
                      ·
                        rfl

theorem cell23_1018852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_1018852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018852 prefixEnd_1018852 := by exact prefixLift 1018852
  have htrace : WordTrace (prefixWord ++ tailWord_1018852) baseStart_1018852 baseEnd_1018852 := by
    simpa [prefixWord, tailWord_1018852, baseEnd_1018852] using wordTrace_append hprefix tailTrace_1018852
  have hstable : (prefixWord ++ tailWord_1018852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018852).length < 2 ^ (prefixWord ++ tailWord_1018852).sum := by decide
  have hdescent : baseEnd_1018852 < baseStart_1018852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018866 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_1018866 : Nat := 118140960795 + 1018866 * 2 ^ 59
def prefixEnd_1018866 : Nat := 4983230072969 + 3 ^ 40 * 1018866 * 2
def baseEnd_1018866 : Nat := 58129775613768435087703

theorem tailTrace_1018866 : CollatzResearch.WordTrace tailWord_1018866 prefixEnd_1018866 58129775613768435087703 := by
  unfold tailWord_1018866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290273981707491326097113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24774063951219976869592301 9290273981707491326097113)
  ·
    refine ⟨6967705486280618494572835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9290273981707491326097113 6967705486280618494572835)
    ·
      refine ⟨10451558229420927741859253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967705486280618494572835 10451558229420927741859253)
      ·
        refine ⟨979833584008211975799305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10451558229420927741859253 979833584008211975799305)
        ·
          refine ⟨734875188006158981849479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979833584008211975799305 734875188006158981849479)
          ·
            refine ⟨1102312782009238472774219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734875188006158981849479 1102312782009238472774219)
            ·
              refine ⟨1653469173013857709161329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102312782009238472774219 1653469173013857709161329)
              ·
                refine ⟨1240101879760393281870997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653469173013857709161329 1240101879760393281870997)
                ·
                  refine ⟨58129775613768435087703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1240101879760393281870997 58129775613768435087703)
                  ·
                    rfl

theorem cell23_1018866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_1018866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018866 prefixEnd_1018866 := by exact prefixLift 1018866
  have htrace : WordTrace (prefixWord ++ tailWord_1018866) baseStart_1018866 baseEnd_1018866 := by
    simpa [prefixWord, tailWord_1018866, baseEnd_1018866] using wordTrace_append hprefix tailTrace_1018866
  have hstable : (prefixWord ++ tailWord_1018866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018866).length < 2 ^ (prefixWord ++ tailWord_1018866).sum := by decide
  have hdescent : baseEnd_1018866 < baseStart_1018866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018885 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_1018885 : Nat := 118140960795 + 1018885 * 2 ^ 59
def prefixEnd_1018885 : Nat := 4983230072969 + 3 ^ 40 * 1018885 * 2
def baseEnd_1018885 : Nat := 523177736656351341451739

theorem tailTrace_1018885 : CollatzResearch.WordTrace tailWord_1018885 prefixEnd_1018885 523177736656351341451739 := by
  unfold tailWord_1018885
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161788913761131549330109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24774525942507421032886739 37161788913761131549330109)
  ·
    refine ⟨13935670842660424330998791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37161788913761131549330109 13935670842660424330998791)
    ·
      refine ⟨20903506263990636496498187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13935670842660424330998791 20903506263990636496498187)
      ·
        refine ⟨31355259395985954744747281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20903506263990636496498187 31355259395985954744747281)
        ·
          refine ⟨23516444546989466058560461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31355259395985954744747281 23516444546989466058560461)
          ·
            refine ⟨8818666705121049771960173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23516444546989466058560461 8818666705121049771960173)
            ·
              refine ⟨3307000014420393664485065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8818666705121049771960173 3307000014420393664485065)
              ·
                refine ⟨2480250010815295248363799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307000014420393664485065 2480250010815295248363799)
                ·
                  refine ⟨3720375016222942872545699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480250010815295248363799 3720375016222942872545699)
                  ·
                    refine ⟨5580562524334414308818549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720375016222942872545699 5580562524334414308818549)
                    ·
                      refine ⟨523177736656351341451739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5580562524334414308818549 523177736656351341451739)
                      ·
                        rfl

theorem cell23_1018885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_1018885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018885 prefixEnd_1018885 := by exact prefixLift 1018885
  have htrace : WordTrace (prefixWord ++ tailWord_1018885) baseStart_1018885 baseEnd_1018885 := by
    simpa [prefixWord, tailWord_1018885, baseEnd_1018885] using wordTrace_append hprefix tailTrace_1018885
  have hstable : (prefixWord ++ tailWord_1018885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018885).length < 2 ^ (prefixWord ++ tailWord_1018885).sum := by decide
  have hdescent : baseEnd_1018885 < baseStart_1018885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018892 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_1018892 : Nat := 118140960795 + 1018892 * 2 ^ 59
def prefixEnd_1018892 : Nat := 4983230072969 + 3 ^ 40 * 1018892 * 2
def baseEnd_1018892 : Nat := 174393777006977604688069

theorem tailTrace_1018892 : CollatzResearch.WordTrace tailWord_1018892 prefixEnd_1018892 174393777006977604688069 := by
  unfold tailWord_1018892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581022112367885872417465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24774696149823847829889953 18581022112367885872417465)
  ·
    refine ⟨13935766584275914404313099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18581022112367885872417465 13935766584275914404313099)
    ·
      refine ⟨20903649876413871606469649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13935766584275914404313099 20903649876413871606469649)
      ·
        refine ⟨15677737407310403704852237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20903649876413871606469649 15677737407310403704852237)
        ·
          refine ⟨5879151527741401389319589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15677737407310403704852237 5879151527741401389319589)
          ·
            refine ⟨1102340911451512760497423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5879151527741401389319589 1102340911451512760497423)
            ·
              refine ⟨1653511367177269140746135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102340911451512760497423 1653511367177269140746135)
              ·
                refine ⟨2480267050765903711119203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653511367177269140746135 2480267050765903711119203)
                ·
                  refine ⟨3720400576148855566678805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480267050765903711119203 3720400576148855566678805)
                  ·
                    refine ⟨174393777006977604688069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3720400576148855566678805 174393777006977604688069)
                    ·
                      rfl

theorem cell23_1018892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_1018892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018892 prefixEnd_1018892 := by exact prefixLift 1018892
  have htrace : WordTrace (prefixWord ++ tailWord_1018892) baseStart_1018892 baseEnd_1018892 := by
    simpa [prefixWord, tailWord_1018892, baseEnd_1018892] using wordTrace_append hprefix tailTrace_1018892
  have hstable : (prefixWord ++ tailWord_1018892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018892).length < 2 ^ (prefixWord ++ tailWord_1018892).sum := by decide
  have hdescent : baseEnd_1018892 < baseStart_1018892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018905 : List Nat := [1, 2, 1, 2, 1, 1, 8, 7]
def baseStart_1018905 : Nat := 118140960795 + 1018905 * 2 ^ 59
def prefixEnd_1018905 : Nat := 4983230072969 + 3 ^ 40 * 1018905 * 2
def baseEnd_1018905 : Nat := 19377333565534861600061

theorem tailTrace_1018905 : CollatzResearch.WordTrace tailWord_1018905 prefixEnd_1018905 19377333565534861600061 := by
  unfold tailWord_1018905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162518373688674965058169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24775012249125783310038779 37162518373688674965058169)
  ·
    refine ⟨27871888780266506223793627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37162518373688674965058169 27871888780266506223793627)
    ·
      refine ⟨41807833170399759335690441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27871888780266506223793627 41807833170399759335690441)
      ·
        refine ⟨31355874877799819501767831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41807833170399759335690441 31355874877799819501767831)
        ·
          refine ⟨47033812316699729252651747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31355874877799819501767831 47033812316699729252651747)
          ·
            refine ⟨70550718475049593878977621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47033812316699729252651747 70550718475049593878977621)
            ·
              refine ⟨826766232129487428269269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 70550718475049593878977621 826766232129487428269269)
              ·
                refine ⟨19377333565534861600061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 826766232129487428269269 19377333565534861600061)
                ·
                  rfl

theorem cell23_1018905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 7].length) (baseStart_1018905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018905 prefixEnd_1018905 := by exact prefixLift 1018905
  have htrace : WordTrace (prefixWord ++ tailWord_1018905) baseStart_1018905 baseEnd_1018905 := by
    simpa [prefixWord, tailWord_1018905, baseEnd_1018905] using wordTrace_append hprefix tailTrace_1018905
  have hstable : (prefixWord ++ tailWord_1018905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018905).length < 2 ^ (prefixWord ++ tailWord_1018905).sum := by decide
  have hdescent : baseEnd_1018905 < baseStart_1018905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018919 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1018919 : Nat := 118140960795 + 1018919 * 2 ^ 59
def prefixEnd_1018919 : Nat := 4983230072969 + 3 ^ 40 * 1018919 * 2
def baseEnd_1018919 : Nat := 523195194998604208426583

theorem tailTrace_1018919 : CollatzResearch.WordTrace tailWord_1018919 prefixEnd_1018919 523195194998604208426583 := by
  unfold tailWord_1018919
  simp only [CollatzResearch.WordTrace]
  refine ⟨37163028995637955356067811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24775352663758636904045207 37163028995637955356067811)
  ·
    refine ⟨55744543493456933034101717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37163028995637955356067811 55744543493456933034101717)
    ·
      refine ⟨1306512738127896867986759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55744543493456933034101717 1306512738127896867986759)
      ·
        refine ⟨1959769107191845301980139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306512738127896867986759 1959769107191845301980139)
        ·
          refine ⟨2939653660787767952970209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959769107191845301980139 2939653660787767952970209)
          ·
            refine ⟨2204740245590825964727657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939653660787767952970209 2204740245590825964727657)
            ·
              refine ⟨1653555184193119473545743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204740245590825964727657 1653555184193119473545743)
              ·
                refine ⟨2480332776289679210318615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653555184193119473545743 2480332776289679210318615)
                ·
                  refine ⟨3720499164434518815477923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480332776289679210318615 3720499164434518815477923)
                  ·
                    refine ⟨5580748746651778223216885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720499164434518815477923 5580748746651778223216885)
                    ·
                      refine ⟨523195194998604208426583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5580748746651778223216885 523195194998604208426583)
                      ·
                        rfl

theorem cell23_1018919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1018919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018919 prefixEnd_1018919 := by exact prefixLift 1018919
  have htrace : WordTrace (prefixWord ++ tailWord_1018919) baseStart_1018919 baseEnd_1018919 := by
    simpa [prefixWord, tailWord_1018919, baseEnd_1018919] using wordTrace_append hprefix tailTrace_1018919
  have hstable : (prefixWord ++ tailWord_1018919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018919).length < 2 ^ (prefixWord ++ tailWord_1018919).sum := by decide
  have hdescent : baseEnd_1018919 < baseStart_1018919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018922 : List Nat := [3, 1, 4, 1, 3, 2, 9]
def baseStart_1018922 : Nat := 118140960795 + 1018922 * 2 ^ 59
def prefixEnd_1018922 : Nat := 4983230072969 + 3 ^ 40 * 1018922 * 2
def baseEnd_1018922 : Nat := 6459218956056391317149

theorem tailTrace_1018922 : CollatzResearch.WordTrace tailWord_1018922 prefixEnd_1018922 6459218956056391317149 := by
  unfold tailWord_1018922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290784603656771717106755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24775425609751391245618013 9290784603656771717106755)
  ·
    refine ⟨13936176905485157575660133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290784603656771717106755 13936176905485157575660133)
    ·
      refine ⟨2613033169778467045436275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13936176905485157575660133 2613033169778467045436275)
      ·
        refine ⟨3919549754667700568154413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613033169778467045436275 3919549754667700568154413)
        ·
          refine ⟨1469831158000387713057905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3919549754667700568154413 1469831158000387713057905)
          ·
            refine ⟨1102373368500290784793429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469831158000387713057905 1102373368500290784793429)
            ·
              refine ⟨6459218956056391317149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1102373368500290784793429 6459218956056391317149)
              ·
                rfl

theorem cell23_1018922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 9].length) (baseStart_1018922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018922 prefixEnd_1018922 := by exact prefixLift 1018922
  have htrace : WordTrace (prefixWord ++ tailWord_1018922) baseStart_1018922 baseEnd_1018922 := by
    simpa [prefixWord, tailWord_1018922, baseEnd_1018922] using wordTrace_append hprefix tailTrace_1018922
  have hstable : (prefixWord ++ tailWord_1018922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018922).length < 2 ^ (prefixWord ++ tailWord_1018922).sum := by decide
  have hdescent : baseEnd_1018922 < baseStart_1018922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018975 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1018975 : Nat := 118140960795 + 1018975 * 2 ^ 59
def prefixEnd_1018975 : Nat := 4983230072969 + 3 ^ 40 * 1018975 * 2
def baseEnd_1018975 : Nat := 523223949915255989326325

theorem tailTrace_1018975 : CollatzResearch.WordTrace tailWord_1018975 prefixEnd_1018975 523223949915255989326325 := by
  unfold tailWord_1018975
  simp only [CollatzResearch.WordTrace]
  refine ⟨37165071483435076920106379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24776714322290051280070919 37165071483435076920106379)
  ·
    refine ⟨55747607225152615380159569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37165071483435076920106379 55747607225152615380159569)
    ·
      refine ⟨41810705418864461535119677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55747607225152615380159569 41810705418864461535119677)
      ·
        refine ⟨15679014532074173075669879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41810705418864461535119677 15679014532074173075669879)
        ·
          refine ⟨23518521798111259613504819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679014532074173075669879 23518521798111259613504819)
          ·
            refine ⟨35277782697166889420257229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518521798111259613504819 35277782697166889420257229)
            ·
              refine ⟨13229168511437583532596461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35277782697166889420257229 13229168511437583532596461)
              ·
                refine ⟨4960938191789093824723673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13229168511437583532596461 4960938191789093824723673)
                ·
                  refine ⟨3720703643841820368542755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960938191789093824723673 3720703643841820368542755)
                  ·
                    refine ⟨5581055465762730552814133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720703643841820368542755 5581055465762730552814133)
                    ·
                      refine ⟨523223949915255989326325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5581055465762730552814133 523223949915255989326325)
                      ·
                        rfl

theorem cell23_1018975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1018975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018975 prefixEnd_1018975 := by exact prefixLift 1018975
  have htrace : WordTrace (prefixWord ++ tailWord_1018975) baseStart_1018975 baseEnd_1018975 := by
    simpa [prefixWord, tailWord_1018975, baseEnd_1018975] using wordTrace_append hprefix tailTrace_1018975
  have hstable : (prefixWord ++ tailWord_1018975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018975).length < 2 ^ (prefixWord ++ tailWord_1018975).sum := by decide
  have hdescent : baseEnd_1018975 < baseStart_1018975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018976 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2]
def baseStart_1018976 : Nat := 118140960795 + 1018976 * 2 ^ 59
def prefixEnd_1018976 : Nat := 4983230072969 + 3 ^ 40 * 1018976 * 2
def baseEnd_1018976 : Nat := 523224463395910485413821

theorem tailTrace_1018976 : CollatzResearch.WordTrace tailWord_1018976 prefixEnd_1018976 523224463395910485413821 := by
  unfold tailWord_1018976
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582553978215727045446391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24776738637620969393928521 18582553978215727045446391)
  ·
    refine ⟨27873830967323590568169587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582553978215727045446391 27873830967323590568169587)
    ·
      refine ⟨41810746450985385852254381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27873830967323590568169587 41810746450985385852254381)
      ·
        refine ⟨15679029919119519694595393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41810746450985385852254381 15679029919119519694595393)
        ·
          refine ⟨11759272439339639770946545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15679029919119519694595393 11759272439339639770946545)
          ·
            refine ⟨8819454329504729828209909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11759272439339639770946545 8819454329504729828209909)
            ·
              refine ⟨826823843391068421394679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8819454329504729828209909 826823843391068421394679)
              ·
                refine ⟨1240235765086602632092019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826823843391068421394679 1240235765086602632092019)
                ·
                  refine ⟨1860353647629903948138029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240235765086602632092019 1860353647629903948138029)
                  ·
                    refine ⟨697632617861213980551761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1860353647629903948138029 697632617861213980551761)
                    ·
                      refine ⟨523224463395910485413821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697632617861213980551761 523224463395910485413821)
                      ·
                        rfl

theorem cell23_1018976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_1018976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018976 prefixEnd_1018976 := by exact prefixLift 1018976
  have htrace : WordTrace (prefixWord ++ tailWord_1018976) baseStart_1018976 baseEnd_1018976 := by
    simpa [prefixWord, tailWord_1018976, baseEnd_1018976] using wordTrace_append hprefix tailTrace_1018976
  have hstable : (prefixWord ++ tailWord_1018976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018976).length < 2 ^ (prefixWord ++ tailWord_1018976).sum := by decide
  have hdescent : baseEnd_1018976 < baseStart_1018976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018984 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1018984 : Nat := 118140960795 + 1018984 * 2 ^ 59
def prefixEnd_1018984 : Nat := 4983230072969 + 3 ^ 40 * 1018984 * 2
def baseEnd_1018984 : Nat := 523228571241146454113785

theorem tailTrace_1018984 : CollatzResearch.WordTrace tailWord_1018984 prefixEnd_1018984 523228571241146454113785 := by
  unfold tailWord_1018984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582699870201235728592003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24776933160268314304789337 18582699870201235728592003)
  ·
    refine ⟨27874049805301853592888005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582699870201235728592003 27874049805301853592888005)
    ·
      refine ⟨5226384338494097548666501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27874049805301853592888005 5226384338494097548666501)
      ·
        refine ⟨979947063467643290374969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5226384338494097548666501 979947063467643290374969)
        ·
          refine ⟨734960297600732467781227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979947063467643290374969 734960297600732467781227)
          ·
            refine ⟨1102440446401098701671841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734960297600732467781227 1102440446401098701671841)
            ·
              refine ⟨826830334800824026253881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102440446401098701671841 826830334800824026253881)
              ·
                refine ⟨620122751100618019690411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826830334800824026253881 620122751100618019690411)
                ·
                  refine ⟨930184126650927029535617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620122751100618019690411 930184126650927029535617)
                  ·
                    refine ⟨697638094988195272151713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 930184126650927029535617 697638094988195272151713)
                    ·
                      refine ⟨523228571241146454113785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697638094988195272151713 523228571241146454113785)
                      ·
                        rfl

theorem cell23_1018984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1018984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1018984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1018984 prefixEnd_1018984 := by exact prefixLift 1018984
  have htrace : WordTrace (prefixWord ++ tailWord_1018984) baseStart_1018984 baseEnd_1018984 := by
    simpa [prefixWord, tailWord_1018984, baseEnd_1018984] using wordTrace_append hprefix tailTrace_1018984
  have hstable : (prefixWord ++ tailWord_1018984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018984).length < 2 ^ (prefixWord ++ tailWord_1018984).sum := by decide
  have hdescent : baseEnd_1018984 < baseStart_1018984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019012 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1019012 : Nat := 118140960795 + 1019012 * 2 ^ 59
def prefixEnd_1019012 : Nat := 4983230072969 + 3 ^ 40 * 1019012 * 2
def baseEnd_1019012 : Nat := 58138105411052482729295

theorem tailTrace_1019012 : CollatzResearch.WordTrace tailWord_1019012 prefixEnd_1019012 58138105411052482729295 := by
  unfold tailWord_1019012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18583210492150516119601645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24777613989534021492802193 18583210492150516119601645)
  ·
    refine ⟨6968703934556443544850617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18583210492150516119601645 6968703934556443544850617)
    ·
      refine ⟨5226527950917332658637963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6968703934556443544850617 5226527950917332658637963)
      ·
        refine ⟨7839791926375998987956945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226527950917332658637963 7839791926375998987956945)
        ·
          refine ⟨5879843944781999240967709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7839791926375998987956945 5879843944781999240967709)
          ·
            refine ⟨2204941479293249715362891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5879843944781999240967709 2204941479293249715362891)
            ·
              refine ⟨3307412218939874573044337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204941479293249715362891 3307412218939874573044337)
              ·
                refine ⟨2480559164204905929783253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307412218939874573044337 2480559164204905929783253)
                ·
                  refine ⟨58138105411052482729295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2480559164204905929783253 58138105411052482729295)
                  ·
                    rfl

theorem cell23_1019012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1019012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019012 prefixEnd_1019012 := by exact prefixLift 1019012
  have htrace : WordTrace (prefixWord ++ tailWord_1019012) baseStart_1019012 baseEnd_1019012 := by
    simpa [prefixWord, tailWord_1019012, baseEnd_1019012] using wordTrace_append hprefix tailTrace_1019012
  have hstable : (prefixWord ++ tailWord_1019012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019012).length < 2 ^ (prefixWord ++ tailWord_1019012).sum := by decide
  have hdescent : baseEnd_1019012 < baseStart_1019012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019075 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1019075 : Nat := 118140960795 + 1019075 * 2 ^ 59
def prefixEnd_1019075 : Nat := 4983230072969 + 3 ^ 40 * 1019075 * 2
def baseEnd_1019075 : Nat := 523275297980705598075865

theorem tailTrace_1019075 : CollatzResearch.WordTrace tailWord_1019075 prefixEnd_1019075 523275297980705598075865 := by
  unfold tailWord_1019075
  simp only [CollatzResearch.WordTrace]
  refine ⟨37168718783072793998746679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24779145855381862665831119 37168718783072793998746679)
  ·
    refine ⟨55753078174609190998120019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37168718783072793998746679 55753078174609190998120019)
    ·
      refine ⟨83629617261913786497180029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55753078174609190998120019 83629617261913786497180029)
      ·
        refine ⟨31361106473217669936442511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83629617261913786497180029 31361106473217669936442511)
        ·
          refine ⟨47041659709826504904663767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31361106473217669936442511 47041659709826504904663767)
          ·
            refine ⟨70562489564739757356995651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47041659709826504904663767 70562489564739757356995651)
            ·
              refine ⟨105843734347109636035493477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70562489564739757356995651 105843734347109636035493477)
              ·
                refine ⟨19845700190083056756655027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105843734347109636035493477 19845700190083056756655027)
                ·
                  refine ⟨29768550285124585134982541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19845700190083056756655027 29768550285124585134982541)
                  ·
                    refine ⟨11163206356921719425618453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29768550285124585134982541 11163206356921719425618453)
                    ·
                      refine ⟨523275297980705598075865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11163206356921719425618453 523275297980705598075865)
                      ·
                        rfl

theorem cell23_1019075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1019075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019075 prefixEnd_1019075 := by exact prefixLift 1019075
  have htrace : WordTrace (prefixWord ++ tailWord_1019075) baseStart_1019075 baseEnd_1019075 := by
    simpa [prefixWord, tailWord_1019075, baseEnd_1019075] using wordTrace_append hprefix tailTrace_1019075
  have hstable : (prefixWord ++ tailWord_1019075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019075).length < 2 ^ (prefixWord ++ tailWord_1019075).sum := by decide
  have hdescent : baseEnd_1019075 < baseStart_1019075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019119 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 6]
def baseStart_1019119 : Nat := 118140960795 + 1019119 * 2 ^ 59
def prefixEnd_1019119 : Nat := 4983230072969 + 3 ^ 40 * 1019119 * 2
def baseEnd_1019119 : Nat := 58144210125500380658407

theorem tailTrace_1019119 : CollatzResearch.WordTrace tailWord_1019119 prefixEnd_1019119 58144210125500380658407 := by
  unfold tailWord_1019119
  simp only [CollatzResearch.WordTrace]
  refine ⟨37170323594913389513348411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24780215729942259675565607 37170323594913389513348411)
  ·
    refine ⟨55755485392370084270022617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37170323594913389513348411 55755485392370084270022617)
    ·
      refine ⟨41816614044277563202516963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55755485392370084270022617 41816614044277563202516963)
      ·
        refine ⟨62724921066416344803775445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41816614044277563202516963 62724921066416344803775445)
        ·
          refine ⟨1470115337494133081338487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62724921066416344803775445 1470115337494133081338487)
          ·
            refine ⟨2205173006241199622007731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470115337494133081338487 2205173006241199622007731)
            ·
              refine ⟨3307759509361799433011597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205173006241199622007731 3307759509361799433011597)
              ·
                refine ⟨1240409816010674787379349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3307759509361799433011597 1240409816010674787379349)
                ·
                  refine ⟨58144210125500380658407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1240409816010674787379349 58144210125500380658407)
                  ·
                    rfl

theorem cell23_1019119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 6].length) (baseStart_1019119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019119 prefixEnd_1019119 := by exact prefixLift 1019119
  have htrace : WordTrace (prefixWord ++ tailWord_1019119) baseStart_1019119 baseEnd_1019119 := by
    simpa [prefixWord, tailWord_1019119, baseEnd_1019119] using wordTrace_append hprefix tailTrace_1019119
  have hstable : (prefixWord ++ tailWord_1019119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019119).length < 2 ^ (prefixWord ++ tailWord_1019119).sum := by decide
  have hdescent : baseEnd_1019119 < baseStart_1019119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019129 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 3]
def baseStart_1019129 : Nat := 118140960795 + 1019129 * 2 ^ 59
def prefixEnd_1019129 : Nat := 4983230072969 + 3 ^ 40 * 1019129 * 2
def baseEnd_1019129 : Nat := 523303025936048386800617

theorem tailTrace_1019129 : CollatzResearch.WordTrace tailWord_1019129 prefixEnd_1019129 523303025936048386800617 := by
  unfold tailWord_1019129
  simp only [CollatzResearch.WordTrace]
  refine ⟨37170688324877161221212441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24780458883251440814141627 37170688324877161221212441)
  ·
    refine ⟨27878016243657870915909331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37170688324877161221212441 27878016243657870915909331)
    ·
      refine ⟨41817024365486806373863997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27878016243657870915909331 41817024365486806373863997)
      ·
        refine ⟨15681384137057552390198999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41817024365486806373863997 15681384137057552390198999)
        ·
          refine ⟨23522076205586328585298499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681384137057552390198999 23522076205586328585298499)
          ·
            refine ⟨35283114308379492877947749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23522076205586328585298499 35283114308379492877947749)
            ·
              refine ⟨6615583932821154914615203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35283114308379492877947749 6615583932821154914615203)
              ·
                refine ⟨9923375899231732371922805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615583932821154914615203 9923375899231732371922805)
                ·
                  refine ⟨930316490552974909867763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9923375899231732371922805 930316490552974909867763)
                  ·
                    refine ⟨1395474735829462364801645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930316490552974909867763 1395474735829462364801645)
                    ·
                      refine ⟨523303025936048386800617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395474735829462364801645 523303025936048386800617)
                      ·
                        rfl

theorem cell23_1019129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_1019129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019129 prefixEnd_1019129 := by exact prefixLift 1019129
  have htrace : WordTrace (prefixWord ++ tailWord_1019129) baseStart_1019129 baseEnd_1019129 := by
    simpa [prefixWord, tailWord_1019129, baseEnd_1019129] using wordTrace_append hprefix tailTrace_1019129
  have hstable : (prefixWord ++ tailWord_1019129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019129).length < 2 ^ (prefixWord ++ tailWord_1019129).sum := by decide
  have hdescent : baseEnd_1019129 < baseStart_1019129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019169 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1019169 : Nat := 118140960795 + 1019169 * 2 ^ 59
def prefixEnd_1019169 : Nat := 4983230072969 + 3 ^ 40 * 1019169 * 2
def baseEnd_1019169 : Nat := 523323565162228230300433

theorem tailTrace_1019169 : CollatzResearch.WordTrace tailWord_1019169 prefixEnd_1019169 523323565162228230300433 := by
  unfold tailWord_1019169
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172147244732248052668561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24781431496488165368445707 37172147244732248052668561)
  ·
    refine ⟨27879110433549186039501421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37172147244732248052668561 27879110433549186039501421)
    ·
      refine ⟨10454666412580944764813033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27879110433549186039501421 10454666412580944764813033)
      ·
        refine ⟨7840999809435708573609775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10454666412580944764813033 7840999809435708573609775)
        ·
          refine ⟨11761499714153562860414663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840999809435708573609775 11761499714153562860414663)
          ·
            refine ⟨17642249571230344290621995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761499714153562860414663 17642249571230344290621995)
            ·
              refine ⟨26463374356845516435932993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642249571230344290621995 26463374356845516435932993)
              ·
                refine ⟨19847530767634137326949745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26463374356845516435932993 19847530767634137326949745)
                ·
                  refine ⟨14885648075725602995212309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19847530767634137326949745 14885648075725602995212309)
                  ·
                    refine ⟨697764753549637640400577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14885648075725602995212309 697764753549637640400577)
                    ·
                      refine ⟨523323565162228230300433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697764753549637640400577 523323565162228230300433)
                      ·
                        rfl

theorem cell23_1019169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1019169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019169 prefixEnd_1019169 := by exact prefixLift 1019169
  have htrace : WordTrace (prefixWord ++ tailWord_1019169) baseStart_1019169 baseEnd_1019169 := by
    simpa [prefixWord, tailWord_1019169, baseEnd_1019169] using wordTrace_append hprefix tailTrace_1019169
  have hstable : (prefixWord ++ tailWord_1019169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019169).length < 2 ^ (prefixWord ++ tailWord_1019169).sum := by decide
  have hdescent : baseEnd_1019169 < baseStart_1019169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019190 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1019190 : Nat := 118140960795 + 1019190 * 2 ^ 59
def prefixEnd_1019190 : Nat := 4983230072969 + 3 ^ 40 * 1019190 * 2
def baseEnd_1019190 : Nat := 523334348255972648137837

theorem tailTrace_1019190 : CollatzResearch.WordTrace tailWord_1019190 prefixEnd_1019190 523334348255972648137837 := by
  unfold tailWord_1019190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323307073603510539948939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24781942118437445759455349 2323307073603510539948939)
  ·
    refine ⟨3484960610405265809923409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323307073603510539948939 3484960610405265809923409)
    ·
      refine ⟨2613720457803949357442557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3484960610405265809923409 2613720457803949357442557)
      ·
        refine ⟨980145171676481009040959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2613720457803949357442557 980145171676481009040959)
        ·
          refine ⟨1470217757514721513561439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980145171676481009040959 1470217757514721513561439)
          ·
            refine ⟨2205326636272082270342159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470217757514721513561439 2205326636272082270342159)
            ·
              refine ⟨3307989954408123405513239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205326636272082270342159 3307989954408123405513239)
              ·
                refine ⟨4961984931612185108269859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307989954408123405513239 4961984931612185108269859)
                ·
                  refine ⟨7442977397418277662404789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961984931612185108269859 7442977397418277662404789)
                  ·
                    refine ⟨697779131007963530850449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442977397418277662404789 697779131007963530850449)
                    ·
                      refine ⟨523334348255972648137837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697779131007963530850449 523334348255972648137837)
                      ·
                        rfl

theorem cell23_1019190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1019190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019190 prefixEnd_1019190 := by exact prefixLift 1019190
  have htrace : WordTrace (prefixWord ++ tailWord_1019190) baseStart_1019190 baseEnd_1019190 := by
    simpa [prefixWord, tailWord_1019190, baseEnd_1019190] using wordTrace_append hprefix tailTrace_1019190
  have hstable : (prefixWord ++ tailWord_1019190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019190).length < 2 ^ (prefixWord ++ tailWord_1019190).sum := by decide
  have hdescent : baseEnd_1019190 < baseStart_1019190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019197 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1019197 : Nat := 118140960795 + 1019197 * 2 ^ 59
def prefixEnd_1019197 : Nat := 4983230072969 + 3 ^ 40 * 1019197 * 2
def baseEnd_1019197 : Nat := 523337942620554120750305

theorem tailTrace_1019197 : CollatzResearch.WordTrace tailWord_1019197 prefixEnd_1019197 523337942620554120750305 := by
  unfold tailWord_1019197
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173168488630808834687845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24782112325753872556458563 37173168488630808834687845)
  ·
    refine ⟨6969969091618276656503971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37173168488630808834687845 6969969091618276656503971)
    ·
      refine ⟨10454953637427414984755957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969969091618276656503971 10454953637427414984755957)
      ·
        refine ⟨980151903508820154820871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10454953637427414984755957 980151903508820154820871)
        ·
          refine ⟨1470227855263230232231307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980151903508820154820871 1470227855263230232231307)
          ·
            refine ⟨2205341782894845348346961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470227855263230232231307 2205341782894845348346961)
            ·
              refine ⟨1654006337171134011260221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205341782894845348346961 1654006337171134011260221)
              ·
                refine ⟨620252376439175254222583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654006337171134011260221 620252376439175254222583)
                ·
                  refine ⟨930378564658762881333875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620252376439175254222583 930378564658762881333875)
                  ·
                    refine ⟨1395567846988144322000813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930378564658762881333875 1395567846988144322000813)
                    ·
                      refine ⟨523337942620554120750305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395567846988144322000813 523337942620554120750305)
                      ·
                        rfl

theorem cell23_1019197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1019197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019197 prefixEnd_1019197 := by exact prefixLift 1019197
  have htrace : WordTrace (prefixWord ++ tailWord_1019197) baseStart_1019197 baseEnd_1019197 := by
    simpa [prefixWord, tailWord_1019197, baseEnd_1019197] using wordTrace_append hprefix tailTrace_1019197
  have hstable : (prefixWord ++ tailWord_1019197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019197).length < 2 ^ (prefixWord ++ tailWord_1019197).sum := by decide
  have hdescent : baseEnd_1019197 < baseStart_1019197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019199 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1019199 : Nat := 118140960795 + 1019199 * 2 ^ 59
def prefixEnd_1019199 : Nat := 4983230072969 + 3 ^ 40 * 1019199 * 2
def baseEnd_1019199 : Nat := 523338969581863112925295

theorem tailTrace_1019199 : CollatzResearch.WordTrace tailWord_1019199 prefixEnd_1019199 523338969581863112925295 := by
  unfold tailWord_1019199
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173241434623563176260651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24782160956415708784173767 37173241434623563176260651)
  ·
    refine ⟨55759862151935344764390977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37173241434623563176260651 55759862151935344764390977)
    ·
      refine ⟨41819896613951508573293233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55759862151935344764390977 41819896613951508573293233)
      ·
        refine ⟨31364922460463631429969925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41819896613951508573293233 31364922460463631429969925)
        ·
          refine ⟨5880922961336930893119361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31364922460463631429969925 5880922961336930893119361)
          ·
            refine ⟨4410692221002698169839521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5880922961336930893119361 4410692221002698169839521)
            ·
              refine ⟨3308019165752023627379641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410692221002698169839521 3308019165752023627379641)
              ·
                refine ⟨2481014374314017720534731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308019165752023627379641 2481014374314017720534731)
                ·
                  refine ⟨3721521561471026580802097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481014374314017720534731 3721521561471026580802097)
                  ·
                    refine ⟨2791141171103269935601573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3721521561471026580802097 2791141171103269935601573)
                    ·
                      refine ⟨523338969581863112925295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2791141171103269935601573 523338969581863112925295)
                      ·
                        rfl

theorem cell23_1019199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1019199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019199 prefixEnd_1019199 := by exact prefixLift 1019199
  have htrace : WordTrace (prefixWord ++ tailWord_1019199) baseStart_1019199 baseEnd_1019199 := by
    simpa [prefixWord, tailWord_1019199, baseEnd_1019199] using wordTrace_append hprefix tailTrace_1019199
  have hstable : (prefixWord ++ tailWord_1019199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019199).length < 2 ^ (prefixWord ++ tailWord_1019199).sum := by decide
  have hdescent : baseEnd_1019199 < baseStart_1019199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019220 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_1019220 : Nat := 118140960795 + 1019220 * 2 ^ 59
def prefixEnd_1019220 : Nat := 4983230072969 + 3 ^ 40 * 1019220 * 2
def baseEnd_1019220 : Nat := 523349752675607530762699

theorem tailTrace_1019220 : CollatzResearch.WordTrace tailWord_1019220 prefixEnd_1019220 523349752675607530762699 := by
  unfold tailWord_1019220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587003683773741881387557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24782671578364989175183409 18587003683773741881387557)
  ·
    refine ⟨3485063190707576602760167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18587003683773741881387557 3485063190707576602760167)
    ·
      refine ⟨5227594786061364904140251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485063190707576602760167 5227594786061364904140251)
      ·
        refine ⟨7841392179092047356210377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227594786061364904140251 7841392179092047356210377)
        ·
          refine ⟨5881044134319035517157783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7841392179092047356210377 5881044134319035517157783)
          ·
            refine ⟨8821566201478553275736675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881044134319035517157783 8821566201478553275736675)
            ·
              refine ⟨13232349302217829913605013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821566201478553275736675 13232349302217829913605013)
              ·
                refine ⟨620266373541460777200235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13232349302217829913605013 620266373541460777200235)
                ·
                  refine ⟨930399560312191165800353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620266373541460777200235 930399560312191165800353)
                  ·
                    refine ⟨697799670234143374350265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 930399560312191165800353 697799670234143374350265)
                    ·
                      refine ⟨523349752675607530762699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697799670234143374350265 523349752675607530762699)
                      ·
                        rfl

theorem cell23_1019220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_1019220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019220 prefixEnd_1019220 := by exact prefixLift 1019220
  have htrace : WordTrace (prefixWord ++ tailWord_1019220) baseStart_1019220 baseEnd_1019220 := by
    simpa [prefixWord, tailWord_1019220, baseEnd_1019220] using wordTrace_append hprefix tailTrace_1019220
  have hstable : (prefixWord ++ tailWord_1019220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019220).length < 2 ^ (prefixWord ++ tailWord_1019220).sum := by decide
  have hdescent : baseEnd_1019220 < baseStart_1019220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019236 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1019236 : Nat := 118140960795 + 1019236 * 2 ^ 59
def prefixEnd_1019236 : Nat := 4983230072969 + 3 ^ 40 * 1019236 * 2
def baseEnd_1019236 : Nat := 523357968366079468162625

theorem tailTrace_1019236 : CollatzResearch.WordTrace tailWord_1019236 prefixEnd_1019236 523357968366079468162625 := by
  unfold tailWord_1019236
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587295467744759247678781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24783060623659678996905041 18587295467744759247678781)
  ·
    refine ⟨6970235800404284717879543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18587295467744759247678781 6970235800404284717879543)
    ·
      refine ⟨10455353700606427076819315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970235800404284717879543 10455353700606427076819315)
      ·
        refine ⟨15683030550909640615228973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455353700606427076819315 15683030550909640615228973)
        ·
          refine ⟨5881136456591115230710865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15683030550909640615228973 5881136456591115230710865)
          ·
            refine ⟨4410852342443336423033149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5881136456591115230710865 4410852342443336423033149)
            ·
              refine ⟨1654069628416251158637431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4410852342443336423033149 1654069628416251158637431)
              ·
                refine ⟨2481104442624376737956147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654069628416251158637431 2481104442624376737956147)
                ·
                  refine ⟨3721656663936565106934221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481104442624376737956147 3721656663936565106934221)
                  ·
                    refine ⟨1395621248976211915100333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721656663936565106934221 1395621248976211915100333)
                    ·
                      refine ⟨523357968366079468162625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395621248976211915100333 523357968366079468162625)
                      ·
                        rfl

theorem cell23_1019236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1019236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019236 prefixEnd_1019236 := by exact prefixLift 1019236
  have htrace : WordTrace (prefixWord ++ tailWord_1019236) baseStart_1019236 baseEnd_1019236 := by
    simpa [prefixWord, tailWord_1019236, baseEnd_1019236] using wordTrace_append hprefix tailTrace_1019236
  have hstable : (prefixWord ++ tailWord_1019236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019236).length < 2 ^ (prefixWord ++ tailWord_1019236).sum := by decide
  have hdescent : baseEnd_1019236 < baseStart_1019236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019326 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1019326 : Nat := 118140960795 + 1019326 * 2 ^ 59
def prefixEnd_1019326 : Nat := 4983230072969 + 3 ^ 40 * 1019326 * 2
def baseEnd_1019326 : Nat := 523404181624984116037211

theorem tailTrace_1019326 : CollatzResearch.WordTrace tailWord_1019326 prefixEnd_1019326 523404181624984116037211 := by
  unfold tailWord_1019326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647234188145432983266729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24785249003442309244089221 4647234188145432983266729)
  ·
    refine ⟨3485425641109074737450047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4647234188145432983266729 3485425641109074737450047)
    ·
      refine ⟨5228138461663612106175071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485425641109074737450047 5228138461663612106175071)
      ·
        refine ⟨7842207692495418159262607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228138461663612106175071 7842207692495418159262607)
        ·
          refine ⟨11763311538743127238893911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842207692495418159262607 11763311538743127238893911)
          ·
            refine ⟨17644967308114690858340867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763311538743127238893911 17644967308114690858340867)
            ·
              refine ⟨26467450962172036287511301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644967308114690858340867 26467450962172036287511301)
              ·
                refine ⟨4962647055407256803908369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26467450962172036287511301 4962647055407256803908369)
                ·
                  refine ⟨3721985291555442602931277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962647055407256803908369 3721985291555442602931277)
                  ·
                    refine ⟨1395744484333290976099229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721985291555442602931277 1395744484333290976099229)
                    ·
                      refine ⟨523404181624984116037211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395744484333290976099229 523404181624984116037211)
                      ·
                        rfl

theorem cell23_1019326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1019326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019326 prefixEnd_1019326 := by exact prefixLift 1019326
  have htrace : WordTrace (prefixWord ++ tailWord_1019326) baseStart_1019326 baseEnd_1019326 := by
    simpa [prefixWord, tailWord_1019326, baseEnd_1019326] using wordTrace_append hprefix tailTrace_1019326
  have hstable : (prefixWord ++ tailWord_1019326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019326).length < 2 ^ (prefixWord ++ tailWord_1019326).sum := by decide
  have hdescent : baseEnd_1019326 < baseStart_1019326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019336 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_1019336 : Nat := 118140960795 + 1019336 * 2 ^ 59
def prefixEnd_1019336 : Nat := 4983230072969 + 3 ^ 40 * 1019336 * 2
def baseEnd_1019336 : Nat := 523409316431529076912165

theorem tailTrace_1019336 : CollatzResearch.WordTrace tailWord_1019336 prefixEnd_1019336 523409316431529076912165 := by
  unfold tailWord_1019336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18589119117563617786998931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24785492156751490382665241 18589119117563617786998931)
  ·
    refine ⟨27883678676345426680498397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18589119117563617786998931 27883678676345426680498397)
    ·
      refine ⟨10456379503629535005186899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27883678676345426680498397 10456379503629535005186899)
      ·
        refine ⟨15684569255444302507780349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456379503629535005186899 15684569255444302507780349)
        ·
          refine ⟨5881713470791613440417631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15684569255444302507780349 5881713470791613440417631)
          ·
            refine ⟨8822570206187420160626447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881713470791613440417631 8822570206187420160626447)
            ·
              refine ⟨13233855309281130240939671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822570206187420160626447 13233855309281130240939671)
              ·
                refine ⟨19850782963921695361409507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13233855309281130240939671 19850782963921695361409507)
                ·
                  refine ⟨29776174445882543042114261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19850782963921695361409507 29776174445882543042114261)
                  ·
                    refine ⟨697879088575372102549553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29776174445882543042114261 697879088575372102549553)
                    ·
                      refine ⟨523409316431529076912165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697879088575372102549553 523409316431529076912165)
                      ·
                        rfl

theorem cell23_1019336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_1019336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019336 prefixEnd_1019336 := by exact prefixLift 1019336
  have htrace : WordTrace (prefixWord ++ tailWord_1019336) baseStart_1019336 baseEnd_1019336 := by
    simpa [prefixWord, tailWord_1019336, baseEnd_1019336] using wordTrace_append hprefix tailTrace_1019336
  have hstable : (prefixWord ++ tailWord_1019336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019336).length < 2 ^ (prefixWord ++ tailWord_1019336).sum := by decide
  have hdescent : baseEnd_1019336 < baseStart_1019336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019339 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_1019339 : Nat := 118140960795 + 1019339 * 2 ^ 59
def prefixEnd_1019339 : Nat := 4983230072969 + 3 ^ 40 * 1019339 * 2
def baseEnd_1019339 : Nat := 523410856873492565174651

theorem tailTrace_1019339 : CollatzResearch.WordTrace tailWord_1019339 prefixEnd_1019339 523410856873492565174651 := by
  unfold tailWord_1019339
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178347654116367086357071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24785565102744244724238047 37178347654116367086357071)
  ·
    refine ⟨55767521481174550629535607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37178347654116367086357071 55767521481174550629535607)
    ·
      refine ⟨83651282221761825944303411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55767521481174550629535607 83651282221761825944303411)
      ·
        refine ⟨125476923332642738916455117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83651282221761825944303411 125476923332642738916455117)
        ·
          refine ⟨47053846249741027093670669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125476923332642738916455117 47053846249741027093670669)
          ·
            refine ⟨17645192343652885160126501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47053846249741027093670669 17645192343652885160126501)
            ·
              refine ⟨3308473564434915967523719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17645192343652885160126501 3308473564434915967523719)
              ·
                refine ⟨4962710346652373951285579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308473564434915967523719 4962710346652373951285579)
                ·
                  refine ⟨7444065519978560926928369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962710346652373951285579 7444065519978560926928369)
                  ·
                    refine ⟨5583049139983920695196277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444065519978560926928369 5583049139983920695196277)
                    ·
                      refine ⟨523410856873492565174651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5583049139983920695196277 523410856873492565174651)
                      ·
                        rfl

theorem cell23_1019339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_1019339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019339 prefixEnd_1019339 := by exact prefixLift 1019339
  have htrace : WordTrace (prefixWord ++ tailWord_1019339) baseStart_1019339 baseEnd_1019339 := by
    simpa [prefixWord, tailWord_1019339, baseEnd_1019339] using wordTrace_append hprefix tailTrace_1019339
  have hstable : (prefixWord ++ tailWord_1019339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019339).length < 2 ^ (prefixWord ++ tailWord_1019339).sum := by decide
  have hdescent : baseEnd_1019339 < baseStart_1019339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019363 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 2, 5]
def baseStart_1019363 : Nat := 118140960795 + 1019363 * 2 ^ 59
def prefixEnd_1019363 : Nat := 4983230072969 + 3 ^ 40 * 1019363 * 2
def baseEnd_1019363 : Nat := 174474393469733490424847

theorem tailTrace_1019363 : CollatzResearch.WordTrace tailWord_1019363 prefixEnd_1019363 174474393469733490424847 := by
  unfold tailWord_1019363
  simp only [CollatzResearch.WordTrace]
  refine ⟨37179223006029419185230743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24786148670686279456820495 37179223006029419185230743)
  ·
    refine ⟨55768834509044128777846115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37179223006029419185230743 55768834509044128777846115)
    ·
      refine ⟨83653251763566193166769173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55768834509044128777846115 83653251763566193166769173)
      ·
        refine ⟨3921246176417165304692305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83653251763566193166769173 3921246176417165304692305)
        ·
          refine ⟨2940934632312873978519229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921246176417165304692305 2940934632312873978519229)
          ·
            refine ⟨1102850487117327741944711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2940934632312873978519229 1102850487117327741944711)
            ·
              refine ⟨1654275730675991612917067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102850487117327741944711 1654275730675991612917067)
              ·
                refine ⟨2481413596013987419375601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654275730675991612917067 2481413596013987419375601)
                ·
                  refine ⟨1861060197010490564531701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2481413596013987419375601 1861060197010490564531701)
                  ·
                    refine ⟨174474393469733490424847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1861060197010490564531701 174474393469733490424847)
                    ·
                      rfl

theorem cell23_1019363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 5].length) (baseStart_1019363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019363 prefixEnd_1019363 := by exact prefixLift 1019363
  have htrace : WordTrace (prefixWord ++ tailWord_1019363) baseStart_1019363 baseEnd_1019363 := by
    simpa [prefixWord, tailWord_1019363, baseEnd_1019363] using wordTrace_append hprefix tailTrace_1019363
  have hstable : (prefixWord ++ tailWord_1019363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019363).length < 2 ^ (prefixWord ++ tailWord_1019363).sum := by decide
  have hdescent : baseEnd_1019363 < baseStart_1019363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019386 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_1019386 : Nat := 118140960795 + 1019386 * 2 ^ 59
def prefixEnd_1019386 : Nat := 4983230072969 + 3 ^ 40 * 1019386 * 2
def baseEnd_1019386 : Nat := 523434990464253881286935

theorem tailTrace_1019386 : CollatzResearch.WordTrace tailWord_1019386 prefixEnd_1019386 523434990464253881286935 := by
  unfold tailWord_1019386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295015471236523528329503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24786707923297396075545341 9295015471236523528329503)
  ·
    refine ⟨13942523206854785292494255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9295015471236523528329503 13942523206854785292494255)
    ·
      refine ⟨20913784810282177938741383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13942523206854785292494255 20913784810282177938741383)
      ·
        refine ⟨31370677215423266908112075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20913784810282177938741383 31370677215423266908112075)
        ·
          refine ⟨47056015823134900362168113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31370677215423266908112075 47056015823134900362168113)
          ·
            refine ⟨35292011867351175271626085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47056015823134900362168113 35292011867351175271626085)
            ·
              refine ⟨6617252225128345363429891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35292011867351175271626085 6617252225128345363429891)
              ·
                refine ⟨9925878337692518045144837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617252225128345363429891 9925878337692518045144837)
                ·
                  refine ⟨1861102188317347133464657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9925878337692518045144837 1861102188317347133464657)
                  ·
                    refine ⟨1395826641238010350098493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861102188317347133464657 1395826641238010350098493)
                    ·
                      refine ⟨523434990464253881286935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395826641238010350098493 523434990464253881286935)
                      ·
                        rfl

theorem cell23_1019386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_1019386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019386 prefixEnd_1019386 := by exact prefixLift 1019386
  have htrace : WordTrace (prefixWord ++ tailWord_1019386) baseStart_1019386 baseEnd_1019386 := by
    simpa [prefixWord, tailWord_1019386, baseEnd_1019386] using wordTrace_append hprefix tailTrace_1019386
  have hstable : (prefixWord ++ tailWord_1019386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019386).length < 2 ^ (prefixWord ++ tailWord_1019386).sum := by decide
  have hdescent : baseEnd_1019386 < baseStart_1019386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019409 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_1019409 : Nat := 118140960795 + 1019409 * 2 ^ 59
def prefixEnd_1019409 : Nat := 4983230072969 + 3 ^ 40 * 1019409 * 2
def baseEnd_1019409 : Nat := 523446800519307291299329

theorem tailTrace_1019409 : CollatzResearch.WordTrace tailWord_1019409 prefixEnd_1019409 523446800519307291299329 := by
  unfold tailWord_1019409
  simp only [CollatzResearch.WordTrace]
  refine ⟨37180900763862769041405281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24787267175908512694270187 37180900763862769041405281)
  ·
    refine ⟨27885675572897076781053961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37180900763862769041405281 27885675572897076781053961)
    ·
      refine ⟨20914256679672807585790471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27885675572897076781053961 20914256679672807585790471)
      ·
        refine ⟨31371385019509211378685707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20914256679672807585790471 31371385019509211378685707)
        ·
          refine ⟨47057077529263817068028561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31371385019509211378685707 47057077529263817068028561)
          ·
            refine ⟨35292808146947862801021421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47057077529263817068028561 35292808146947862801021421)
            ·
              refine ⟨13234803055105448550383033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35292808146947862801021421 13234803055105448550383033)
              ·
                refine ⟨9926102291329086412787275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13234803055105448550383033 9926102291329086412787275)
                ·
                  refine ⟨14889153436993629619180913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926102291329086412787275 14889153436993629619180913)
                  ·
                    refine ⟨11166865077745222214385685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14889153436993629619180913 11166865077745222214385685)
                    ·
                      refine ⟨523446800519307291299329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11166865077745222214385685 523446800519307291299329)
                      ·
                        rfl

theorem cell23_1019409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_1019409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019409 prefixEnd_1019409 := by exact prefixLift 1019409
  have htrace : WordTrace (prefixWord ++ tailWord_1019409) baseStart_1019409 baseEnd_1019409 := by
    simpa [prefixWord, tailWord_1019409, baseEnd_1019409] using wordTrace_append hprefix tailTrace_1019409
  have hstable : (prefixWord ++ tailWord_1019409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019409).length < 2 ^ (prefixWord ++ tailWord_1019409).sum := by decide
  have hdescent : baseEnd_1019409 < baseStart_1019409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019427 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 1, 4]
def baseStart_1019427 : Nat := 118140960795 + 1019427 * 2 ^ 59
def prefixEnd_1019427 : Nat := 4983230072969 + 3 ^ 40 * 1019427 * 2
def baseEnd_1019427 : Nat := 174485347723696073624749

theorem tailTrace_1019427 : CollatzResearch.WordTrace tailWord_1019427 prefixEnd_1019427 174485347723696073624749 := by
  unfold tailWord_1019427
  simp only [CollatzResearch.WordTrace]
  refine ⟨37181557277797558115560535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24787704851865038743707023 37181557277797558115560535)
  ·
    refine ⟨55772335916696337173340803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37181557277797558115560535 55772335916696337173340803)
    ·
      refine ⟨83658503875044505760011205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55772335916696337173340803 83658503875044505760011205)
      ·
        refine ⟨15685969476570844830002101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83658503875044505760011205 15685969476570844830002101)
        ·
          refine ⟨1470559638428516702812697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15685969476570844830002101 1470559638428516702812697)
          ·
            refine ⟨1102919728821387527109523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470559638428516702812697 1102919728821387527109523)
            ·
              refine ⟨1654379593232081290664285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102919728821387527109523 1654379593232081290664285)
              ·
                refine ⟨620392347462030483999107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654379593232081290664285 620392347462030483999107)
                ·
                  refine ⟨930588521193045725998661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620392347462030483999107 930588521193045725998661)
                  ·
                    refine ⟨174485347723696073624749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930588521193045725998661 174485347723696073624749)
                    ·
                      rfl

theorem cell23_1019427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 4].length) (baseStart_1019427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019427 prefixEnd_1019427 := by exact prefixLift 1019427
  have htrace : WordTrace (prefixWord ++ tailWord_1019427) baseStart_1019427 baseEnd_1019427 := by
    simpa [prefixWord, tailWord_1019427, baseEnd_1019427] using wordTrace_append hprefix tailTrace_1019427
  have hstable : (prefixWord ++ tailWord_1019427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019427).length < 2 ^ (prefixWord ++ tailWord_1019427).sum := by decide
  have hdescent : baseEnd_1019427 < baseStart_1019427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019443 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 4, 3, 2]
def baseStart_1019443 : Nat := 118140960795 + 1019443 * 2 ^ 59
def prefixEnd_1019443 : Nat := 4983230072969 + 3 ^ 40 * 1019443 * 2
def baseEnd_1019443 : Nat := 523464258861560158274173

theorem tailTrace_1019443 : CollatzResearch.WordTrace tailWord_1019443 prefixEnd_1019443 523464258861560158274173 := by
  unfold tailWord_1019443
  simp only [CollatzResearch.WordTrace]
  refine ⟨37182140845739592848142983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24788093897159728565428655 37182140845739592848142983)
  ·
    refine ⟨55773211268609389272214475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37182140845739592848142983 55773211268609389272214475)
    ·
      refine ⟨83659816902914083908321713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55773211268609389272214475 83659816902914083908321713)
      ·
        refine ⟨62744862677185562931241285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83659816902914083908321713 62744862677185562931241285)
        ·
          refine ⟨11764661751972293049607741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62744862677185562931241285 11764661751972293049607741)
          ·
            refine ⟨4411748156989609893602903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11764661751972293049607741 4411748156989609893602903)
            ·
              refine ⟨6617622235484414840404355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411748156989609893602903 6617622235484414840404355)
              ·
                refine ⟨9926433353226622260606533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617622235484414840404355 9926433353226622260606533)
                ·
                  refine ⟨1861206253729991673863725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9926433353226622260606533 1861206253729991673863725)
                  ·
                    refine ⟨697952345148746877698897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861206253729991673863725 697952345148746877698897)
                    ·
                      refine ⟨523464258861560158274173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 697952345148746877698897 523464258861560158274173)
                      ·
                        rfl

theorem cell23_1019443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3, 2].length) (baseStart_1019443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019443 prefixEnd_1019443 := by exact prefixLift 1019443
  have htrace : WordTrace (prefixWord ++ tailWord_1019443) baseStart_1019443 baseEnd_1019443 := by
    simpa [prefixWord, tailWord_1019443, baseEnd_1019443] using wordTrace_append hprefix tailTrace_1019443
  have hstable : (prefixWord ++ tailWord_1019443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019443).length < 2 ^ (prefixWord ++ tailWord_1019443).sum := by decide
  have hdescent : baseEnd_1019443 < baseStart_1019443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019456 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_1019456 : Nat := 118140960795 + 1019456 * 2 ^ 59
def prefixEnd_1019456 : Nat := 4983230072969 + 3 ^ 40 * 1019456 * 2
def baseEnd_1019456 : Nat := 523470934110068607411613

theorem tailTrace_1019456 : CollatzResearch.WordTrace tailWord_1019456 prefixEnd_1019456 523470934110068607411613 := by
  unfold tailWord_1019456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18591307497346248034183111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24788409996461664045577481 18591307497346248034183111)
  ·
    refine ⟨27886961246019372051274667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18591307497346248034183111 27886961246019372051274667)
    ·
      refine ⟨41830441869029058076912001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27886961246019372051274667 41830441869029058076912001)
      ·
        refine ⟨31372831401771793557684001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41830441869029058076912001 31372831401771793557684001)
        ·
          refine ⟨23529623551328845168263001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31372831401771793557684001 23529623551328845168263001)
          ·
            refine ⟨17647217663496633876197251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23529623551328845168263001 17647217663496633876197251)
            ·
              refine ⟨26470826495244950814295877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647217663496633876197251 26470826495244950814295877)
              ·
                refine ⟨4963279967858428277680477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26470826495244950814295877 4963279967858428277680477)
                ·
                  refine ⟨1861229987946910604130179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4963279967858428277680477 1861229987946910604130179)
                  ·
                    refine ⟨2791844981920365906195269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1861229987946910604130179 2791844981920365906195269)
                    ·
                      refine ⟨523470934110068607411613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2791844981920365906195269 523470934110068607411613)
                      ·
                        rfl

theorem cell23_1019456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_1019456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019456 prefixEnd_1019456 := by exact prefixLift 1019456
  have htrace : WordTrace (prefixWord ++ tailWord_1019456) baseStart_1019456 baseEnd_1019456 := by
    simpa [prefixWord, tailWord_1019456, baseEnd_1019456] using wordTrace_append hprefix tailTrace_1019456
  have hstable : (prefixWord ++ tailWord_1019456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019456).length < 2 ^ (prefixWord ++ tailWord_1019456).sum := by decide
  have hdescent : baseEnd_1019456 < baseStart_1019456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019466 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1019466 : Nat := 118140960795 + 1019466 * 2 ^ 59
def prefixEnd_1019466 : Nat := 4983230072969 + 3 ^ 40 * 1019466 * 2
def baseEnd_1019466 : Nat := 174492022972204522762189

theorem tailTrace_1019466 : CollatzResearch.WordTrace tailWord_1019466 prefixEnd_1019466 174492022972204522762189 := by
  unfold tailWord_1019466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295744931164066944057563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24788653149770845184153501 9295744931164066944057563)
  ·
    refine ⟨13943617396746100416086345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9295744931164066944057563 13943617396746100416086345)
    ·
      refine ⟨10457713047559575312064759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13943617396746100416086345 10457713047559575312064759)
      ·
        refine ⟨15686569571339362968097139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10457713047559575312064759 15686569571339362968097139)
        ·
          refine ⟨23529854357009044452145709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15686569571339362968097139 23529854357009044452145709)
          ·
            refine ⟨8823695383878391669554641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23529854357009044452145709 8823695383878391669554641)
            ·
              refine ⟨6617771537908793752165981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8823695383878391669554641 6617771537908793752165981)
              ·
                refine ⟨2481664326715797657062243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6617771537908793752165981 2481664326715797657062243)
                ·
                  refine ⟨3722496490073696485593365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481664326715797657062243 3722496490073696485593365)
                  ·
                    refine ⟨174492022972204522762189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3722496490073696485593365 174492022972204522762189)
                    ·
                      rfl

theorem cell23_1019466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1019466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019466 prefixEnd_1019466 := by exact prefixLift 1019466
  have htrace : WordTrace (prefixWord ++ tailWord_1019466) baseStart_1019466 baseEnd_1019466 := by
    simpa [prefixWord, tailWord_1019466, baseEnd_1019466] using wordTrace_append hprefix tailTrace_1019466
  have hstable : (prefixWord ++ tailWord_1019466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019466).length < 2 ^ (prefixWord ++ tailWord_1019466).sum := by decide
  have hdescent : baseEnd_1019466 < baseStart_1019466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019493 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1019493 : Nat := 118140960795 + 1019493 * 2 ^ 59
def prefixEnd_1019493 : Nat := 4983230072969 + 3 ^ 40 * 1019493 * 2
def baseEnd_1019493 : Nat := 523489932894284962648943

theorem tailTrace_1019493 : CollatzResearch.WordTrace tailWord_1019493 prefixEnd_1019493 523489932894284962648943 := by
  unfold tailWord_1019493
  simp only [CollatzResearch.WordTrace]
  refine ⟨37183964495558451387463133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24789309663705634258308755 37183964495558451387463133)
  ·
    refine ⟨13943986685834419270298675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37183964495558451387463133 13943986685834419270298675)
    ·
      refine ⟨20915980028751628905448013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13943986685834419270298675 20915980028751628905448013)
      ·
        refine ⟨7843492510781860839543005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20915980028751628905448013 7843492510781860839543005)
        ·
          refine ⟨2941309691543197814828627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7843492510781860839543005 2941309691543197814828627)
          ·
            refine ⟨4411964537314796722242941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941309691543197814828627 4411964537314796722242941)
            ·
              refine ⟨1654486701493048770841103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4411964537314796722242941 1654486701493048770841103)
              ·
                refine ⟨2481730052239573156261655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654486701493048770841103 2481730052239573156261655)
                ·
                  refine ⟨3722595078359359734392483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481730052239573156261655 3722595078359359734392483)
                  ·
                    refine ⟨5583892617539039601588725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3722595078359359734392483 5583892617539039601588725)
                    ·
                      refine ⟨523489932894284962648943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5583892617539039601588725 523489932894284962648943)
                      ·
                        rfl

theorem cell23_1019493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1019493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019493 prefixEnd_1019493 := by exact prefixLift 1019493
  have htrace : WordTrace (prefixWord ++ tailWord_1019493) baseStart_1019493 baseEnd_1019493 := by
    simpa [prefixWord, tailWord_1019493, baseEnd_1019493] using wordTrace_append hprefix tailTrace_1019493
  have hstable : (prefixWord ++ tailWord_1019493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019493).length < 2 ^ (prefixWord ++ tailWord_1019493).sum := by decide
  have hdescent : baseEnd_1019493 < baseStart_1019493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019496 : List Nat := [2, 1, 4, 3, 1, 12]
def baseStart_1019496 : Nat := 118140960795 + 1019496 * 2 ^ 59
def prefixEnd_1019496 : Nat := 4983230072969 + 3 ^ 40 * 1019496 * 2
def baseEnd_1019496 : Nat := 2154285898503080044903

theorem tailTrace_1019496 : CollatzResearch.WordTrace tailWord_1019496 prefixEnd_1019496 2154285898503080044903 := by
  unfold tailWord_1019496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592036957273791449911171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24789382609698388599881561 18592036957273791449911171)
  ·
    refine ⟨27888055435910687174866757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592036957273791449911171 27888055435910687174866757)
    ·
      refine ⟨5229010394233253845287517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27888055435910687174866757 5229010394233253845287517)
      ·
        refine ⟨1960878897837470191982819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5229010394233253845287517 1960878897837470191982819)
        ·
          refine ⟨2941318346756205287974229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960878897837470191982819 2941318346756205287974229)
          ·
            refine ⟨2154285898503080044903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2941318346756205287974229 2154285898503080044903)
            ·
              rfl

theorem cell23_1019496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 12].length) (baseStart_1019496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019496 prefixEnd_1019496 := by exact prefixLift 1019496
  have htrace : WordTrace (prefixWord ++ tailWord_1019496) baseStart_1019496 baseEnd_1019496 := by
    simpa [prefixWord, tailWord_1019496, baseEnd_1019496] using wordTrace_append hprefix tailTrace_1019496
  have hstable : (prefixWord ++ tailWord_1019496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019496).length < 2 ^ (prefixWord ++ tailWord_1019496).sum := by decide
  have hdescent : baseEnd_1019496 < baseStart_1019496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019501 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1019501 : Nat := 118140960795 + 1019501 * 2 ^ 59
def prefixEnd_1019501 : Nat := 4983230072969 + 3 ^ 40 * 1019501 * 2
def baseEnd_1019501 : Nat := 523494040739520931348907

theorem tailTrace_1019501 : CollatzResearch.WordTrace tailWord_1019501 prefixEnd_1019501 523494040739520931348907 := by
  unfold tailWord_1019501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37184256279529468753754357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24789504186352979169169571 37184256279529468753754357)
  ·
    refine ⟨3486024026205887695664471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37184256279529468753754357 3486024026205887695664471)
    ·
      refine ⟨5229036039308831543496707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486024026205887695664471 5229036039308831543496707)
      ·
        refine ⟨7843554058963247315245061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229036039308831543496707 7843554058963247315245061)
        ·
          refine ⟨1470666386055608871608449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7843554058963247315245061 1470666386055608871608449)
          ·
            refine ⟨1102999789541706653706337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470666386055608871608449 1102999789541706653706337)
            ·
              refine ⟨827249842156279990279753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102999789541706653706337 827249842156279990279753)
              ·
                refine ⟨620437381617209992709815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827249842156279990279753 620437381617209992709815)
                ·
                  refine ⟨930656072425814989064723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620437381617209992709815 930656072425814989064723)
                  ·
                    refine ⟨1395984108638722483597085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930656072425814989064723 1395984108638722483597085)
                    ·
                      refine ⟨523494040739520931348907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395984108638722483597085 523494040739520931348907)
                      ·
                        rfl

theorem cell23_1019501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1019501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019501 prefixEnd_1019501 := by exact prefixLift 1019501
  have htrace : WordTrace (prefixWord ++ tailWord_1019501) baseStart_1019501 baseEnd_1019501 := by
    simpa [prefixWord, tailWord_1019501, baseEnd_1019501] using wordTrace_append hprefix tailTrace_1019501
  have hstable : (prefixWord ++ tailWord_1019501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019501).length < 2 ^ (prefixWord ++ tailWord_1019501).sum := by decide
  have hdescent : baseEnd_1019501 < baseStart_1019501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019510 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1019510 : Nat := 118140960795 + 1019510 * 2 ^ 59
def prefixEnd_1019510 : Nat := 4983230072969 + 3 ^ 40 * 1019510 * 2
def baseEnd_1019510 : Nat := 523498662065411396136365

theorem tailTrace_1019510 : CollatzResearch.WordTrace tailWord_1019510 prefixEnd_1019510 523498662065411396136365 := by
  unfold tailWord_1019510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324036533531053955676999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24789723024331242193887989 2324036533531053955676999)
  ·
    refine ⟨3486054800296580933515499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324036533531053955676999 3486054800296580933515499)
    ·
      refine ⟨5229082200444871400273249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486054800296580933515499 5229082200444871400273249)
      ·
        refine ⟨3921811650333653550204937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5229082200444871400273249 3921811650333653550204937)
        ·
          refine ⟨2941358737750240162653703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921811650333653550204937 2941358737750240162653703)
          ·
            refine ⟨4412038106625360243980555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941358737750240162653703 4412038106625360243980555)
            ·
              refine ⟨6618057159938040365970833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412038106625360243980555 6618057159938040365970833)
              ·
                refine ⟨4963542869953530274478125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6618057159938040365970833 4963542869953530274478125)
                ·
                  refine ⟨1861328576232573852929297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4963542869953530274478125 1861328576232573852929297)
                  ·
                    refine ⟨1395996432174430389696973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861328576232573852929297 1395996432174430389696973)
                    ·
                      refine ⟨523498662065411396136365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1395996432174430389696973 523498662065411396136365)
                      ·
                        rfl

theorem cell23_1019510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1019510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019510 prefixEnd_1019510 := by exact prefixLift 1019510
  have htrace : WordTrace (prefixWord ++ tailWord_1019510) baseStart_1019510 baseEnd_1019510 := by
    simpa [prefixWord, tailWord_1019510, baseEnd_1019510] using wordTrace_append hprefix tailTrace_1019510
  have hstable : (prefixWord ++ tailWord_1019510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019510).length < 2 ^ (prefixWord ++ tailWord_1019510).sum := by decide
  have hdescent : baseEnd_1019510 < baseStart_1019510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019523 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 3]
def baseStart_1019523 : Nat := 118140960795 + 1019523 * 2 ^ 59
def prefixEnd_1019523 : Nat := 4983230072969 + 3 ^ 40 * 1019523 * 2
def baseEnd_1019523 : Nat := 523505337313919845273805

theorem tailTrace_1019523 : CollatzResearch.WordTrace tailWord_1019523 prefixEnd_1019523 523505337313919845273805 := by
  unfold tailWord_1019523
  simp only [CollatzResearch.WordTrace]
  refine ⟨37185058685449766511055223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790039123633177674036815 37185058685449766511055223)
  ·
    refine ⟨55777588028174649766582835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37185058685449766511055223 55777588028174649766582835)
    ·
      refine ⟨83666382042261974649874253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55777588028174649766582835 83666382042261974649874253)
      ·
        refine ⟨31374893265848240493702845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83666382042261974649874253 31374893265848240493702845)
        ·
          refine ⟨11765584974693090185138567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31374893265848240493702845 11765584974693090185138567)
          ·
            refine ⟨17648377462039635277707851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765584974693090185138567 17648377462039635277707851)
            ·
              refine ⟨26472566193059452916561777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17648377462039635277707851 26472566193059452916561777)
              ·
                refine ⟨19854424644794589687421333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26472566193059452916561777 19854424644794589687421333)
                ·
                  refine ⟨930676155224746391597875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19854424644794589687421333 930676155224746391597875)
                  ·
                    refine ⟨1396014232837119587396813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930676155224746391597875 1396014232837119587396813)
                    ·
                      refine ⟨523505337313919845273805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396014232837119587396813 523505337313919845273805)
                      ·
                        rfl

theorem cell23_1019523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_1019523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019523 prefixEnd_1019523 := by exact prefixLift 1019523
  have htrace : WordTrace (prefixWord ++ tailWord_1019523) baseStart_1019523 baseEnd_1019523 := by
    simpa [prefixWord, tailWord_1019523, baseEnd_1019523] using wordTrace_append hprefix tailTrace_1019523
  have hstable : (prefixWord ++ tailWord_1019523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019523).length < 2 ^ (prefixWord ++ tailWord_1019523).sum := by decide
  have hdescent : baseEnd_1019523 < baseStart_1019523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019574 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1019574 : Nat := 118140960795 + 1019574 * 2 ^ 59
def prefixEnd_1019574 : Nat := 4983230072969 + 3 ^ 40 * 1019574 * 2
def baseEnd_1019574 : Nat := 523531524827299145736071

theorem tailTrace_1019574 : CollatzResearch.WordTrace tailWord_1019574 prefixEnd_1019574 523531524827299145736071 := by
  unfold tailWord_1019574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324182425516562638822611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24791279205510001480774517 2324182425516562638822611)
  ·
    refine ⟨3486273638274843958233917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324182425516562638822611 3486273638274843958233917)
    ·
      refine ⟨1307352614353066484337719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3486273638274843958233917 1307352614353066484337719)
      ·
        refine ⟨1961028921529599726506579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307352614353066484337719 1961028921529599726506579)
        ·
          refine ⟨2941543382294399589759869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961028921529599726506579 2941543382294399589759869)
          ·
            refine ⟨1103078768360399846159951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2941543382294399589759869 1103078768360399846159951)
            ·
              refine ⟨1654618152540599769239927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103078768360399846159951 1654618152540599769239927)
              ·
                refine ⟨2481927228810899653859891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654618152540599769239927 2481927228810899653859891)
                ·
                  refine ⟨3722890843216349480789837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481927228810899653859891 3722890843216349480789837)
                  ·
                    refine ⟨1396084066206131055296189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722890843216349480789837 1396084066206131055296189)
                    ·
                      refine ⟨523531524827299145736071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396084066206131055296189 523531524827299145736071)
                      ·
                        rfl

theorem cell23_1019574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1019574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019574 prefixEnd_1019574 := by exact prefixLift 1019574
  have htrace : WordTrace (prefixWord ++ tailWord_1019574) baseStart_1019574 baseEnd_1019574 := by
    simpa [prefixWord, tailWord_1019574, baseEnd_1019574] using wordTrace_append hprefix tailTrace_1019574
  have hstable : (prefixWord ++ tailWord_1019574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019574).length < 2 ^ (prefixWord ++ tailWord_1019574).sum := by decide
  have hdescent : baseEnd_1019574 < baseStart_1019574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019663 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 7, 4]
def baseStart_1019663 : Nat := 118140960795 + 1019663 * 2 ^ 59
def prefixEnd_1019663 : Nat := 4983230072969 + 3 ^ 40 * 1019663 * 2
def baseEnd_1019663 : Nat := 174525741535183099174387

theorem tailTrace_1019663 : CollatzResearch.WordTrace tailWord_1019663 prefixEnd_1019663 174525741535183099174387 := by
  unfold tailWord_1019663
  simp only [CollatzResearch.WordTrace]
  refine ⟨37190164904942570421151643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24793443269961713614101095 37190164904942570421151643)
  ·
    refine ⟨55785247357413855631727465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37190164904942570421151643 55785247357413855631727465)
    ·
      refine ⟨41838935518060391723795599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55785247357413855631727465 41838935518060391723795599)
      ·
        refine ⟨62758403277090587585693399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41838935518060391723795599 62758403277090587585693399)
        ·
          refine ⟨94137604915635881378540099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62758403277090587585693399 94137604915635881378540099)
          ·
            refine ⟨141206407373453822067810149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94137604915635881378540099 141206407373453822067810149)
            ·
              refine ⟨26476201382522591637714403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141206407373453822067810149 26476201382522591637714403)
              ·
                refine ⟨39714302073783887456571605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26476201382522591637714403 39714302073783887456571605)
                ·
                  refine ⟨930803954854309862263397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39714302073783887456571605 930803954854309862263397)
                  ·
                    refine ⟨174525741535183099174387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930803954854309862263397 174525741535183099174387)
                    ·
                      rfl

theorem cell23_1019663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_1019663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019663 prefixEnd_1019663 := by exact prefixLift 1019663
  have htrace : WordTrace (prefixWord ++ tailWord_1019663) baseStart_1019663 baseEnd_1019663 := by
    simpa [prefixWord, tailWord_1019663, baseEnd_1019663] using wordTrace_append hprefix tailTrace_1019663
  have hstable : (prefixWord ++ tailWord_1019663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019663).length < 2 ^ (prefixWord ++ tailWord_1019663).sum := by decide
  have hdescent : baseEnd_1019663 < baseStart_1019663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019680 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_1019680 : Nat := 118140960795 + 1019680 * 2 ^ 59
def prefixEnd_1019680 : Nat := 4983230072969 + 3 ^ 40 * 1019680 * 2
def baseEnd_1019680 : Nat := 174528651258891910336861

theorem tailTrace_1019680 : CollatzResearch.WordTrace tailWord_1019680 prefixEnd_1019680 174528651258891910336861 := by
  unfold tailWord_1019680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18595392472940491162260247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24793856630587321549680329 18595392472940491162260247)
  ·
    refine ⟨27893088709410736743390371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18595392472940491162260247 27893088709410736743390371)
    ·
      refine ⟨41839633064116105115085557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27893088709410736743390371 41839633064116105115085557)
      ·
        refine ⟨3922465599760884854539271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41839633064116105115085557 3922465599760884854539271)
        ·
          refine ⟨5883698399641327281808907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922465599760884854539271 5883698399641327281808907)
          ·
            refine ⟨8825547599461990922713361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883698399641327281808907 8825547599461990922713361)
            ·
              refine ⟨6619160699596493192035021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8825547599461990922713361 6619160699596493192035021)
              ·
                refine ⟨2482185262348684947013133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6619160699596493192035021 2482185262348684947013133)
                ·
                  refine ⟨930819473380756855129925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2482185262348684947013133 930819473380756855129925)
                  ·
                    refine ⟨174528651258891910336861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930819473380756855129925 174528651258891910336861)
                    ·
                      rfl

theorem cell23_1019680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_1019680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019680 prefixEnd_1019680 := by exact prefixLift 1019680
  have htrace : WordTrace (prefixWord ++ tailWord_1019680) baseStart_1019680 baseEnd_1019680 := by
    simpa [prefixWord, tailWord_1019680, baseEnd_1019680] using wordTrace_append hprefix tailTrace_1019680
  have hstable : (prefixWord ++ tailWord_1019680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019680).length < 2 ^ (prefixWord ++ tailWord_1019680).sum := by decide
  have hdescent : baseEnd_1019680 < baseStart_1019680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019703 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1019703 : Nat := 118140960795 + 1019703 * 2 ^ 59
def prefixEnd_1019703 : Nat := 4983230072969 + 3 ^ 40 * 1019703 * 2
def baseEnd_1019703 : Nat := 523597763831729141022977

theorem tailTrace_1019703 : CollatzResearch.WordTrace tailWord_1019703 prefixEnd_1019703 523597763831729141022977 := by
  unfold tailWord_1019703
  simp only [CollatzResearch.WordTrace]
  refine ⟨37191623824797657252607763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24794415883198438168405175 37191623824797657252607763)
  ·
    refine ⟨55787435737196485878911645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37191623824797657252607763 55787435737196485878911645)
    ·
      refine ⟨20920288401448682204591867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55787435737196485878911645 20920288401448682204591867)
      ·
        refine ⟨31380432602173023306887801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20920288401448682204591867 31380432602173023306887801)
        ·
          refine ⟨23535324451629767480165851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31380432602173023306887801 23535324451629767480165851)
          ·
            refine ⟨35302986677444651220248777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23535324451629767480165851 35302986677444651220248777)
            ·
              refine ⟨26477240008083488415186583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35302986677444651220248777 26477240008083488415186583)
              ·
                refine ⟨39715860012125232622779875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26477240008083488415186583 39715860012125232622779875)
                ·
                  refine ⟨59573790018187848934169813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39715860012125232622779875 59573790018187848934169813)
                  ·
                    refine ⟨1396260703551277709394605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59573790018187848934169813 1396260703551277709394605)
                    ·
                      refine ⟨523597763831729141022977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396260703551277709394605 523597763831729141022977)
                      ·
                        rfl

theorem cell23_1019703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1019703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019703 prefixEnd_1019703 := by exact prefixLift 1019703
  have htrace : WordTrace (prefixWord ++ tailWord_1019703) baseStart_1019703 baseEnd_1019703 := by
    simpa [prefixWord, tailWord_1019703, baseEnd_1019703] using wordTrace_append hprefix tailTrace_1019703
  have hstable : (prefixWord ++ tailWord_1019703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019703).length < 2 ^ (prefixWord ++ tailWord_1019703).sum := by decide
  have hdescent : baseEnd_1019703 < baseStart_1019703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019737 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 3]
def baseStart_1019737 : Nat := 118140960795 + 1019737 * 2 ^ 59
def prefixEnd_1019737 : Nat := 4983230072969 + 3 ^ 40 * 1019737 * 2
def baseEnd_1019737 : Nat := 523615222173982007997821

theorem tailTrace_1019737 : CollatzResearch.WordTrace tailWord_1019737 prefixEnd_1019737 523615222173982007997821 := by
  unfold tailWord_1019737
  simp only [CollatzResearch.WordTrace]
  refine ⟨37192863906674481059345465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24795242604449654039563643 37192863906674481059345465)
  ·
    refine ⟨27894647930005860794509099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37192863906674481059345465 27894647930005860794509099)
    ·
      refine ⟨41841971895008791191763649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27894647930005860794509099 41841971895008791191763649)
      ·
        refine ⟨31381478921256593393822737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41841971895008791191763649 31381478921256593393822737)
        ·
          refine ⟨23536109190942445045367053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31381478921256593393822737 23536109190942445045367053)
          ·
            refine ⟨8826040946603416892012645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23536109190942445045367053 8826040946603416892012645)
            ·
              refine ⟨1654882677488140667252371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8826040946603416892012645 1654882677488140667252371)
              ·
                refine ⟨2482324016232211000878557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654882677488140667252371 2482324016232211000878557)
                ·
                  refine ⟨930871506087079125329459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2482324016232211000878557 930871506087079125329459)
                  ·
                    refine ⟨1396307259130618687994189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930871506087079125329459 1396307259130618687994189)
                    ·
                      refine ⟨523615222173982007997821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396307259130618687994189 523615222173982007997821)
                      ·
                        rfl

theorem cell23_1019737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_1019737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019737 prefixEnd_1019737 := by exact prefixLift 1019737
  have htrace : WordTrace (prefixWord ++ tailWord_1019737) baseStart_1019737 baseEnd_1019737 := by
    simpa [prefixWord, tailWord_1019737, baseEnd_1019737] using wordTrace_append hprefix tailTrace_1019737
  have hstable : (prefixWord ++ tailWord_1019737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019737).length < 2 ^ (prefixWord ++ tailWord_1019737).sum := by decide
  have hdescent : baseEnd_1019737 < baseStart_1019737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019760 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2]
def baseStart_1019760 : Nat := 118140960795 + 1019760 * 2 ^ 59
def prefixEnd_1019760 : Nat := 4983230072969 + 3 ^ 40 * 1019760 * 2
def baseEnd_1019760 : Nat := 523627032229035418010215

theorem tailTrace_1019760 : CollatzResearch.WordTrace tailWord_1019760 prefixEnd_1019760 523627032229035418010215 := by
  unfold tailWord_1019760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596851392795577993716367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24795801857060770658288489 18596851392795577993716367)
  ·
    refine ⟨27895277089193366990574551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18596851392795577993716367 27895277089193366990574551)
    ·
      refine ⟨41842915633790050485861827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27895277089193366990574551 41842915633790050485861827)
      ·
        refine ⟨62764373450685075728792741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41842915633790050485861827 62764373450685075728792741)
        ·
          refine ⟨11768320022003451699148639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62764373450685075728792741 11768320022003451699148639)
          ·
            refine ⟨17652480033005177548722959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768320022003451699148639 17652480033005177548722959)
            ·
              refine ⟨26478720049507766323084439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17652480033005177548722959 26478720049507766323084439)
              ·
                refine ⟨39718080074261649484626659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26478720049507766323084439 39718080074261649484626659)
                ·
                  refine ⟨59577120111392474226939989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39718080074261649484626659 59577120111392474226939989)
                  ·
                    refine ⟨698169376305380557346953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59577120111392474226939989 698169376305380557346953)
                    ·
                      refine ⟨523627032229035418010215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698169376305380557346953 523627032229035418010215)
                      ·
                        rfl

theorem cell23_1019760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2].length) (baseStart_1019760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019760 prefixEnd_1019760 := by exact prefixLift 1019760
  have htrace : WordTrace (prefixWord ++ tailWord_1019760) baseStart_1019760 baseEnd_1019760 := by
    simpa [prefixWord, tailWord_1019760, baseEnd_1019760] using wordTrace_append hprefix tailTrace_1019760
  have hstable : (prefixWord ++ tailWord_1019760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019760).length < 2 ^ (prefixWord ++ tailWord_1019760).sum := by decide
  have hdescent : baseEnd_1019760 < baseStart_1019760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019763 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_1019763 : Nat := 118140960795 + 1019763 * 2 ^ 59
def prefixEnd_1019763 : Nat := 4983230072969 + 3 ^ 40 * 1019763 * 2
def baseEnd_1019763 : Nat := 523628572670998906272701

theorem tailTrace_1019763 : CollatzResearch.WordTrace tailWord_1019763 prefixEnd_1019763 523628572670998906272701 := by
  unfold tailWord_1019763
  simp only [CollatzResearch.WordTrace]
  refine ⟨37193812204580287499791943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24795874803053524999861295 37193812204580287499791943)
  ·
    refine ⟨55790718306870431249687915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37193812204580287499791943 55790718306870431249687915)
    ·
      refine ⟨83686077460305646874531873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55790718306870431249687915 83686077460305646874531873)
      ·
        refine ⟨62764558095229235155898905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83686077460305646874531873 62764558095229235155898905)
        ·
          refine ⟨47073418571421926366924179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62764558095229235155898905 47073418571421926366924179)
          ·
            refine ⟨70610127857132889550386269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47073418571421926366924179 70610127857132889550386269)
            ·
              refine ⟨26478797946424833581394851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70610127857132889550386269 26478797946424833581394851)
              ·
                refine ⟨39718196919637250372092277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26478797946424833581394851 39718196919637250372092277)
                ·
                  refine ⟨3723580961215992222383651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39718196919637250372092277 3723580961215992222383651)
                  ·
                    refine ⟨5585371441823988333575477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3723580961215992222383651 5585371441823988333575477)
                    ·
                      refine ⟨523628572670998906272701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5585371441823988333575477 523628572670998906272701)
                      ·
                        rfl

theorem cell23_1019763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_1019763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019763 prefixEnd_1019763 := by exact prefixLift 1019763
  have htrace : WordTrace (prefixWord ++ tailWord_1019763) baseStart_1019763 baseEnd_1019763 := by
    simpa [prefixWord, tailWord_1019763, baseEnd_1019763] using wordTrace_append hprefix tailTrace_1019763
  have hstable : (prefixWord ++ tailWord_1019763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019763).length < 2 ^ (prefixWord ++ tailWord_1019763).sum := by decide
  have hdescent : baseEnd_1019763 < baseStart_1019763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019770 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_1019770 : Nat := 118140960795 + 1019770 * 2 ^ 59
def prefixEnd_1019770 : Nat := 4983230072969 + 3 ^ 40 * 1019770 * 2
def baseEnd_1019770 : Nat := 174544055678526792961723

theorem tailTrace_1019770 : CollatzResearch.WordTrace tailWord_1019770 prefixEnd_1019770 174544055678526792961723 := by
  unfold tailWord_1019770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298516878888731923824191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24796045010369951796864509 9298516878888731923824191)
  ·
    refine ⟨13947775318333097885736287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9298516878888731923824191 13947775318333097885736287)
    ·
      refine ⟨20921662977499646828604431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947775318333097885736287 20921662977499646828604431)
      ·
        refine ⟨31382494466249470242906647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20921662977499646828604431 31382494466249470242906647)
        ·
          refine ⟨47073741699374205364359971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31382494466249470242906647 47073741699374205364359971)
          ·
            refine ⟨70610612549061308046539957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47073741699374205364359971 70610612549061308046539957)
            ·
              refine ⟨6619744926474497629363121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70610612549061308046539957 6619744926474497629363121)
              ·
                refine ⟨4964808694855873222022341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619744926474497629363121 4964808694855873222022341)
                ·
                  refine ⟨930901630285476229129189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4964808694855873222022341 930901630285476229129189)
                  ·
                    refine ⟨174544055678526792961723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930901630285476229129189 174544055678526792961723)
                    ·
                      rfl

theorem cell23_1019770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_1019770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019770 prefixEnd_1019770 := by exact prefixLift 1019770
  have htrace : WordTrace (prefixWord ++ tailWord_1019770) baseStart_1019770 baseEnd_1019770 := by
    simpa [prefixWord, tailWord_1019770, baseEnd_1019770] using wordTrace_append hprefix tailTrace_1019770
  have hstable : (prefixWord ++ tailWord_1019770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019770).length < 2 ^ (prefixWord ++ tailWord_1019770).sum := by decide
  have hdescent : baseEnd_1019770 < baseStart_1019770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019774 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1019774 : Nat := 118140960795 + 1019774 * 2 ^ 59
def prefixEnd_1019774 : Nat := 4983230072969 + 3 ^ 40 * 1019774 * 2
def baseEnd_1019774 : Nat := 174544740319399454411717

theorem tailTrace_1019774 : CollatzResearch.WordTrace tailWord_1019774 prefixEnd_1019774 174544740319399454411717 := by
  unfold tailWord_1019774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649276675942554547305297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24796142271693624252294917 4649276675942554547305297)
  ·
    refine ⟨3486957506956915910478973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4649276675942554547305297 3486957506956915910478973)
    ·
      refine ⟨1307609065108843466429615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3486957506956915910478973 1307609065108843466429615)
      ·
        refine ⟨1961413597663265199644423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307609065108843466429615 1961413597663265199644423)
        ·
          refine ⟨2942120396494897799466635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961413597663265199644423 2942120396494897799466635)
          ·
            refine ⟨4413180594742346699199953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942120396494897799466635 4413180594742346699199953)
            ·
              refine ⟨3309885446056760024399965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413180594742346699199953 3309885446056760024399965)
              ·
                refine ⟨1241207042271285009149987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309885446056760024399965 1241207042271285009149987)
                ·
                  refine ⟨1861810563406927513724981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241207042271285009149987 1861810563406927513724981)
                  ·
                    refine ⟨174544740319399454411717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1861810563406927513724981 174544740319399454411717)
                    ·
                      rfl

theorem cell23_1019774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1019774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019774 prefixEnd_1019774 := by exact prefixLift 1019774
  have htrace : WordTrace (prefixWord ++ tailWord_1019774) baseStart_1019774 baseEnd_1019774 := by
    simpa [prefixWord, tailWord_1019774, baseEnd_1019774] using wordTrace_append hprefix tailTrace_1019774
  have hstable : (prefixWord ++ tailWord_1019774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019774).length < 2 ^ (prefixWord ++ tailWord_1019774).sum := by decide
  have hdescent : baseEnd_1019774 < baseStart_1019774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019780 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1019780 : Nat := 118140960795 + 1019780 * 2 ^ 59
def prefixEnd_1019780 : Nat := 4983230072969 + 3 ^ 40 * 1019780 * 2
def baseEnd_1019780 : Nat := 523637301842125339760123

theorem tailTrace_1019780 : CollatzResearch.WordTrace tailWord_1019780 prefixEnd_1019780 523637301842125339760123 := by
  unfold tailWord_1019780
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597216122759349701580397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24796288163679132935440529 18597216122759349701580397)
  ·
    refine ⟨6973956046034756138092649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18597216122759349701580397 6973956046034756138092649)
    ·
      refine ⟨5230467034526067103569487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6973956046034756138092649 5230467034526067103569487)
      ·
        refine ⟨7845700551789100655354231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230467034526067103569487 7845700551789100655354231)
        ·
          refine ⟨11768550827683650983031347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845700551789100655354231 11768550827683650983031347)
          ·
            refine ⟨17652826241525476474547021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768550827683650983031347 17652826241525476474547021)
            ·
              refine ⟨6619809840572053677955133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17652826241525476474547021 6619809840572053677955133)
              ·
                refine ⟨2482428690214520129233175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6619809840572053677955133 2482428690214520129233175)
                ·
                  refine ⟨3723643035321780193849763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482428690214520129233175 3723643035321780193849763)
                  ·
                    refine ⟨5585464552982670290774645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3723643035321780193849763 5585464552982670290774645)
                    ·
                      refine ⟨523637301842125339760123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5585464552982670290774645 523637301842125339760123)
                      ·
                        rfl

theorem cell23_1019780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1019780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019780 prefixEnd_1019780 := by exact prefixLift 1019780
  have htrace : WordTrace (prefixWord ++ tailWord_1019780) baseStart_1019780 baseEnd_1019780 := by
    simpa [prefixWord, tailWord_1019780, baseEnd_1019780] using wordTrace_append hprefix tailTrace_1019780
  have hstable : (prefixWord ++ tailWord_1019780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019780).length < 2 ^ (prefixWord ++ tailWord_1019780).sum := by decide
  have hdescent : baseEnd_1019780 < baseStart_1019780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019804 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1019804 : Nat := 118140960795 + 1019804 * 2 ^ 59
def prefixEnd_1019804 : Nat := 4983230072969 + 3 ^ 40 * 1019804 * 2
def baseEnd_1019804 : Nat := 174549875125944415286671

theorem tailTrace_1019804 : CollatzResearch.WordTrace tailWord_1019804 prefixEnd_1019804 174549875125944415286671 := by
  unfold tailWord_1019804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597653798715875751017233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24796871731621167668022977 18597653798715875751017233)
  ·
    refine ⟨13948240349036906813262925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18597653798715875751017233 13948240349036906813262925)
    ·
      refine ⟨5230590130888840054973597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13948240349036906813262925 5230590130888840054973597)
      ·
        refine ⟨1961471299083315020615099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5230590130888840054973597 1961471299083315020615099)
        ·
          refine ⟨2942206948624972530922649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961471299083315020615099 2942206948624972530922649)
          ·
            refine ⟨2206655211468729398191987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942206948624972530922649 2206655211468729398191987)
            ·
              refine ⟨3309982817203094097287981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206655211468729398191987 3309982817203094097287981)
              ·
                refine ⟨1241243556451160286482993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309982817203094097287981 1241243556451160286482993)
                ·
                  refine ⟨930932667338370214862245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241243556451160286482993 930932667338370214862245)
                  ·
                    refine ⟨174549875125944415286671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930932667338370214862245 174549875125944415286671)
                    ·
                      rfl

theorem cell23_1019804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1019804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019804 prefixEnd_1019804 := by exact prefixLift 1019804
  have htrace : WordTrace (prefixWord ++ tailWord_1019804) baseStart_1019804 baseEnd_1019804 := by
    simpa [prefixWord, tailWord_1019804, baseEnd_1019804] using wordTrace_append hprefix tailTrace_1019804
  have hstable : (prefixWord ++ tailWord_1019804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019804).length < 2 ^ (prefixWord ++ tailWord_1019804).sum := by decide
  have hdescent : baseEnd_1019804 < baseStart_1019804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019828 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1019828 : Nat := 118140960795 + 1019828 * 2 ^ 59
def prefixEnd_1019828 : Nat := 4983230072969 + 3 ^ 40 * 1019828 * 2
def baseEnd_1019828 : Nat := 523661948913541151959903

theorem tailTrace_1019828 : CollatzResearch.WordTrace tailWord_1019828 prefixEnd_1019828 523661948913541151959903 := by
  unfold tailWord_1019828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598091474672401800454069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24797455299563202400605425 18598091474672401800454069)
  ·
    refine ⟨1743571075750537668792569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18598091474672401800454069 1743571075750537668792569)
    ·
      refine ⟨1307678306812903251594427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743571075750537668792569 1307678306812903251594427)
      ·
        refine ⟨1961517460219354877391641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307678306812903251594427 1961517460219354877391641)
        ·
          refine ⟨1471138095164516158043731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961517460219354877391641 1471138095164516158043731)
          ·
            refine ⟨2206707142746774237065597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471138095164516158043731 2206707142746774237065597)
            ·
              refine ⟨827515178530040338899599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2206707142746774237065597 827515178530040338899599)
              ·
                refine ⟨1241272767795060508349399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827515178530040338899599 1241272767795060508349399)
                ·
                  refine ⟨1861909151692590762524099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241272767795060508349399 1861909151692590762524099)
                  ·
                    refine ⟨2792863727538886143786149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1861909151692590762524099 2792863727538886143786149)
                    ·
                      refine ⟨523661948913541151959903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2792863727538886143786149 523661948913541151959903)
                      ·
                        rfl

theorem cell23_1019828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1019828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019828 prefixEnd_1019828 := by exact prefixLift 1019828
  have htrace : WordTrace (prefixWord ++ tailWord_1019828) baseStart_1019828 baseEnd_1019828 := by
    simpa [prefixWord, tailWord_1019828, baseEnd_1019828] using wordTrace_append hprefix tailTrace_1019828
  have hstable : (prefixWord ++ tailWord_1019828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019828).length < 2 ^ (prefixWord ++ tailWord_1019828).sum := by decide
  have hdescent : baseEnd_1019828 < baseStart_1019828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019850 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1019850 : Nat := 118140960795 + 1019850 * 2 ^ 59
def prefixEnd_1019850 : Nat := 4983230072969 + 3 ^ 40 * 1019850 * 2
def baseEnd_1019850 : Nat := 523673245487940065884801

theorem tailTrace_1019850 : CollatzResearch.WordTrace tailWord_1019850 prefixEnd_1019850 523673245487940065884801 := by
  unfold tailWord_1019850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299246338816275339552251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24797990236843400905472669 9299246338816275339552251)
  ·
    refine ⟨13948869508224413009328377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9299246338816275339552251 13948869508224413009328377)
    ·
      refine ⟨10461652131168309756996283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13948869508224413009328377 10461652131168309756996283)
      ·
        refine ⟨15692478196752464635494425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10461652131168309756996283 15692478196752464635494425)
        ·
          refine ⟨11769358647564348476620819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15692478196752464635494425 11769358647564348476620819)
          ·
            refine ⟨17654037971346522714931229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769358647564348476620819 17654037971346522714931229)
            ·
              refine ⟨6620264239254946018099211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17654037971346522714931229 6620264239254946018099211)
              ·
                refine ⟨9930396358882419027148817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620264239254946018099211 9930396358882419027148817)
                ·
                  refine ⟨7447797269161814270361613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9930396358882419027148817 7447797269161814270361613)
                  ·
                    refine ⟨2792923975935680351385605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7447797269161814270361613 2792923975935680351385605)
                    ·
                      refine ⟨523673245487940065884801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2792923975935680351385605 523673245487940065884801)
                      ·
                        rfl

theorem cell23_1019850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1019850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019850 prefixEnd_1019850 := by exact prefixLift 1019850
  have htrace : WordTrace (prefixWord ++ tailWord_1019850) baseStart_1019850 baseEnd_1019850 := by
    simpa [prefixWord, tailWord_1019850, baseEnd_1019850] using wordTrace_append hprefix tailTrace_1019850
  have hstable : (prefixWord ++ tailWord_1019850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019850).length < 2 ^ (prefixWord ++ tailWord_1019850).sum := by decide
  have hdescent : baseEnd_1019850 < baseStart_1019850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019880 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1019880 : Nat := 118140960795 + 1019880 * 2 ^ 59
def prefixEnd_1019880 : Nat := 4983230072969 + 3 ^ 40 * 1019880 * 2
def baseEnd_1019880 : Nat := 523688649907574948509663

theorem tailTrace_1019880 : CollatzResearch.WordTrace tailWord_1019880 prefixEnd_1019880 523688649907574948509663 := by
  unfold tailWord_1019880
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599039772578208240900547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24798719696770944321200729 18599039772578208240900547)
  ·
    refine ⟨27898559658867312361350821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599039772578208240900547 27898559658867312361350821)
    ·
      refine ⟨5230979936037621067753279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27898559658867312361350821 5230979936037621067753279)
      ·
        refine ⟨7846469904056431601629919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230979936037621067753279 7846469904056431601629919)
        ·
          refine ⟨11769704856084647402444879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846469904056431601629919 11769704856084647402444879)
          ·
            refine ⟨17654557284126971103667319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769704856084647402444879 17654557284126971103667319)
            ·
              refine ⟨26481835926190456655500979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17654557284126971103667319 26481835926190456655500979)
              ·
                refine ⟨39722753889285684983251469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26481835926190456655500979 39722753889285684983251469)
                ·
                  refine ⟨14896032708482131868719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39722753889285684983251469 14896032708482131868719301)
                  ·
                    refine ⟨2793006132840399725384869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14896032708482131868719301 2793006132840399725384869)
                    ·
                      refine ⟨523688649907574948509663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2793006132840399725384869 523688649907574948509663)
                      ·
                        rfl

theorem cell23_1019880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1019880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019880 prefixEnd_1019880 := by exact prefixLift 1019880
  have htrace : WordTrace (prefixWord ++ tailWord_1019880) baseStart_1019880 baseEnd_1019880 := by
    simpa [prefixWord, tailWord_1019880, baseEnd_1019880] using wordTrace_append hprefix tailTrace_1019880
  have hstable : (prefixWord ++ tailWord_1019880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019880).length < 2 ^ (prefixWord ++ tailWord_1019880).sum := by decide
  have hdescent : baseEnd_1019880 < baseStart_1019880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019901 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_1019901 : Nat := 118140960795 + 1019901 * 2 ^ 59
def prefixEnd_1019901 : Nat := 4983230072969 + 3 ^ 40 * 1019901 * 2
def baseEnd_1019901 : Nat := 523699433001319366347067

theorem tailTrace_1019901 : CollatzResearch.WordTrace tailWord_1019901 prefixEnd_1019901 523699433001319366347067 := by
  unfold tailWord_1019901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37198845478080337068315557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24799230318720224712210371 37198845478080337068315557)
  ·
    refine ⟨6974783527140063200309167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37198845478080337068315557 6974783527140063200309167)
    ·
      refine ⟨10462175290710094800463751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974783527140063200309167 10462175290710094800463751)
      ·
        refine ⟨15693262936065142200695627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10462175290710094800463751 15693262936065142200695627)
        ·
          refine ⟨23539894404097713301043441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15693262936065142200695627 23539894404097713301043441)
          ·
            refine ⟨17654920803073284975782581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23539894404097713301043441 17654920803073284975782581)
            ·
              refine ⟨1655148825288120466479617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17654920803073284975782581 1655148825288120466479617)
              ·
                refine ⟨1241361618966090349859713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655148825288120466479617 1241361618966090349859713)
                ·
                  refine ⟨931021214224567762394785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241361618966090349859713 931021214224567762394785)
                  ·
                    refine ⟨698265910668425821796089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 931021214224567762394785 698265910668425821796089)
                    ·
                      refine ⟨523699433001319366347067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698265910668425821796089 523699433001319366347067)
                      ·
                        rfl

theorem cell23_1019901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_1019901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019901 prefixEnd_1019901 := by exact prefixLift 1019901
  have htrace : WordTrace (prefixWord ++ tailWord_1019901) baseStart_1019901 baseEnd_1019901 := by
    simpa [prefixWord, tailWord_1019901, baseEnd_1019901] using wordTrace_append hprefix tailTrace_1019901
  have hstable : (prefixWord ++ tailWord_1019901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019901).length < 2 ^ (prefixWord ++ tailWord_1019901).sum := by decide
  have hdescent : baseEnd_1019901 < baseStart_1019901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019918 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_1019918 : Nat := 118140960795 + 1019918 * 2 ^ 59
def prefixEnd_1019918 : Nat := 4983230072969 + 3 ^ 40 * 1019918 * 2
def baseEnd_1019918 : Nat := 523708162172445799834489

theorem tailTrace_1019918 : CollatzResearch.WordTrace tailWord_1019918 prefixEnd_1019918 523708162172445799834489 := by
  unfold tailWord_1019918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649933189877343621460551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24799643679345832647789605 4649933189877343621460551)
  ·
    refine ⟨6974899784816015432190827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4649933189877343621460551 6974899784816015432190827)
    ·
      refine ⟨10462349677224023148286241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974899784816015432190827 10462349677224023148286241)
      ·
        refine ⟨7846762257918017361214681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10462349677224023148286241 7846762257918017361214681)
        ·
          refine ⟨5885071693438513020911011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846762257918017361214681 5885071693438513020911011)
          ·
            refine ⟨8827607540157769531366517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885071693438513020911011 8827607540157769531366517)
            ·
              refine ⟨827588206889790893565611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8827607540157769531366517 827588206889790893565611)
              ·
                refine ⟨1241382310334686340348417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827588206889790893565611 1241382310334686340348417)
                ·
                  refine ⟨931036732751014755261313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241382310334686340348417 931036732751014755261313)
                  ·
                    refine ⟨698277549563261066445985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 931036732751014755261313 698277549563261066445985)
                    ·
                      refine ⟨523708162172445799834489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698277549563261066445985 523708162172445799834489)
                      ·
                        rfl

theorem cell23_1019918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_1019918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019918 prefixEnd_1019918 := by exact prefixLift 1019918
  have htrace : WordTrace (prefixWord ++ tailWord_1019918) baseStart_1019918 baseEnd_1019918 := by
    simpa [prefixWord, tailWord_1019918, baseEnd_1019918] using wordTrace_append hprefix tailTrace_1019918
  have hstable : (prefixWord ++ tailWord_1019918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019918).length < 2 ^ (prefixWord ++ tailWord_1019918).sum := by decide
  have hdescent : baseEnd_1019918 < baseStart_1019918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019920 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_1019920 : Nat := 118140960795 + 1019920 * 2 ^ 59
def prefixEnd_1019920 : Nat := 4983230072969 + 3 ^ 40 * 1019920 * 2
def baseEnd_1019920 : Nat := 174569729711251597336493

theorem tailTrace_1019920 : CollatzResearch.WordTrace tailWord_1019920 prefixEnd_1019920 174569729711251597336493 := by
  unfold tailWord_1019920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599769232505751656628607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24799692310007668875504809 18599769232505751656628607)
  ·
    refine ⟨27899653848758627484942911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599769232505751656628607 27899653848758627484942911)
    ·
      refine ⟨41849480773137941227414367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27899653848758627484942911 41849480773137941227414367)
      ·
        refine ⟨62774221159706911841121551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41849480773137941227414367 62774221159706911841121551)
        ·
          refine ⟨94161331739560367761682327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62774221159706911841121551 94161331739560367761682327)
          ·
            refine ⟨141241997609340551642523491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94161331739560367761682327 141241997609340551642523491)
            ·
              refine ⟨211862996414010827463785237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141241997609340551642523491 211862996414010827463785237)
              ·
                refine ⟨9931077956906757537364933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211862996414010827463785237 9931077956906757537364933)
                ·
                  refine ⟨1862077116920017038255925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9931077956906757537364933 1862077116920017038255925)
                  ·
                    refine ⟨174569729711251597336493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1862077116920017038255925 174569729711251597336493)
                    ·
                      rfl

theorem cell23_1019920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_1019920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019920 prefixEnd_1019920 := by exact prefixLift 1019920
  have htrace : WordTrace (prefixWord ++ tailWord_1019920) baseStart_1019920 baseEnd_1019920 := by
    simpa [prefixWord, tailWord_1019920, baseEnd_1019920] using wordTrace_append hprefix tailTrace_1019920
  have hstable : (prefixWord ++ tailWord_1019920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019920).length < 2 ^ (prefixWord ++ tailWord_1019920).sum := by decide
  have hdescent : baseEnd_1019920 < baseStart_1019920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019957 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1019957 : Nat := 118140960795 + 1019957 * 2 ^ 59
def prefixEnd_1019957 : Nat := 4983230072969 + 3 ^ 40 * 1019957 * 2
def baseEnd_1019957 : Nat := 523728187917971147246809

theorem tailTrace_1019957 : CollatzResearch.WordTrace tailWord_1019957 prefixEnd_1019957 523728187917971147246809 := by
  unfold tailWord_1019957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37200887965877458632354125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24800591977251639088236083 37200887965877458632354125)
  ·
    refine ⟨13950332987204046987132797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37200887965877458632354125 13950332987204046987132797)
    ·
      refine ⟨5231374870201517620174799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13950332987204046987132797 5231374870201517620174799)
      ·
        refine ⟨7847062305302276430262199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5231374870201517620174799 7847062305302276430262199)
        ·
          refine ⟨11770593457953414645393299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847062305302276430262199 11770593457953414645393299)
          ·
            refine ⟨17655890186930121968089949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770593457953414645393299 17655890186930121968089949)
            ·
              refine ⟨6620958820098795738033731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17655890186930121968089949 6620958820098795738033731)
              ·
                refine ⟨9931438230148193607050597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620958820098795738033731 9931438230148193607050597)
                ·
                  refine ⟨1862144668152786301321987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9931438230148193607050597 1862144668152786301321987)
                  ·
                    refine ⟨2793217002229179451982981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1862144668152786301321987 2793217002229179451982981)
                    ·
                      refine ⟨523728187917971147246809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2793217002229179451982981 523728187917971147246809)
                      ·
                        rfl

theorem cell23_1019957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1019957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019957 prefixEnd_1019957 := by exact prefixLift 1019957
  have htrace : WordTrace (prefixWord ++ tailWord_1019957) baseStart_1019957 baseEnd_1019957 := by
    simpa [prefixWord, tailWord_1019957, baseEnd_1019957] using wordTrace_append hprefix tailTrace_1019957
  have hstable : (prefixWord ++ tailWord_1019957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019957).length < 2 ^ (prefixWord ++ tailWord_1019957).sum := by decide
  have hdescent : baseEnd_1019957 < baseStart_1019957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019977 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_1019977 : Nat := 118140960795 + 1019977 * 2 ^ 59
def prefixEnd_1019977 : Nat := 4983230072969 + 3 ^ 40 * 1019977 * 2
def baseEnd_1019977 : Nat := 523738457531061068996717

theorem tailTrace_1019977 : CollatzResearch.WordTrace tailWord_1019977 prefixEnd_1019977 523738457531061068996717 := by
  unfold tailWord_1019977
  simp only [CollatzResearch.WordTrace]
  refine ⟨37201617425805002048082185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24801078283870001365388123 37201617425805002048082185)
  ·
    refine ⟨27901213069353751536061639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37201617425805002048082185 27901213069353751536061639)
    ·
      refine ⟨41851819604030627304092459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27901213069353751536061639 41851819604030627304092459)
      ·
        refine ⟨62777729406045940956138689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41851819604030627304092459 62777729406045940956138689)
        ·
          refine ⟨47083297054534455717104017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62777729406045940956138689 47083297054534455717104017)
          ·
            refine ⟨35312472790900841787828013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47083297054534455717104017 35312472790900841787828013)
            ·
              refine ⟨13242177296587815670435505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35312472790900841787828013 13242177296587815670435505)
              ·
                refine ⟨9931632972440861752826629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13242177296587815670435505 9931632972440861752826629)
                ·
                  refine ⟨1862181182332661578654993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9931632972440861752826629 1862181182332661578654993)
                  ·
                    refine ⟨1396635886749496183991245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862181182332661578654993 1396635886749496183991245)
                    ·
                      refine ⟨523738457531061068996717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396635886749496183991245 523738457531061068996717)
                      ·
                        rfl

theorem cell23_1019977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_1019977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019977 prefixEnd_1019977 := by exact prefixLift 1019977
  have htrace : WordTrace (prefixWord ++ tailWord_1019977) baseStart_1019977 baseEnd_1019977 := by
    simpa [prefixWord, tailWord_1019977, baseEnd_1019977] using wordTrace_append hprefix tailTrace_1019977
  have hstable : (prefixWord ++ tailWord_1019977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019977).length < 2 ^ (prefixWord ++ tailWord_1019977).sum := by decide
  have hdescent : baseEnd_1019977 < baseStart_1019977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019994 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1019994 : Nat := 118140960795 + 1019994 * 2 ^ 59
def prefixEnd_1019994 : Nat := 4983230072969 + 3 ^ 40 * 1019994 * 2
def baseEnd_1019994 : Nat := 523747186702187502484139

theorem tailTrace_1019994 : CollatzResearch.WordTrace tailWord_1019994 prefixEnd_1019994 523747186702187502484139 := by
  unfold tailWord_1019994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300559366685853487862759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24801491644495609300967357 9300559366685853487862759)
  ·
    refine ⟨13950839050028780231794139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300559366685853487862759 13950839050028780231794139)
    ·
      refine ⟨20926258575043170347691209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13950839050028780231794139 20926258575043170347691209)
      ·
        refine ⟨15694693931282377760768407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20926258575043170347691209 15694693931282377760768407)
        ·
          refine ⟨23542040896923566641152611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694693931282377760768407 23542040896923566641152611)
          ·
            refine ⟨35313061345385349961728917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542040896923566641152611 35313061345385349961728917)
            ·
              refine ⟨1655299750564938279456043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35313061345385349961728917 1655299750564938279456043)
              ·
                refine ⟨2482949625847407419184065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655299750564938279456043 2482949625847407419184065)
                ·
                  refine ⟨1862212219385555564388049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2482949625847407419184065 1862212219385555564388049)
                  ·
                    refine ⟨1396659164539166673291037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862212219385555564388049 1396659164539166673291037)
                    ·
                      refine ⟨523747186702187502484139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396659164539166673291037 523747186702187502484139)
                      ·
                        rfl

theorem cell23_1019994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1019994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1019994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1019994 prefixEnd_1019994 := by exact prefixLift 1019994
  have htrace : WordTrace (prefixWord ++ tailWord_1019994) baseStart_1019994 baseEnd_1019994 := by
    simpa [prefixWord, tailWord_1019994, baseEnd_1019994] using wordTrace_append hprefix tailTrace_1019994
  have hstable : (prefixWord ++ tailWord_1019994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019994).length < 2 ^ (prefixWord ++ tailWord_1019994).sum := by decide
  have hdescent : baseEnd_1019994 < baseStart_1019994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020014 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_1020014 : Nat := 118140960795 + 1020014 * 2 ^ 59
def prefixEnd_1020014 : Nat := 4983230072969 + 3 ^ 40 * 1020014 * 2
def baseEnd_1020014 : Nat := 58195272923919713803783

theorem tailTrace_1020014 : CollatzResearch.WordTrace tailWord_1020014 prefixEnd_1020014 58195272923919713803783 := by
  unfold tailWord_1020014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650370865833869670897387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24801977951113971578119397 4650370865833869670897387)
  ·
    refine ⟨6975556298750804506346081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4650370865833869670897387 6975556298750804506346081)
    ·
      refine ⟨5231667224063103379759561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6975556298750804506346081 5231667224063103379759561)
      ·
        refine ⟨3923750418047327534819671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5231667224063103379759561 3923750418047327534819671)
        ·
          refine ⟨5885625627070991302229507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3923750418047327534819671 5885625627070991302229507)
          ·
            refine ⟨8828438440606486953344261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885625627070991302229507 8828438440606486953344261)
            ·
              refine ⟨1655332207613716303752049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8828438440606486953344261 1655332207613716303752049)
              ·
                refine ⟨1241499155710287227814037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655332207613716303752049 1241499155710287227814037)
                ·
                  refine ⟨58195272923919713803783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1241499155710287227814037 58195272923919713803783)
                  ·
                    rfl

theorem cell23_1020014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_1020014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020014 prefixEnd_1020014 := by exact prefixLift 1020014
  have htrace : WordTrace (prefixWord ++ tailWord_1020014) baseStart_1020014 baseEnd_1020014 := by
    simpa [prefixWord, tailWord_1020014, baseEnd_1020014] using wordTrace_append hprefix tailTrace_1020014
  have hstable : (prefixWord ++ tailWord_1020014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020014).length < 2 ^ (prefixWord ++ tailWord_1020014).sum := by decide
  have hdescent : baseEnd_1020014 < baseStart_1020014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020018 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_1020018 : Nat := 118140960795 + 1020018 * 2 ^ 59
def prefixEnd_1020018 : Nat := 4983230072969 + 3 ^ 40 * 1020018 * 2
def baseEnd_1020018 : Nat := 174586503412631802861343

theorem tailTrace_1020018 : CollatzResearch.WordTrace tailWord_1020018 prefixEnd_1020018 174586503412631802861343 := by
  unfold tailWord_1020018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300778204664116512581177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24802075212437644033549805 9300778204664116512581177)
  ·
    refine ⟨6975583653498087384435883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9300778204664116512581177 6975583653498087384435883)
    ·
      refine ⟨10463375480247131076653825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975583653498087384435883 10463375480247131076653825)
      ·
        refine ⟨7847531610185348307490369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10463375480247131076653825 7847531610185348307490369)
        ·
          refine ⟨5885648707639011230617777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7847531610185348307490369 5885648707639011230617777)
          ·
            refine ⟨4414236530729258422963333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5885648707639011230617777 4414236530729258422963333)
            ·
              refine ⟨827669349511735954305625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4414236530729258422963333 827669349511735954305625)
              ·
                refine ⟨620752012133801965729219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827669349511735954305625 620752012133801965729219)
                ·
                  refine ⟨931128018200702948593829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620752012133801965729219 931128018200702948593829)
                  ·
                    refine ⟨174586503412631802861343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931128018200702948593829 174586503412631802861343)
                    ·
                      rfl

theorem cell23_1020018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_1020018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020018 prefixEnd_1020018 := by exact prefixLift 1020018
  have htrace : WordTrace (prefixWord ++ tailWord_1020018) baseStart_1020018 baseEnd_1020018 := by
    simpa [prefixWord, tailWord_1020018, baseEnd_1020018] using wordTrace_append hprefix tailTrace_1020018
  have hstable : (prefixWord ++ tailWord_1020018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020018).length < 2 ^ (prefixWord ++ tailWord_1020018).sum := by decide
  have hdescent : baseEnd_1020018 < baseStart_1020018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020024 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_1020024 : Nat := 118140960795 + 1020024 * 2 ^ 59
def prefixEnd_1020024 : Nat := 4983230072969 + 3 ^ 40 * 1020024 * 2
def baseEnd_1020024 : Nat := 523762591121822385109001

theorem tailTrace_1020024 : CollatzResearch.WordTrace tailWord_1020024 prefixEnd_1020024 523762591121822385109001 := by
  unfold tailWord_1020024
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601665828317364537521563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24802221104423152716695417 18601665828317364537521563)
  ·
    refine ⟨27902498742476046806282345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18601665828317364537521563 27902498742476046806282345)
    ·
      refine ⟨20926874056857035104711759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27902498742476046806282345 20926874056857035104711759)
      ·
        refine ⟨31390311085285552657067639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926874056857035104711759 31390311085285552657067639)
        ·
          refine ⟨47085466627928328985601459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31390311085285552657067639 47085466627928328985601459)
          ·
            refine ⟨70628199941892493478402189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47085466627928328985601459 70628199941892493478402189)
            ·
              refine ⟨26485574978209685054400821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70628199941892493478402189 26485574978209685054400821)
              ·
                refine ⟨2483022654207157973850077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26485574978209685054400821 2483022654207157973850077)
                ·
                  refine ⟨931133495327684240193779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2483022654207157973850077 931133495327684240193779)
                  ·
                    refine ⟨1396700242991526360290669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931133495327684240193779 1396700242991526360290669)
                    ·
                      refine ⟨523762591121822385109001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396700242991526360290669 523762591121822385109001)
                      ·
                        rfl

theorem cell23_1020024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_1020024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020024 prefixEnd_1020024 := by exact prefixLift 1020024
  have htrace : WordTrace (prefixWord ++ tailWord_1020024) baseStart_1020024 baseEnd_1020024 := by
    simpa [prefixWord, tailWord_1020024, baseEnd_1020024] using wordTrace_append hprefix tailTrace_1020024
  have hstable : (prefixWord ++ tailWord_1020024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020024).length < 2 ^ (prefixWord ++ tailWord_1020024).sum := by decide
  have hdescent : baseEnd_1020024 < baseStart_1020024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020061 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1020061 : Nat := 118140960795 + 1020061 * 2 ^ 59
def prefixEnd_1020061 : Nat := 4983230072969 + 3 ^ 40 * 1020061 * 2
def baseEnd_1020061 : Nat := 174593863302012913448777

theorem tailTrace_1020061 : CollatzResearch.WordTrace tailWord_1020061 prefixEnd_1020061 174593863302012913448777 := by
  unfold tailWord_1020061
  simp only [CollatzResearch.WordTrace]
  refine ⟨37204681157500684394140037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24803120771667122929426691 37204681157500684394140037)
  ·
    refine ⟨6975877717031378323901257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37204681157500684394140037 6975877717031378323901257)
    ·
      refine ⟨5231908287773533742925943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6975877717031378323901257 5231908287773533742925943)
      ·
        refine ⟨7847862431660300614388915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5231908287773533742925943 7847862431660300614388915)
        ·
          refine ⟨11771793647490450921583373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847862431660300614388915 11771793647490450921583373)
          ·
            refine ⟨4414422617808919095593765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11771793647490450921583373 4414422617808919095593765)
            ·
              refine ⟨827704240839172330423831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4414422617808919095593765 827704240839172330423831)
              ·
                refine ⟨1241556361258758495635747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827704240839172330423831 1241556361258758495635747)
                ·
                  refine ⟨1862334541888137743453621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241556361258758495635747 1862334541888137743453621)
                  ·
                    refine ⟨174593863302012913448777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1862334541888137743453621 174593863302012913448777)
                    ·
                      rfl

theorem cell23_1020061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1020061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020061 prefixEnd_1020061 := by exact prefixLift 1020061
  have htrace : WordTrace (prefixWord ++ tailWord_1020061) baseStart_1020061 baseEnd_1020061 := by
    simpa [prefixWord, tailWord_1020061, baseEnd_1020061] using wordTrace_append hprefix tailTrace_1020061
  have hstable : (prefixWord ++ tailWord_1020061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020061).length < 2 ^ (prefixWord ++ tailWord_1020061).sum := by decide
  have hdescent : baseEnd_1020061 < baseStart_1020061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020091 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 2, 4]
def baseStart_1020091 : Nat := 118140960795 + 1020091 * 2 ^ 59
def prefixEnd_1020091 : Nat := 4983230072969 + 3 ^ 40 * 1020091 * 2
def baseEnd_1020091 : Nat := 174598998108557874323731

theorem tailTrace_1020091 : CollatzResearch.WordTrace tailWord_1020091 prefixEnd_1020091 174598998108557874323731 := by
  unfold tailWord_1020091
  simp only [CollatzResearch.WordTrace]
  refine ⟨37205775347391999517732127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24803850231594666345154751 37205775347391999517732127)
  ·
    refine ⟨55808663021087999276598191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37205775347391999517732127 55808663021087999276598191)
    ·
      refine ⟨83712994531631998914897287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55808663021087999276598191 83712994531631998914897287)
      ·
        refine ⟨125569491797447998372345931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83712994531631998914897287 125569491797447998372345931)
        ·
          refine ⟨188354237696171997558518897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125569491797447998372345931 188354237696171997558518897)
          ·
            refine ⟨141265678272128998168889173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188354237696171997558518897 141265678272128998168889173)
            ·
              refine ⟨827728583625755848645835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 141265678272128998168889173 827728583625755848645835)
              ·
                refine ⟨1241592875438633772968753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827728583625755848645835 1241592875438633772968753)
                ·
                  refine ⟨931194656578975329726565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241592875438633772968753 931194656578975329726565)
                  ·
                    refine ⟨174598998108557874323731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931194656578975329726565 174598998108557874323731)
                    ·
                      rfl

theorem cell23_1020091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 4].length) (baseStart_1020091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020091 prefixEnd_1020091 := by exact prefixLift 1020091
  have htrace : WordTrace (prefixWord ++ tailWord_1020091) baseStart_1020091 baseEnd_1020091 := by
    simpa [prefixWord, tailWord_1020091, baseEnd_1020091] using wordTrace_append hprefix tailTrace_1020091
  have hstable : (prefixWord ++ tailWord_1020091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020091).length < 2 ^ (prefixWord ++ tailWord_1020091).sum := by decide
  have hdescent : baseEnd_1020091 < baseStart_1020091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020118 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1020118 : Nat := 118140960795 + 1020118 * 2 ^ 59
def prefixEnd_1020118 : Nat := 4983230072969 + 3 ^ 40 * 1020118 * 2
def baseEnd_1020118 : Nat := 523810858303345017333569

theorem tailTrace_1020118 : CollatzResearch.WordTrace tailWord_1020118 prefixEnd_1020118 523810858303345017333569 := by
  unfold tailWord_1020118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325422507393386445560313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24804506745529455419310005 2325422507393386445560313)
  ·
    refine ⟨1744066880545039834170235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2325422507393386445560313 1744066880545039834170235)
    ·
      refine ⟨2616100320817559751255353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744066880545039834170235 2616100320817559751255353)
      ·
        refine ⟨1962075240613169813441515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616100320817559751255353 1962075240613169813441515)
        ·
          refine ⟨2943112860919754720162273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962075240613169813441515 2943112860919754720162273)
          ·
            refine ⟨2207334645689816040121705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943112860919754720162273 2207334645689816040121705)
            ·
              refine ⟨1655500984267362030091279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207334645689816040121705 1655500984267362030091279)
              ·
                refine ⟨2483251476401043045136919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655500984267362030091279 2483251476401043045136919)
                ·
                  refine ⟨3724877214601564567705379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483251476401043045136919 3724877214601564567705379)
                  ·
                    refine ⟨5587315821902346851558069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3724877214601564567705379 5587315821902346851558069)
                    ·
                      refine ⟨523810858303345017333569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5587315821902346851558069 523810858303345017333569)
                      ·
                        rfl

theorem cell23_1020118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1020118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020118 prefixEnd_1020118 := by exact prefixLift 1020118
  have htrace : WordTrace (prefixWord ++ tailWord_1020118) baseStart_1020118 baseEnd_1020118 := by
    simpa [prefixWord, tailWord_1020118, baseEnd_1020118] using wordTrace_append hprefix tailTrace_1020118
  have hstable : (prefixWord ++ tailWord_1020118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020118).length < 2 ^ (prefixWord ++ tailWord_1020118).sum := by decide
  have hdescent : baseEnd_1020118 < baseStart_1020118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020127 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1020127 : Nat := 118140960795 + 1020127 * 2 ^ 59
def prefixEnd_1020127 : Nat := 4983230072969 + 3 ^ 40 * 1020127 * 2
def baseEnd_1020127 : Nat := 523815479629235482121027

theorem tailTrace_1020127 : CollatzResearch.WordTrace tailWord_1020127 prefixEnd_1020127 523815479629235482121027 := by
  unfold tailWord_1020127
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207088375261577666042635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24804725583507718444028423 37207088375261577666042635)
  ·
    refine ⟨55810632562892366499063953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37207088375261577666042635 55810632562892366499063953)
    ·
      refine ⟨41857974422169274874297965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55810632562892366499063953 41857974422169274874297965)
      ·
        refine ⟨15696740408313478077861737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41857974422169274874297965 15696740408313478077861737)
        ·
          refine ⟨11772555306235108558396303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15696740408313478077861737 11772555306235108558396303)
          ·
            refine ⟨17658832959352662837594455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772555306235108558396303 17658832959352662837594455)
            ·
              refine ⟨26488249439028994256391683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17658832959352662837594455 26488249439028994256391683)
              ·
                refine ⟨39732374158543491384587525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26488249439028994256391683 39732374158543491384587525)
                ·
                  refine ⟨7449820154726904634610161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39732374158543491384587525 7449820154726904634610161)
                  ·
                    refine ⟨5587365116045178475957621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7449820154726904634610161 5587365116045178475957621)
                    ·
                      refine ⟨523815479629235482121027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5587365116045178475957621 523815479629235482121027)
                      ·
                        rfl

theorem cell23_1020127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1020127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020127 prefixEnd_1020127 := by exact prefixLift 1020127
  have htrace : WordTrace (prefixWord ++ tailWord_1020127) baseStart_1020127 baseEnd_1020127 := by
    simpa [prefixWord, tailWord_1020127, baseEnd_1020127] using wordTrace_append hprefix tailTrace_1020127
  have hstable : (prefixWord ++ tailWord_1020127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020127).length < 2 ^ (prefixWord ++ tailWord_1020127).sum := by decide
  have hdescent : baseEnd_1020127 < baseStart_1020127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020137 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_1020137 : Nat := 118140960795 + 1020137 * 2 ^ 59
def prefixEnd_1020137 : Nat := 4983230072969 + 3 ^ 40 * 1020137 * 2
def baseEnd_1020137 : Nat := 523820614435780442995981

theorem tailTrace_1020137 : CollatzResearch.WordTrace tailWord_1020137 prefixEnd_1020137 523820614435780442995981 := by
  unfold tailWord_1020137
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207453105225349373906665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24804968736816899582604443 37207453105225349373906665)
  ·
    refine ⟨27905589828919012030429999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37207453105225349373906665 27905589828919012030429999)
    ·
      refine ⟨41858384743378518045644999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27905589828919012030429999 41858384743378518045644999)
      ·
        refine ⟨62787577115067777068467499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41858384743378518045644999 62787577115067777068467499)
        ·
          refine ⟨94181365672601665602701249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62787577115067777068467499 94181365672601665602701249)
          ·
            refine ⟨70636024254451249202025937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94181365672601665602701249 70636024254451249202025937)
            ·
              refine ⟨52977018190838436901519453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70636024254451249202025937 52977018190838436901519453)
              ·
                refine ⟨19866381821564413838069795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52977018190838436901519453 19866381821564413838069795)
                ·
                  refine ⟨29799572732346620757104693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19866381821564413838069795 29799572732346620757104693)
                  ·
                    refine ⟨2793709943657495695978565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29799572732346620757104693 2793709943657495695978565)
                    ·
                      refine ⟨523820614435780442995981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2793709943657495695978565 523820614435780442995981)
                      ·
                        rfl

theorem cell23_1020137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_1020137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020137 prefixEnd_1020137 := by exact prefixLift 1020137
  have htrace : WordTrace (prefixWord ++ tailWord_1020137) baseStart_1020137 baseEnd_1020137 := by
    simpa [prefixWord, tailWord_1020137, baseEnd_1020137] using wordTrace_append hprefix tailTrace_1020137
  have hstable : (prefixWord ++ tailWord_1020137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020137).length < 2 ^ (prefixWord ++ tailWord_1020137).sum := by decide
  have hdescent : baseEnd_1020137 < baseStart_1020137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020147 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 8]
def baseStart_1020147 : Nat := 118140960795 + 1020147 * 2 ^ 59
def prefixEnd_1020147 : Nat := 4983230072969 + 3 ^ 40 * 1020147 * 2
def baseEnd_1020147 : Nat := 174608583080775134623645

theorem tailTrace_1020147 : CollatzResearch.WordTrace tailWord_1020147 prefixEnd_1020147 174608583080775134623645 := by
  unfold tailWord_1020147
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207817835189121081770695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24805211890126080721180463 37207817835189121081770695)
  ·
    refine ⟨55811726752783681622656043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37207817835189121081770695 55811726752783681622656043)
    ·
      refine ⟨83717590129175522433984065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55811726752783681622656043 83717590129175522433984065)
      ·
        refine ⟨62788192596881641825488049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83717590129175522433984065 62788192596881641825488049)
        ·
          refine ⟨47091144447661231369116037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62788192596881641825488049 47091144447661231369116037)
          ·
            refine ⟨8829589583936480881709257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47091144447661231369116037 8829589583936480881709257)
            ·
              refine ⟨6622192187952360661281943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829589583936480881709257 6622192187952360661281943)
              ·
                refine ⟨9933288281928540991922915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622192187952360661281943 9933288281928540991922915)
                ·
                  refine ⟨14899932422892811487884373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933288281928540991922915 14899932422892811487884373)
                  ·
                    refine ⟨174608583080775134623645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14899932422892811487884373 174608583080775134623645)
                    ·
                      rfl

theorem cell23_1020147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_1020147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020147 prefixEnd_1020147 := by exact prefixLift 1020147
  have htrace : WordTrace (prefixWord ++ tailWord_1020147) baseStart_1020147 baseEnd_1020147 := by
    simpa [prefixWord, tailWord_1020147, baseEnd_1020147] using wordTrace_append hprefix tailTrace_1020147
  have hstable : (prefixWord ++ tailWord_1020147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020147).length < 2 ^ (prefixWord ++ tailWord_1020147).sum := by decide
  have hdescent : baseEnd_1020147 < baseStart_1020147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020158 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_1020158 : Nat := 118140960795 + 1020158 * 2 ^ 59
def prefixEnd_1020158 : Nat := 4983230072969 + 3 ^ 40 * 1020158 * 2
def baseEnd_1020158 : Nat := 523831397529524860833385

theorem tailTrace_1020158 : CollatzResearch.WordTrace tailWord_1020158 prefixEnd_1020158 523831397529524860833385 := by
  unfold tailWord_1020158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651027379768658745052641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24805479358766179973614085 4651027379768658745052641)
  ·
    refine ⟨3488270534826494058789481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4651027379768658745052641 3488270534826494058789481)
    ·
      refine ⟨2616202901119870544092111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3488270534826494058789481 2616202901119870544092111)
      ·
        refine ⟨3924304351679805816138167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616202901119870544092111 3924304351679805816138167)
        ·
          refine ⟨5886456527519708724207251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924304351679805816138167 5886456527519708724207251)
          ·
            refine ⟨8829684791279563086310877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886456527519708724207251 8829684791279563086310877)
            ·
              refine ⟨3311131796729836157366579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8829684791279563086310877 3311131796729836157366579)
              ·
                refine ⟨4966697695094754236049869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311131796729836157366579 4966697695094754236049869)
                ·
                  refine ⟨1862511635660532838518701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4966697695094754236049869 1862511635660532838518701)
                  ·
                    refine ⟨698441863372699814444513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862511635660532838518701 698441863372699814444513)
                    ·
                      refine ⟨523831397529524860833385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698441863372699814444513 523831397529524860833385)
                      ·
                        rfl

theorem cell23_1020158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_1020158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020158 prefixEnd_1020158 := by exact prefixLift 1020158
  have htrace : WordTrace (prefixWord ++ tailWord_1020158) baseStart_1020158 baseEnd_1020158 := by
    simpa [prefixWord, tailWord_1020158, baseEnd_1020158] using wordTrace_append hprefix tailTrace_1020158
  have hstable : (prefixWord ++ tailWord_1020158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020158).length < 2 ^ (prefixWord ++ tailWord_1020158).sum := by decide
  have hdescent : baseEnd_1020158 < baseStart_1020158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020171 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 1, 4, 2]
def baseStart_1020171 : Nat := 118140960795 + 1020171 * 2 ^ 59
def prefixEnd_1020171 : Nat := 4983230072969 + 3 ^ 40 * 1020171 * 2
def baseEnd_1020171 : Nat := 523838072778033309970825

theorem tailTrace_1020171 : CollatzResearch.WordTrace tailWord_1020171 prefixEnd_1020171 523838072778033309970825 := by
  unfold tailWord_1020171
  simp only [CollatzResearch.WordTrace]
  refine ⟨37208693187102173180644367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24805795458068115453762911 37208693187102173180644367)
  ·
    refine ⟨55813039780653259770966551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37208693187102173180644367 55813039780653259770966551)
    ·
      refine ⟨83719559670979889656449827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55813039780653259770966551 83719559670979889656449827)
      ·
        refine ⟨125579339506469834484674741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83719559670979889656449827 125579339506469834484674741)
        ·
          refine ⟨11773063078731546982938257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125579339506469834484674741 11773063078731546982938257)
          ·
            refine ⟨8829797309048660237203693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773063078731546982938257 8829797309048660237203693)
            ·
              refine ⟨3311173990893247588951385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8829797309048660237203693 3311173990893247588951385)
              ·
                refine ⟨2483380493169935691713539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311173990893247588951385 2483380493169935691713539)
                ·
                  refine ⟨3725070739754903537570309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483380493169935691713539 3725070739754903537570309)
                  ·
                    refine ⟨698450763704044413294433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725070739754903537570309 698450763704044413294433)
                    ·
                      refine ⟨523838072778033309970825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698450763704044413294433 523838072778033309970825)
                      ·
                        rfl

theorem cell23_1020171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4, 2].length) (baseStart_1020171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020171 prefixEnd_1020171 := by exact prefixLift 1020171
  have htrace : WordTrace (prefixWord ++ tailWord_1020171) baseStart_1020171 baseEnd_1020171 := by
    simpa [prefixWord, tailWord_1020171, baseEnd_1020171] using wordTrace_append hprefix tailTrace_1020171
  have hstable : (prefixWord ++ tailWord_1020171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020171).length < 2 ^ (prefixWord ++ tailWord_1020171).sum := by decide
  have hdescent : baseEnd_1020171 < baseStart_1020171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020174 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1020174 : Nat := 118140960795 + 1020174 * 2 ^ 59
def prefixEnd_1020174 : Nat := 4983230072969 + 3 ^ 40 * 1020174 * 2
def baseEnd_1020174 : Nat := 523839613219996798233311

theorem tailTrace_1020174 : CollatzResearch.WordTrace tailWord_1020174 prefixEnd_1020174 523839613219996798233311 := by
  unfold tailWord_1020174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651100325761413086625447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24805868404060869795335717 4651100325761413086625447)
  ·
    refine ⟨6976650488642119629938171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4651100325761413086625447 6976650488642119629938171)
    ·
      refine ⟨10464975732963179444907257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976650488642119629938171 10464975732963179444907257)
      ·
        refine ⟨7848731799722384583680443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10464975732963179444907257 7848731799722384583680443)
        ·
          refine ⟨11773097699583576875520665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848731799722384583680443 11773097699583576875520665)
          ·
            refine ⟨8829823274687682656640499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773097699583576875520665 8829823274687682656640499)
            ·
              refine ⟨13244734912031523984960749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829823274687682656640499 13244734912031523984960749)
              ·
                refine ⟨4966775592011821494360281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13244734912031523984960749 4966775592011821494360281)
                ·
                  refine ⟨3725081694008866120770211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966775592011821494360281 3725081694008866120770211)
                  ·
                    refine ⟨5587622541013299181155317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725081694008866120770211 5587622541013299181155317)
                    ·
                      refine ⟨523839613219996798233311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5587622541013299181155317 523839613219996798233311)
                      ·
                        rfl

theorem cell23_1020174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1020174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020174 prefixEnd_1020174 := by exact prefixLift 1020174
  have htrace : WordTrace (prefixWord ++ tailWord_1020174) baseStart_1020174 baseEnd_1020174 := by
    simpa [prefixWord, tailWord_1020174, baseEnd_1020174] using wordTrace_append hprefix tailTrace_1020174
  have hstable : (prefixWord ++ tailWord_1020174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020174).length < 2 ^ (prefixWord ++ tailWord_1020174).sum := by decide
  have hdescent : baseEnd_1020174 < baseStart_1020174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020184 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1020184 : Nat := 118140960795 + 1020184 * 2 ^ 59
def prefixEnd_1020184 : Nat := 4983230072969 + 3 ^ 40 * 1020184 * 2
def baseEnd_1020184 : Nat := 523844748026541759108265

theorem tailTrace_1020184 : CollatzResearch.WordTrace tailWord_1020184 prefixEnd_1020184 523844748026541759108265 := by
  unfold tailWord_1020184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604583668027538200433803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24806111557370050933911737 18604583668027538200433803)
  ·
    refine ⟨27906875502041307300650705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18604583668027538200433803 27906875502041307300650705)
    ·
      refine ⟨20930156626530980475488029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27906875502041307300650705 20930156626530980475488029)
      ·
        refine ⟨7848808734949117678308011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20930156626530980475488029 7848808734949117678308011)
        ·
          refine ⟨11773213102423676517462017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848808734949117678308011 11773213102423676517462017)
          ·
            refine ⟨8829909826817757388096513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773213102423676517462017 8829909826817757388096513)
            ·
              refine ⟨6622432370113318041072385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829909826817757388096513 6622432370113318041072385)
              ·
                refine ⟨4966824277584988530804289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622432370113318041072385 4966824277584988530804289)
                ·
                  refine ⟨3725118208188741398103217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966824277584988530804289 3725118208188741398103217)
                  ·
                    refine ⟨2793838656141556048577413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725118208188741398103217 2793838656141556048577413)
                    ·
                      refine ⟨523844748026541759108265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2793838656141556048577413 523844748026541759108265)
                      ·
                        rfl

theorem cell23_1020184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1020184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020184 prefixEnd_1020184 := by exact prefixLift 1020184
  have htrace : WordTrace (prefixWord ++ tailWord_1020184) baseStart_1020184 baseEnd_1020184 := by
    simpa [prefixWord, tailWord_1020184, baseEnd_1020184] using wordTrace_append hprefix tailTrace_1020184
  have hstable : (prefixWord ++ tailWord_1020184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020184).length < 2 ^ (prefixWord ++ tailWord_1020184).sum := by decide
  have hdescent : baseEnd_1020184 < baseStart_1020184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020187 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_1020187 : Nat := 118140960795 + 1020187 * 2 ^ 59
def prefixEnd_1020187 : Nat := 4983230072969 + 3 ^ 40 * 1020187 * 2
def baseEnd_1020187 : Nat := 523846288468505247370751

theorem tailTrace_1020187 : CollatzResearch.WordTrace tailWord_1020187 prefixEnd_1020187 523846288468505247370751 := by
  unfold tailWord_1020187
  simp only [CollatzResearch.WordTrace]
  refine ⟨37209276755044207913226815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24806184503362805275484543 37209276755044207913226815)
  ·
    refine ⟨55813915132566311869840223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37209276755044207913226815 55813915132566311869840223)
    ·
      refine ⟨83720872698849467804760335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55813915132566311869840223 83720872698849467804760335)
      ·
        refine ⟨125581309048274201707140503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83720872698849467804760335 125581309048274201707140503)
        ·
          refine ⟨188371963572411302560710755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125581309048274201707140503 188371963572411302560710755)
          ·
            refine ⟨282557945358616953841066133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188371963572411302560710755 282557945358616953841066133)
            ·
              refine ⟨13244903688685169711299975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282557945358616953841066133 13244903688685169711299975)
              ·
                refine ⟨19867355533027754566949963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13244903688685169711299975 19867355533027754566949963)
                ·
                  refine ⟨29801033299541631850424945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19867355533027754566949963 29801033299541631850424945)
                  ·
                    refine ⟨22350774974656223887818709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29801033299541631850424945 22350774974656223887818709)
                    ·
                      refine ⟨523846288468505247370751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22350774974656223887818709 523846288468505247370751)
                      ·
                        rfl

theorem cell23_1020187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_1020187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020187 prefixEnd_1020187 := by exact prefixLift 1020187
  have htrace : WordTrace (prefixWord ++ tailWord_1020187) baseStart_1020187 baseEnd_1020187 := by
    simpa [prefixWord, tailWord_1020187, baseEnd_1020187] using wordTrace_append hprefix tailTrace_1020187
  have hstable : (prefixWord ++ tailWord_1020187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020187).length < 2 ^ (prefixWord ++ tailWord_1020187).sum := by decide
  have hdescent : baseEnd_1020187 < baseStart_1020187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020204 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_1020204 : Nat := 118140960795 + 1020204 * 2 ^ 59
def prefixEnd_1020204 : Nat := 4983230072969 + 3 ^ 40 * 1020204 * 2
def baseEnd_1020204 : Nat := 523855017639631680858173

theorem tailTrace_1020204 : CollatzResearch.WordTrace tailWord_1020204 prefixEnd_1020204 523855017639631680858173 := by
  unfold tailWord_1020204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604948397991309908297833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24806597863988413211063777 18604948397991309908297833)
  ·
    refine ⟨13953711298493482431223375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18604948397991309908297833 13953711298493482431223375)
    ·
      refine ⟨20930566947740223646835063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953711298493482431223375 20930566947740223646835063)
      ·
        refine ⟨31395850421610335470252595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20930566947740223646835063 31395850421610335470252595)
        ·
          refine ⟨47093775632415503205378893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31395850421610335470252595 47093775632415503205378893)
          ·
            refine ⟨17660165862155813702017085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47093775632415503205378893 17660165862155813702017085)
            ·
              refine ⟨6622562198308430138256407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17660165862155813702017085 6622562198308430138256407)
              ·
                refine ⟨9933843297462645207384611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622562198308430138256407 9933843297462645207384611)
                ·
                  refine ⟨14900764946193967811076917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933843297462645207384611 14900764946193967811076917)
                  ·
                    refine ⟨1396946713705684482288461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14900764946193967811076917 1396946713705684482288461)
                    ·
                      refine ⟨523855017639631680858173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1396946713705684482288461 523855017639631680858173)
                      ·
                        rfl

theorem cell23_1020204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_1020204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020204 prefixEnd_1020204 := by exact prefixLift 1020204
  have htrace : WordTrace (prefixWord ++ tailWord_1020204) baseStart_1020204 baseEnd_1020204 := by
    simpa [prefixWord, tailWord_1020204, baseEnd_1020204] using wordTrace_append hprefix tailTrace_1020204
  have hstable : (prefixWord ++ tailWord_1020204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020204).length < 2 ^ (prefixWord ++ tailWord_1020204).sum := by decide
  have hdescent : baseEnd_1020204 < baseStart_1020204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020224 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_1020224 : Nat := 118140960795 + 1020224 * 2 ^ 59
def prefixEnd_1020224 : Nat := 4983230072969 + 3 ^ 40 * 1020224 * 2
def baseEnd_1020224 : Nat := 174621762417573867536027

theorem tailTrace_1020224 : CollatzResearch.WordTrace tailWord_1020224 prefixEnd_1020224 174621762417573867536027 := by
  unfold tailWord_1020224
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605313127955081616161863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24807084170606775488215817 18605313127955081616161863)
  ·
    refine ⟨27907969691932622424242795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18605313127955081616161863 27907969691932622424242795)
    ·
      refine ⟨41861954537898933636364193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27907969691932622424242795 41861954537898933636364193)
      ·
        refine ⟨31396465903424200227273145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41861954537898933636364193 31396465903424200227273145)
        ·
          refine ⟨23547349427568150170454859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31396465903424200227273145 23547349427568150170454859)
          ·
            refine ⟨35321024141352225255682289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23547349427568150170454859 35321024141352225255682289)
            ·
              refine ⟨26490768106014168941761717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35321024141352225255682289 26490768106014168941761717)
              ·
                refine ⟨2483509509938828338290161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26490768106014168941761717 2483509509938828338290161)
                ·
                  refine ⟨1862632132454121253717621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483509509938828338290161 1862632132454121253717621)
                  ·
                    refine ⟨174621762417573867536027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1862632132454121253717621 174621762417573867536027)
                    ·
                      rfl

theorem cell23_1020224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_1020224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020224 prefixEnd_1020224 := by exact prefixLift 1020224
  have htrace : WordTrace (prefixWord ++ tailWord_1020224) baseStart_1020224 baseEnd_1020224 := by
    simpa [prefixWord, tailWord_1020224, baseEnd_1020224] using wordTrace_append hprefix tailTrace_1020224
  have hstable : (prefixWord ++ tailWord_1020224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020224).length < 2 ^ (prefixWord ++ tailWord_1020224).sum := by decide
  have hdescent : baseEnd_1020224 < baseStart_1020224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020281 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_1020281 : Nat := 118140960795 + 1020281 * 2 ^ 59
def prefixEnd_1020281 : Nat := 4983230072969 + 3 ^ 40 * 1020281 * 2
def baseEnd_1020281 : Nat := 523894555650027879595319

theorem tailTrace_1020281 : CollatzResearch.WordTrace tailWord_1020281 prefixEnd_1020281 523894555650027879595319 := by
  unfold tailWord_1020281
  simp only [CollatzResearch.WordTrace]
  refine ⟨37212705216703661967148697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24808470144469107978099131 37212705216703661967148697)
  ·
    refine ⟨27909528912527746475361523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37212705216703661967148697 27909528912527746475361523)
    ·
      refine ⟨41864293368791619713042285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909528912527746475361523 41864293368791619713042285)
      ·
        refine ⟨15699110013296857392390857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41864293368791619713042285 15699110013296857392390857)
        ·
          refine ⟨11774332509972643044293143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15699110013296857392390857 11774332509972643044293143)
          ·
            refine ⟨17661498764958964566439715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774332509972643044293143 17661498764958964566439715)
            ·
              refine ⟨26492248147438446849659573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17661498764958964566439715 26492248147438446849659573)
              ·
                refine ⟨2483648263822354392155585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26492248147438446849659573 2483648263822354392155585)
                ·
                  refine ⟨1862736197866765794116689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483648263822354392155585 1862736197866765794116689)
                  ·
                    refine ⟨1397052148400074345587517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862736197866765794116689 1397052148400074345587517)
                    ·
                      refine ⟨523894555650027879595319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397052148400074345587517 523894555650027879595319)
                      ·
                        rfl

theorem cell23_1020281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_1020281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020281 prefixEnd_1020281 := by exact prefixLift 1020281
  have htrace : WordTrace (prefixWord ++ tailWord_1020281) baseStart_1020281 baseEnd_1020281 := by
    simpa [prefixWord, tailWord_1020281, baseEnd_1020281] using wordTrace_append hprefix tailTrace_1020281
  have hstable : (prefixWord ++ tailWord_1020281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020281).length < 2 ^ (prefixWord ++ tailWord_1020281).sum := by decide
  have hdescent : baseEnd_1020281 < baseStart_1020281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020356 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1020356 : Nat := 118140960795 + 1020356 * 2 ^ 59
def prefixEnd_1020356 : Nat := 4983230072969 + 3 ^ 40 * 1020356 * 2
def baseEnd_1020356 : Nat := 174644355566371695385825

theorem tailTrace_1020356 : CollatzResearch.WordTrace tailWord_1020356 prefixEnd_1020356 174644355566371695385825 := by
  unfold tailWord_1020356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607720345715974888064461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24810293794287966517419281 18607720345715974888064461)
  ·
    refine ⟨6977895129643490583024173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18607720345715974888064461 6977895129643490583024173)
    ·
      refine ⟨2616710673616308968634065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6977895129643490583024173 2616710673616308968634065)
      ·
        refine ⟨1962533005212231726475549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616710673616308968634065 1962533005212231726475549)
        ·
          refine ⟨735949876954586897428331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1962533005212231726475549 735949876954586897428331)
          ·
            refine ⟨1103924815431880346142497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735949876954586897428331 1103924815431880346142497)
            ·
              refine ⟨827943611573910259606873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103924815431880346142497 827943611573910259606873)
              ·
                refine ⟨620957708680432694705155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827943611573910259606873 620957708680432694705155)
                ·
                  refine ⟨931436563020649042057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620957708680432694705155 931436563020649042057733)
                  ·
                    refine ⟨174644355566371695385825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931436563020649042057733 174644355566371695385825)
                    ·
                      rfl

theorem cell23_1020356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1020356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020356 prefixEnd_1020356 := by exact prefixLift 1020356
  have htrace : WordTrace (prefixWord ++ tailWord_1020356) baseStart_1020356 baseEnd_1020356 := by
    simpa [prefixWord, tailWord_1020356, baseEnd_1020356] using wordTrace_append hprefix tailTrace_1020356
  have hstable : (prefixWord ++ tailWord_1020356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020356).length < 2 ^ (prefixWord ++ tailWord_1020356).sum := by decide
  have hdescent : baseEnd_1020356 < baseStart_1020356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020361 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_1020361 : Nat := 118140960795 + 1020361 * 2 ^ 59
def prefixEnd_1020361 : Nat := 4983230072969 + 3 ^ 40 * 1020361 * 2
def baseEnd_1020361 : Nat := 174645211367462522198317

theorem tailTrace_1020361 : CollatzResearch.WordTrace tailWord_1020361 prefixEnd_1020361 174645211367462522198317 := by
  unfold tailWord_1020361
  simp only [CollatzResearch.WordTrace]
  refine ⟨37215623056413835630060937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24810415370942557086707291 37215623056413835630060937)
  ·
    refine ⟨27911717292310376722545703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37215623056413835630060937 27911717292310376722545703)
    ·
      refine ⟨41867575938465565083818555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27911717292310376722545703 41867575938465565083818555)
      ·
        refine ⟨62801363907698347625727833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41867575938465565083818555 62801363907698347625727833)
        ·
          refine ⟨47101022930773760719295875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62801363907698347625727833 47101022930773760719295875)
          ·
            refine ⟨70651534396160641078943813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47101022930773760719295875 70651534396160641078943813)
            ·
              refine ⟨13247162699280120202301965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70651534396160641078943813 13247162699280120202301965)
              ·
                refine ⟨4967686012230045075863237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13247162699280120202301965 4967686012230045075863237)
                ·
                  refine ⟨931441127293133451724357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4967686012230045075863237 931441127293133451724357)
                  ·
                    refine ⟨174645211367462522198317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931441127293133451724357 174645211367462522198317)
                    ·
                      rfl

theorem cell23_1020361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_1020361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020361 prefixEnd_1020361 := by exact prefixLift 1020361
  have htrace : WordTrace (prefixWord ++ tailWord_1020361) baseStart_1020361 baseEnd_1020361 := by
    simpa [prefixWord, tailWord_1020361, baseEnd_1020361] using wordTrace_append hprefix tailTrace_1020361
  have hstable : (prefixWord ++ tailWord_1020361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020361).length < 2 ^ (prefixWord ++ tailWord_1020361).sum := by decide
  have hdescent : baseEnd_1020361 < baseStart_1020361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020378 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_1020378 : Nat := 118140960795 + 1020378 * 2 ^ 59
def prefixEnd_1020378 : Nat := 4983230072969 + 3 ^ 40 * 1020378 * 2
def baseEnd_1020378 : Nat := 174648121091171333360791

theorem tailTrace_1020378 : CollatzResearch.WordTrace tailWord_1020378 prefixEnd_1020378 174648121091171333360791 := by
  unfold tailWord_1020378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304060774338061883357447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24810828731568165022286525 9304060774338061883357447)
  ·
    refine ⟨13956091161507092825036171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9304060774338061883357447 13956091161507092825036171)
    ·
      refine ⟨20934136742260639237554257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13956091161507092825036171 20934136742260639237554257)
      ·
        refine ⟨15700602556695479428165693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20934136742260639237554257 15700602556695479428165693)
        ·
          refine ⟨5887725958760804785562135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15700602556695479428165693 5887725958760804785562135)
          ·
            refine ⟨8831588938141207178343203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887725958760804785562135 8831588938141207178343203)
            ·
              refine ⟨13247383407211810767514805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8831588938141207178343203 13247383407211810767514805)
              ·
                refine ⟨1241942194426107259454513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13247383407211810767514805 1241942194426107259454513)
                ·
                  refine ⟨931456645819580444590885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241942194426107259454513 931456645819580444590885)
                  ·
                    refine ⟨174648121091171333360791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931456645819580444590885 174648121091171333360791)
                    ·
                      rfl

theorem cell23_1020378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_1020378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020378 prefixEnd_1020378 := by exact prefixLift 1020378
  have htrace : WordTrace (prefixWord ++ tailWord_1020378) baseStart_1020378 baseEnd_1020378 := by
    simpa [prefixWord, tailWord_1020378, baseEnd_1020378] using wordTrace_append hprefix tailTrace_1020378
  have hstable : (prefixWord ++ tailWord_1020378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020378).length < 2 ^ (prefixWord ++ tailWord_1020378).sum := by decide
  have hdescent : baseEnd_1020378 < baseStart_1020378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020385 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_1020385 : Nat := 118140960795 + 1020385 * 2 ^ 59
def prefixEnd_1020385 : Nat := 4983230072969 + 3 ^ 40 * 1020385 * 2
def baseEnd_1020385 : Nat := 523947957638095472694841

theorem tailTrace_1020385 : CollatzResearch.WordTrace tailWord_1020385 prefixEnd_1020385 523947957638095472694841 := by
  unfold tailWord_1020385
  simp only [CollatzResearch.WordTrace]
  refine ⟨37216498408326887728934609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24810998938884591819289739 37216498408326887728934609)
  ·
    refine ⟨27912373806245165796700957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37216498408326887728934609 27912373806245165796700957)
    ·
      refine ⟨10467140177341937173762859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27912373806245165796700957 10467140177341937173762859)
      ·
        refine ⟨15700710266012905760644289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467140177341937173762859 15700710266012905760644289)
        ·
          refine ⟨11775532699509679320483217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15700710266012905760644289 11775532699509679320483217)
          ·
            refine ⟨8831649524632259490362413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11775532699509679320483217 8831649524632259490362413)
            ·
              refine ⟨3311868571737097308885905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8831649524632259490362413 3311868571737097308885905)
              ·
                refine ⟨2483901428802822981664429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311868571737097308885905 2483901428802822981664429)
                ·
                  refine ⟨931463035801058618124161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2483901428802822981664429 931463035801058618124161)
                  ·
                    refine ⟨698597276850793963593121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 931463035801058618124161 698597276850793963593121)
                    ·
                      refine ⟨523947957638095472694841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698597276850793963593121 523947957638095472694841)
                      ·
                        rfl

theorem cell23_1020385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_1020385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020385 prefixEnd_1020385 := by exact prefixLift 1020385
  have htrace : WordTrace (prefixWord ++ tailWord_1020385) baseStart_1020385 baseEnd_1020385 := by
    simpa [prefixWord, tailWord_1020385, baseEnd_1020385] using wordTrace_append hprefix tailTrace_1020385
  have hstable : (prefixWord ++ tailWord_1020385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020385).length < 2 ^ (prefixWord ++ tailWord_1020385).sum := by decide
  have hdescent : baseEnd_1020385 < baseStart_1020385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020389 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1020389 : Nat := 118140960795 + 1020389 * 2 ^ 59
def prefixEnd_1020389 : Nat := 4983230072969 + 3 ^ 40 * 1020389 * 2
def baseEnd_1020389 : Nat := 523950011560713457044823

theorem tailTrace_1020389 : CollatzResearch.WordTrace tailWord_1020389 prefixEnd_1020389 523950011560713457044823 := by
  unfold tailWord_1020389
  simp only [CollatzResearch.WordTrace]
  refine ⟨37216644300312396412080221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24811096200208264274720147 37216644300312396412080221)
  ·
    refine ⟨13956241612617148654530083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37216644300312396412080221 13956241612617148654530083)
    ·
      refine ⟨20934362418925722981795125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13956241612617148654530083 20934362418925722981795125)
      ·
        refine ⟨1962596476774286529543293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20934362418925722981795125 1962596476774286529543293)
        ·
          refine ⟨735973678790357448578735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1962596476774286529543293 735973678790357448578735)
          ·
            refine ⟨1103960518185536172868103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735973678790357448578735 1103960518185536172868103)
            ·
              refine ⟨1655940777278304259302155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103960518185536172868103 1655940777278304259302155)
              ·
                refine ⟨2483911165917456388953233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655940777278304259302155 2483911165917456388953233)
                ·
                  refine ⟨1862933374438092291714925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483911165917456388953233 1862933374438092291714925)
                  ·
                    refine ⟨698600015414284609393097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1862933374438092291714925 698600015414284609393097)
                    ·
                      refine ⟨523950011560713457044823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698600015414284609393097 523950011560713457044823)
                      ·
                        rfl

theorem cell23_1020389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1020389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020389 prefixEnd_1020389 := by exact prefixLift 1020389
  have htrace : WordTrace (prefixWord ++ tailWord_1020389) baseStart_1020389 baseEnd_1020389 := by
    simpa [prefixWord, tailWord_1020389, baseEnd_1020389] using wordTrace_append hprefix tailTrace_1020389
  have hstable : (prefixWord ++ tailWord_1020389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020389).length < 2 ^ (prefixWord ++ tailWord_1020389).sum := by decide
  have hdescent : baseEnd_1020389 < baseStart_1020389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020398 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1020398 : Nat := 118140960795 + 1020398 * 2 ^ 59
def prefixEnd_1020398 : Nat := 4983230072969 + 3 ^ 40 * 1020398 * 2
def baseEnd_1020398 : Nat := 523954632886603921832281

theorem tailTrace_1020398 : CollatzResearch.WordTrace tailWord_1020398 prefixEnd_1020398 523954632886603921832281 := by
  unfold tailWord_1020398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652121569659973868644731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24811315038186527299438565 4652121569659973868644731)
  ·
    refine ⟨6978182354489960802967097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4652121569659973868644731 6978182354489960802967097)
    ·
      refine ⟨5233636765867470602225323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6978182354489960802967097 5233636765867470602225323)
      ·
        refine ⟨7850455148801205903337985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233636765867470602225323 7850455148801205903337985)
        ·
          refine ⟨5887841361600904427503489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7850455148801205903337985 5887841361600904427503489)
          ·
            refine ⟨4415881021200678320627617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5887841361600904427503489 4415881021200678320627617)
            ·
              refine ⟨3311910765900508740470713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415881021200678320627617 3311910765900508740470713)
              ·
                refine ⟨2483933074425381555353035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311910765900508740470713 2483933074425381555353035)
                ·
                  refine ⟨3725899611638072333029553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483933074425381555353035 3725899611638072333029553)
                  ·
                    refine ⟨2794424708728554249772165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725899611638072333029553 2794424708728554249772165)
                    ·
                      refine ⟨523954632886603921832281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2794424708728554249772165 523954632886603921832281)
                      ·
                        rfl

theorem cell23_1020398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1020398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020398 prefixEnd_1020398 := by exact prefixLift 1020398
  have htrace : WordTrace (prefixWord ++ tailWord_1020398) baseStart_1020398 baseEnd_1020398 := by
    simpa [prefixWord, tailWord_1020398, baseEnd_1020398] using wordTrace_append hprefix tailTrace_1020398
  have hstable : (prefixWord ++ tailWord_1020398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020398).length < 2 ^ (prefixWord ++ tailWord_1020398).sum := by decide
  have hdescent : baseEnd_1020398 < baseStart_1020398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020422 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1020422 : Nat := 118140960795 + 1020422 * 2 ^ 59
def prefixEnd_1020422 : Nat := 4983230072969 + 3 ^ 40 * 1020422 * 2
def baseEnd_1020422 : Nat := 523966956422311827932171

theorem tailTrace_1020422 : CollatzResearch.WordTrace tailWord_1020422 prefixEnd_1020422 523966956422311827932171 := by
  unfold tailWord_1020422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163057747162276345250985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24811898606128562032021013 1163057747162276345250985)
  ·
    refine ⟨872293310371707258938239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1163057747162276345250985 872293310371707258938239)
    ·
      refine ⟨1308439965557560888407359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872293310371707258938239 1308439965557560888407359)
      ·
        refine ⟨1962659948336341332611039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308439965557560888407359 1962659948336341332611039)
        ·
          refine ⟨2943989922504511998916559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962659948336341332611039 2943989922504511998916559)
          ·
            refine ⟨4415984883756767998374839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943989922504511998916559 4415984883756767998374839)
            ·
              refine ⟨6623977325635151997562259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415984883756767998374839 6623977325635151997562259)
              ·
                refine ⟨9935965988452727996343389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623977325635151997562259 9935965988452727996343389)
                ·
                  refine ⟨3725987245669772998628771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9935965988452727996343389 3725987245669772998628771)
                  ·
                    refine ⟨5588980868504659497943157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725987245669772998628771 5588980868504659497943157)
                    ·
                      refine ⟨523966956422311827932171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5588980868504659497943157 523966956422311827932171)
                      ·
                        rfl

theorem cell23_1020422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1020422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020422 prefixEnd_1020422 := by exact prefixLift 1020422
  have htrace : WordTrace (prefixWord ++ tailWord_1020422) baseStart_1020422 baseEnd_1020422 := by
    simpa [prefixWord, tailWord_1020422, baseEnd_1020422] using wordTrace_append hprefix tailTrace_1020422
  have hstable : (prefixWord ++ tailWord_1020422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020422).length < 2 ^ (prefixWord ++ tailWord_1020422).sum := by decide
  have hdescent : baseEnd_1020422 < baseStart_1020422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020486 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1020486 : Nat := 118140960795 + 1020486 * 2 ^ 59
def prefixEnd_1020486 : Nat := 4983230072969 + 3 ^ 40 * 1020486 * 2
def baseEnd_1020486 : Nat := 523999819184199577531877

theorem tailTrace_1020486 : CollatzResearch.WordTrace tailWord_1020486 prefixEnd_1020486 523999819184199577531877 := by
  unfold tailWord_1020486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163130693155030686823791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24813454787307321318907541 1163130693155030686823791)
  ·
    refine ⟨1744696039732546030235687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163130693155030686823791 1744696039732546030235687)
    ·
      refine ⟨2617044059598819045353531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744696039732546030235687 2617044059598819045353531)
      ·
        refine ⟨3925566089398228568030297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617044059598819045353531 3925566089398228568030297)
        ·
          refine ⟨2944174567048671426022723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925566089398228568030297 2944174567048671426022723)
          ·
            refine ⟨4416261850573007139034085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944174567048671426022723 4416261850573007139034085)
            ·
              refine ⟨828049096982438838568891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4416261850573007139034085 828049096982438838568891)
              ·
                refine ⟨1242073645473658257853337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828049096982438838568891 1242073645473658257853337)
                ·
                  refine ⟨931555234105243693390003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242073645473658257853337 931555234105243693390003)
                  ·
                    refine ⟨1397332851157865540085005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931555234105243693390003 1397332851157865540085005)
                    ·
                      refine ⟨523999819184199577531877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397332851157865540085005 523999819184199577531877)
                      ·
                        rfl

theorem cell23_1020486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1020486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020486 prefixEnd_1020486 := by exact prefixLift 1020486
  have htrace : WordTrace (prefixWord ++ tailWord_1020486) baseStart_1020486 baseEnd_1020486 := by
    simpa [prefixWord, tailWord_1020486, baseEnd_1020486] using wordTrace_append hprefix tailTrace_1020486
  have hstable : (prefixWord ++ tailWord_1020486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020486).length < 2 ^ (prefixWord ++ tailWord_1020486).sum := by decide
  have hdescent : baseEnd_1020486 < baseStart_1020486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020492 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1020492 : Nat := 118140960795 + 1020492 * 2 ^ 59
def prefixEnd_1020492 : Nat := 4983230072969 + 3 ^ 40 * 1020492 * 2
def baseEnd_1020492 : Nat := 524002900068126554056849

theorem tailTrace_1020492 : CollatzResearch.WordTrace tailWord_1020492 prefixEnd_1020492 524002900068126554056849 := by
  unfold tailWord_1020492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610200509469622501539865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24813600679292830002053153 18610200509469622501539865)
  ·
    refine ⟨13957650382102216876154899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18610200509469622501539865 13957650382102216876154899)
    ·
      refine ⟨20936475573153325314232349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13957650382102216876154899 20936475573153325314232349)
      ·
        refine ⟨7851178339932496992837131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20936475573153325314232349 7851178339932496992837131)
        ·
          refine ⟨11776767509898745489255697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7851178339932496992837131 11776767509898745489255697)
          ·
            refine ⟨8832575632424059116941773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11776767509898745489255697 8832575632424059116941773)
            ·
              refine ⟨3312215862159022168853165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8832575632424059116941773 3312215862159022168853165)
              ·
                refine ⟨1242080948309633313319937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312215862159022168853165 1242080948309633313319937)
                ·
                  refine ⟨931560711232224984989953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242080948309633313319937 931560711232224984989953)
                  ·
                    refine ⟨698670533424168738742465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 931560711232224984989953 698670533424168738742465)
                    ·
                      refine ⟨524002900068126554056849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698670533424168738742465 524002900068126554056849)
                      ·
                        rfl

theorem cell23_1020492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1020492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020492 prefixEnd_1020492 := by exact prefixLift 1020492
  have htrace : WordTrace (prefixWord ++ tailWord_1020492) baseStart_1020492 baseEnd_1020492 := by
    simpa [prefixWord, tailWord_1020492, baseEnd_1020492] using wordTrace_append hprefix tailTrace_1020492
  have hstable : (prefixWord ++ tailWord_1020492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020492).length < 2 ^ (prefixWord ++ tailWord_1020492).sum := by decide
  have hdescent : baseEnd_1020492 < baseStart_1020492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020511 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 7]
def baseStart_1020511 : Nat := 118140960795 + 1020511 * 2 ^ 59
def prefixEnd_1020511 : Nat := 4983230072969 + 3 ^ 40 * 1020511 * 2
def baseEnd_1020511 : Nat := 174670885400187326573087

theorem tailTrace_1020511 : CollatzResearch.WordTrace tailWord_1020511 prefixEnd_1020511 174670885400187326573087 := by
  unfold tailWord_1020511
  simp only [CollatzResearch.WordTrace]
  refine ⟨37221094005870411248021387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24814062670580274165347591 37221094005870411248021387)
  ·
    refine ⟨55831641008805616872032081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37221094005870411248021387 55831641008805616872032081)
    ·
      refine ⟨41873730756604212654024061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55831641008805616872032081 41873730756604212654024061)
      ·
        refine ⟨15702649033726579745259023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41873730756604212654024061 15702649033726579745259023)
        ·
          refine ⟨23553973550589869617888535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15702649033726579745259023 23553973550589869617888535)
          ·
            refine ⟨35330960325884804426832803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23553973550589869617888535 35330960325884804426832803)
            ·
              refine ⟨52996440488827206640249205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35330960325884804426832803 52996440488827206640249205)
              ·
                refine ⟨4968416295827550622523363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52996440488827206640249205 4968416295827550622523363)
                ·
                  refine ⟨7452624443741325933785045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968416295827550622523363 7452624443741325933785045)
                  ·
                    refine ⟨174670885400187326573087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7452624443741325933785045 174670885400187326573087)
                    ·
                      rfl

theorem cell23_1020511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_1020511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020511 prefixEnd_1020511 := by exact prefixLift 1020511
  have htrace : WordTrace (prefixWord ++ tailWord_1020511) baseStart_1020511 baseEnd_1020511 := by
    simpa [prefixWord, tailWord_1020511, baseEnd_1020511] using wordTrace_append hprefix tailTrace_1020511
  have hstable : (prefixWord ++ tailWord_1020511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020511).length < 2 ^ (prefixWord ++ tailWord_1020511).sum := by decide
  have hdescent : baseEnd_1020511 < baseStart_1020511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020562 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1020562 : Nat := 118140960795 + 1020562 * 2 ^ 59
def prefixEnd_1020562 : Nat := 4983230072969 + 3 ^ 40 * 1020562 * 2
def baseEnd_1020562 : Nat := 174679614571313760060509

theorem tailTrace_1020562 : CollatzResearch.WordTrace tailWord_1020562 prefixEnd_1020562 174679614571313760060509 := by
  unfold tailWord_1020562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305738532171411739531985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24815302752457097972085293 9305738532171411739531985)
  ·
    refine ⟨6979303899128558804648989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9305738532171411739531985 6979303899128558804648989)
    ·
      refine ⟨2617238962173209551743371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6979303899128558804648989 2617238962173209551743371)
      ·
        refine ⟨3925858443259814327615057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617238962173209551743371 3925858443259814327615057)
        ·
          refine ⟨2944393832444860745711293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925858443259814327615057 2944393832444860745711293)
          ·
            refine ⟨1104147687166822779641735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2944393832444860745711293 1104147687166822779641735)
            ·
              refine ⟨1656221530750234169462603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104147687166822779641735 1656221530750234169462603)
              ·
                refine ⟨2484332296125351254193905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656221530750234169462603 2484332296125351254193905)
                ·
                  refine ⟨1863249222094013440645429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2484332296125351254193905 1863249222094013440645429)
                  ·
                    refine ⟨174679614571313760060509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1863249222094013440645429 174679614571313760060509)
                    ·
                      rfl

theorem cell23_1020562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1020562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020562 prefixEnd_1020562 := by exact prefixLift 1020562
  have htrace : WordTrace (prefixWord ++ tailWord_1020562) baseStart_1020562 baseEnd_1020562 := by
    simpa [prefixWord, tailWord_1020562, baseEnd_1020562] using wordTrace_append hprefix tailTrace_1020562
  have hstable : (prefixWord ++ tailWord_1020562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020562).length < 2 ^ (prefixWord ++ tailWord_1020562).sum := by decide
  have hdescent : baseEnd_1020562 < baseStart_1020562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020615 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_1020615 : Nat := 118140960795 + 1020615 * 2 ^ 59
def prefixEnd_1020615 : Nat := 4983230072969 + 3 ^ 40 * 1020615 * 2
def baseEnd_1020615 : Nat := 524066058188629572818783

theorem tailTrace_1020615 : CollatzResearch.WordTrace tailWord_1020615 prefixEnd_1020615 524066058188629572818783 := by
  unfold tailWord_1020615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224887197493637009807299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24816591464995758006538199 37224887197493637009807299)
  ·
    refine ⟨55837330796240455514710949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37224887197493637009807299 55837330796240455514710949)
    ·
      refine ⟨10469499524295085409008303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55837330796240455514710949 10469499524295085409008303)
      ·
        refine ⟨15704249286442628113512455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10469499524295085409008303 15704249286442628113512455)
        ·
          refine ⟨23556373929663942170268683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15704249286442628113512455 23556373929663942170268683)
          ·
            refine ⟨35334560894495913255403025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23556373929663942170268683 35334560894495913255403025)
            ·
              refine ⟨26500920670871934941552269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35334560894495913255403025 26500920670871934941552269)
              ·
                refine ⟨9937845251576975603082101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26500920670871934941552269 9937845251576975603082101)
                ·
                  refine ⟨931672992335341462788947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9937845251576975603082101 931672992335341462788947)
                  ·
                    refine ⟨1397509488503012194183421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931672992335341462788947 1397509488503012194183421)
                    ·
                      refine ⟨524066058188629572818783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397509488503012194183421 524066058188629572818783)
                      ·
                        rfl

theorem cell23_1020615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_1020615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020615 prefixEnd_1020615 := by exact prefixLift 1020615
  have htrace : WordTrace (prefixWord ++ tailWord_1020615) baseStart_1020615 baseEnd_1020615 := by
    simpa [prefixWord, tailWord_1020615, baseEnd_1020615] using wordTrace_append hprefix tailTrace_1020615
  have hstable : (prefixWord ++ tailWord_1020615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020615).length < 2 ^ (prefixWord ++ tailWord_1020615).sum := by decide
  have hdescent : baseEnd_1020615 < baseStart_1020615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020625 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_1020625 : Nat := 118140960795 + 1020625 * 2 ^ 59
def prefixEnd_1020625 : Nat := 4983230072969 + 3 ^ 40 * 1020625 * 2
def baseEnd_1020625 : Nat := 524071192995174533693737

theorem tailTrace_1020625 : CollatzResearch.WordTrace tailWord_1020625 prefixEnd_1020625 524071192995174533693737 := by
  unfold tailWord_1020625
  simp only [CollatzResearch.WordTrace]
  refine ⟨37225251927457408717671329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24816834618304939145114219 37225251927457408717671329)
  ·
    refine ⟨27918938945593056538253497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37225251927457408717671329 27918938945593056538253497)
    ·
      refine ⟨20939204209194792403690123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27918938945593056538253497 20939204209194792403690123)
      ·
        refine ⟨31408806313792188605535185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20939204209194792403690123 31408806313792188605535185)
        ·
          refine ⟨23556604735344141454151389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31408806313792188605535185 23556604735344141454151389)
          ·
            refine ⟨8833726775754053045306771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23556604735344141454151389 8833726775754053045306771)
            ·
              refine ⟨13250590163631079567960157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833726775754053045306771 13250590163631079567960157)
              ·
                refine ⟨4968971311361654837985059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13250590163631079567960157 4968971311361654837985059)
                ·
                  refine ⟨7453456967042482256977589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968971311361654837985059 7453456967042482256977589)
                  ·
                    refine ⟨698761590660232711591649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7453456967042482256977589 698761590660232711591649)
                    ·
                      refine ⟨524071192995174533693737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698761590660232711591649 524071192995174533693737)
                      ·
                        rfl

theorem cell23_1020625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_1020625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020625 prefixEnd_1020625 := by exact prefixLift 1020625
  have htrace : WordTrace (prefixWord ++ tailWord_1020625) baseStart_1020625 baseEnd_1020625 := by
    simpa [prefixWord, tailWord_1020625, baseEnd_1020625] using wordTrace_append hprefix tailTrace_1020625
  have hstable : (prefixWord ++ tailWord_1020625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020625).length < 2 ^ (prefixWord ++ tailWord_1020625).sum := by decide
  have hdescent : baseEnd_1020625 < baseStart_1020625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020626 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1020626 : Nat := 118140960795 + 1020626 * 2 ^ 59
def prefixEnd_1020626 : Nat := 4983230072969 + 3 ^ 40 * 1020626 * 2
def baseEnd_1020626 : Nat := 174690568825276343260411

theorem tailTrace_1020626 : CollatzResearch.WordTrace tailWord_1020626 prefixEnd_1020626 174690568825276343260411 := by
  unfold tailWord_1020626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306322100113446472114433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24816858933635857258971821 9306322100113446472114433)
  ·
    refine ⟨6979741575085084854085825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9306322100113446472114433 6979741575085084854085825)
    ·
      refine ⟨5234806181313813640564369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6979741575085084854085825 5234806181313813640564369)
      ·
        refine ⟨3926104635985360230423277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5234806181313813640564369 3926104635985360230423277)
        ·
          refine ⟨1472289238494510086408729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3926104635985360230423277 1472289238494510086408729)
          ·
            refine ⟨1104216928870882564806547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472289238494510086408729 1104216928870882564806547)
            ·
              refine ⟨1656325393306323847209821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104216928870882564806547 1656325393306323847209821)
              ·
                refine ⟨621122022489871442703683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1656325393306323847209821 621122022489871442703683)
                ·
                  refine ⟨931683033734807164055525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621122022489871442703683 931683033734807164055525)
                  ·
                    refine ⟨174690568825276343260411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931683033734807164055525 174690568825276343260411)
                    ·
                      rfl

theorem cell23_1020626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1020626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020626 prefixEnd_1020626 := by exact prefixLift 1020626
  have htrace : WordTrace (prefixWord ++ tailWord_1020626) baseStart_1020626 baseEnd_1020626 := by
    simpa [prefixWord, tailWord_1020626, baseEnd_1020626] using wordTrace_append hprefix tailTrace_1020626
  have hstable : (prefixWord ++ tailWord_1020626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020626).length < 2 ^ (prefixWord ++ tailWord_1020626).sum := by decide
  have hdescent : baseEnd_1020626 < baseStart_1020626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020695 : List Nat := [1, 1, 3, 4, 4, 10]
def baseStart_1020695 : Nat := 118140960795 + 1020695 * 2 ^ 59
def prefixEnd_1020695 : Nat := 4983230072969 + 3 ^ 40 * 1020695 * 2
def baseEnd_1020695 : Nat := 2156819492349750040405

theorem tailTrace_1020695 : CollatzResearch.WordTrace tailWord_1020695 prefixEnd_1020695 2156819492349750040405 := by
  unfold tailWord_1020695
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227805037203810672719539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24818536691469207115146359 37227805037203810672719539)
  ·
    refine ⟨55841707555805716009079309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37227805037203810672719539 55841707555805716009079309)
    ·
      refine ⟨20940640333427143503404741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55841707555805716009079309 20940640333427143503404741)
      ·
        refine ⟨3926370062517589406888389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20940640333427143503404741 3926370062517589406888389)
        ·
          refine ⟨736194386722048013791573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3926370062517589406888389 736194386722048013791573)
          ·
            refine ⟨2156819492349750040405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 736194386722048013791573 2156819492349750040405)
            ·
              rfl

theorem cell23_1020695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 10].length) (baseStart_1020695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020695 prefixEnd_1020695 := by exact prefixLift 1020695
  have htrace : WordTrace (prefixWord ++ tailWord_1020695) baseStart_1020695 baseEnd_1020695 := by
    simpa [prefixWord, tailWord_1020695, baseEnd_1020695] using wordTrace_append hprefix tailTrace_1020695
  have hstable : (prefixWord ++ tailWord_1020695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020695).length < 2 ^ (prefixWord ++ tailWord_1020695).sum := by decide
  have hdescent : baseEnd_1020695 < baseStart_1020695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020705 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1020705 : Nat := 118140960795 + 1020705 * 2 ^ 59
def prefixEnd_1020705 : Nat := 4983230072969 + 3 ^ 40 * 1020705 * 2
def baseEnd_1020705 : Nat := 524112271447534220693369

theorem tailTrace_1020705 : CollatzResearch.WordTrace tailWord_1020705 prefixEnd_1020705 524112271447534220693369 := by
  unfold tailWord_1020705
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228169767167582380583569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24818779844778388253722379 37228169767167582380583569)
  ·
    refine ⟨27921127325375686785437677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37228169767167582380583569 27921127325375686785437677)
    ·
      refine ⟨10470422747015882544539129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27921127325375686785437677 10470422747015882544539129)
      ·
        refine ⟨7852817060261911908404347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470422747015882544539129 7852817060261911908404347)
        ·
          refine ⟨11779225590392867862606521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852817060261911908404347 11779225590392867862606521)
          ·
            refine ⟨8834419192794650896954891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11779225590392867862606521 8834419192794650896954891)
            ·
              refine ⟨13251628789191976345432337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834419192794650896954891 13251628789191976345432337)
              ·
                refine ⟨9938721591893982259074253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13251628789191976345432337 9938721591893982259074253)
                ·
                  refine ⟨3727020596960243347152845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9938721591893982259074253 3727020596960243347152845)
                  ·
                    refine ⟨1397632723860091255182317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727020596960243347152845 1397632723860091255182317)
                    ·
                      refine ⟨524112271447534220693369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397632723860091255182317 524112271447534220693369)
                      ·
                        rfl

theorem cell23_1020705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1020705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020705 prefixEnd_1020705 := by exact prefixLift 1020705
  have htrace : WordTrace (prefixWord ++ tailWord_1020705) baseStart_1020705 baseEnd_1020705 := by
    simpa [prefixWord, tailWord_1020705, baseEnd_1020705] using wordTrace_append hprefix tailTrace_1020705
  have hstable : (prefixWord ++ tailWord_1020705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020705).length < 2 ^ (prefixWord ++ tailWord_1020705).sum := by decide
  have hdescent : baseEnd_1020705 < baseStart_1020705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020715 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 7, 2]
def baseStart_1020715 : Nat := 118140960795 + 1020715 * 2 ^ 59
def prefixEnd_1020715 : Nat := 4983230072969 + 3 ^ 40 * 1020715 * 2
def baseEnd_1020715 : Nat := 524117406254079181568323

theorem tailTrace_1020715 : CollatzResearch.WordTrace tailWord_1020715 prefixEnd_1020715 524117406254079181568323 := by
  unfold tailWord_1020715
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228534497131354088447599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24819022998087569392298399 37228534497131354088447599)
  ·
    refine ⟨55842801745697031132671399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37228534497131354088447599 55842801745697031132671399)
    ·
      refine ⟨83764202618545546699007099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55842801745697031132671399 83764202618545546699007099)
      ·
        refine ⟨125646303927818320048510649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83764202618545546699007099 125646303927818320048510649)
        ·
          refine ⟨94234727945863740036382987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125646303927818320048510649 94234727945863740036382987)
          ·
            refine ⟨141352091918795610054574481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94234727945863740036382987 141352091918795610054574481)
            ·
              refine ⟨106014068939096707540930861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141352091918795610054574481 106014068939096707540930861)
              ·
                refine ⟨39755275852161265327849073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106014068939096707540930861 39755275852161265327849073)
                ·
                  refine ⟨29816456889120948995886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39755275852161265327849073 29816456889120948995886805)
                  ·
                    refine ⟨698823208338772242091097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29816456889120948995886805 698823208338772242091097)
                    ·
                      refine ⟨524117406254079181568323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698823208338772242091097 524117406254079181568323)
                      ·
                        rfl

theorem cell23_1020715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7, 2].length) (baseStart_1020715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020715 prefixEnd_1020715 := by exact prefixLift 1020715
  have htrace : WordTrace (prefixWord ++ tailWord_1020715) baseStart_1020715 baseEnd_1020715 := by
    simpa [prefixWord, tailWord_1020715, baseEnd_1020715] using wordTrace_append hprefix tailTrace_1020715
  have hstable : (prefixWord ++ tailWord_1020715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020715).length < 2 ^ (prefixWord ++ tailWord_1020715).sum := by decide
  have hdescent : baseEnd_1020715 < baseStart_1020715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020722 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1020722 : Nat := 118140960795 + 1020722 * 2 ^ 59
def prefixEnd_1020722 : Nat := 4983230072969 + 3 ^ 40 * 1020722 * 2
def baseEnd_1020722 : Nat := 524121000618660654180791

theorem tailTrace_1020722 : CollatzResearch.WordTrace tailWord_1020722 prefixEnd_1020722 524121000618660654180791 := by
  unfold tailWord_1020722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9307197452026498570988105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24819193205403996189301613 9307197452026498570988105)
  ·
    refine ⟨6980398089019873928241079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9307197452026498570988105 6980398089019873928241079)
    ·
      refine ⟨10470597133529810892361619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980398089019873928241079 10470597133529810892361619)
      ·
        refine ⟨15705895700294716338542429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10470597133529810892361619 15705895700294716338542429)
        ·
          refine ⟨5889710887610518626953411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15705895700294716338542429 5889710887610518626953411)
          ·
            refine ⟨8834566331415777940430117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889710887610518626953411 8834566331415777940430117)
            ·
              refine ⟨1656481187140458363830647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8834566331415777940430117 1656481187140458363830647)
              ·
                refine ⟨2484721780710687545745971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656481187140458363830647 2484721780710687545745971)
                ·
                  refine ⟨3727082671066031318618957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484721780710687545745971 3727082671066031318618957)
                  ·
                    refine ⟨1397656001649761744482109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727082671066031318618957 1397656001649761744482109)
                    ·
                      refine ⟨524121000618660654180791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397656001649761744482109 524121000618660654180791)
                      ·
                        rfl

theorem cell23_1020722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1020722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020722 prefixEnd_1020722 := by exact prefixLift 1020722
  have htrace : WordTrace (prefixWord ++ tailWord_1020722) baseStart_1020722 baseEnd_1020722 := by
    simpa [prefixWord, tailWord_1020722, baseEnd_1020722] using wordTrace_append hprefix tailTrace_1020722
  have hstable : (prefixWord ++ tailWord_1020722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020722).length < 2 ^ (prefixWord ++ tailWord_1020722).sum := by decide
  have hdescent : baseEnd_1020722 < baseStart_1020722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020740 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1020740 : Nat := 118140960795 + 1020740 * 2 ^ 59
def prefixEnd_1020740 : Nat := 4983230072969 + 3 ^ 40 * 1020740 * 2
def baseEnd_1020740 : Nat := 524130243270441583755709

theorem tailTrace_1020740 : CollatzResearch.WordTrace tailWord_1020740 prefixEnd_1020740 524130243270441583755709 := by
  unfold tailWord_1020740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614723161020391679053837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24819630881360522238738449 18614723161020391679053837)
  ·
    refine ⟨6980521185382646879645189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18614723161020391679053837 6980521185382646879645189)
    ·
      refine ⟨1308847722259246289933473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6980521185382646879645189 1308847722259246289933473)
      ·
        refine ⟨981635791694434717450105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1308847722259246289933473 981635791694434717450105)
        ·
          refine ⟨736226843770826038087579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981635791694434717450105 736226843770826038087579)
          ·
            refine ⟨1104340265656239057131369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736226843770826038087579 1104340265656239057131369)
            ·
              refine ⟨828255199242179292848527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104340265656239057131369 828255199242179292848527)
              ·
                refine ⟨1242382798863268939272791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828255199242179292848527 1242382798863268939272791)
                ·
                  refine ⟨1863574198294903408909187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242382798863268939272791 1863574198294903408909187)
                  ·
                    refine ⟨2795361297442355113363781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863574198294903408909187 2795361297442355113363781)
                    ·
                      refine ⟨524130243270441583755709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2795361297442355113363781 524130243270441583755709)
                      ·
                        rfl

theorem cell23_1020740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1020740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020740 prefixEnd_1020740 := by exact prefixLift 1020740
  have htrace : WordTrace (prefixWord ++ tailWord_1020740) baseStart_1020740 baseEnd_1020740 := by
    simpa [prefixWord, tailWord_1020740, baseEnd_1020740] using wordTrace_append hprefix tailTrace_1020740
  have hstable : (prefixWord ++ tailWord_1020740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020740).length < 2 ^ (prefixWord ++ tailWord_1020740).sum := by decide
  have hdescent : baseEnd_1020740 < baseStart_1020740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020779 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 2, 2, 2]
def baseStart_1020779 : Nat := 118140960795 + 1020779 * 2 ^ 59
def prefixEnd_1020779 : Nat := 4983230072969 + 3 ^ 40 * 1020779 * 2
def baseEnd_1020779 : Nat := 524150269015966931168029

theorem tailTrace_1020779 : CollatzResearch.WordTrace tailWord_1020779 prefixEnd_1020779 524150269015966931168029 := by
  unfold tailWord_1020779
  simp only [CollatzResearch.WordTrace]
  refine ⟨37230868768899493018777391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24820579179266328679184927 37230868768899493018777391)
  ·
    refine ⟨55846303153349239528166087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37230868768899493018777391 55846303153349239528166087)
    ·
      refine ⟨83769454730023859292249131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55846303153349239528166087 83769454730023859292249131)
      ·
        refine ⟨125654182095035788938373697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83769454730023859292249131 125654182095035788938373697)
        ·
          refine ⟨94240636571276841703780273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125654182095035788938373697 94240636571276841703780273)
          ·
            refine ⟨70680477428457631277835205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94240636571276841703780273 70680477428457631277835205)
            ·
              refine ⟨13252589517835805864594101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70680477428457631277835205 13252589517835805864594101)
              ·
                refine ⟨1242430267297106799805697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13252589517835805864594101 1242430267297106799805697)
                ·
                  refine ⟨931822700472830099854273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242430267297106799805697 931822700472830099854273)
                  ·
                    refine ⟨698867025354622574890705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 931822700472830099854273 698867025354622574890705)
                    ·
                      refine ⟨524150269015966931168029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698867025354622574890705 524150269015966931168029)
                      ·
                        rfl

theorem cell23_1020779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2, 2].length) (baseStart_1020779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020779 prefixEnd_1020779 := by exact prefixLift 1020779
  have htrace : WordTrace (prefixWord ++ tailWord_1020779) baseStart_1020779 baseEnd_1020779 := by
    simpa [prefixWord, tailWord_1020779, baseEnd_1020779] using wordTrace_append hprefix tailTrace_1020779
  have hstable : (prefixWord ++ tailWord_1020779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020779).length < 2 ^ (prefixWord ++ tailWord_1020779).sum := by decide
  have hdescent : baseEnd_1020779 < baseStart_1020779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020785 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 7]
def baseStart_1020785 : Nat := 118140960795 + 1020785 * 2 ^ 59
def prefixEnd_1020785 : Nat := 4983230072969 + 3 ^ 40 * 1020785 * 2
def baseEnd_1020785 : Nat := 58239261099988211965889

theorem tailTrace_1020785 : CollatzResearch.WordTrace tailWord_1020785 prefixEnd_1020785 58239261099988211965889 := by
  unfold tailWord_1020785
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231087606877756043495809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24820725071251837362330539 37231087606877756043495809)
  ·
    refine ⟨27923315705158317032621857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37231087606877756043495809 27923315705158317032621857)
    ·
      refine ⟨20942486778868737774466393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27923315705158317032621857 20942486778868737774466393)
      ·
        refine ⟨15706865084151553330849795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20942486778868737774466393 15706865084151553330849795)
        ·
          refine ⟨23560297626227329996274693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15706865084151553330849795 23560297626227329996274693)
          ·
            refine ⟨4417555804917624374301505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23560297626227329996274693 4417555804917624374301505)
            ·
              refine ⟨3313166853688218280726129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417555804917624374301505 3313166853688218280726129)
              ·
                refine ⟨2484875140266163710544597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313166853688218280726129 2484875140266163710544597)
                ·
                  refine ⟨58239261099988211965889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2484875140266163710544597 58239261099988211965889)
                  ·
                    rfl

theorem cell23_1020785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_1020785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020785 prefixEnd_1020785 := by exact prefixLift 1020785
  have htrace : WordTrace (prefixWord ++ tailWord_1020785) baseStart_1020785 baseEnd_1020785 := by
    simpa [prefixWord, tailWord_1020785, baseEnd_1020785] using wordTrace_append hprefix tailTrace_1020785
  have hstable : (prefixWord ++ tailWord_1020785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020785).length < 2 ^ (prefixWord ++ tailWord_1020785).sum := by decide
  have hdescent : baseEnd_1020785 < baseStart_1020785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020795 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3]
def baseStart_1020795 : Nat := 118140960795 + 1020795 * 2 ^ 59
def prefixEnd_1020795 : Nat := 4983230072969 + 3 ^ 40 * 1020795 * 2
def baseEnd_1020795 : Nat := 524158484706438868567955

theorem tailTrace_1020795 : CollatzResearch.WordTrace tailWord_1020795 prefixEnd_1020795 524158484706438868567955 := by
  unfold tailWord_1020795
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231452336841527751359839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24820968224561018500906559 37231452336841527751359839)
  ·
    refine ⟨55847178505262291627039759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37231452336841527751359839 55847178505262291627039759)
    ·
      refine ⟨83770767757893437440559639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55847178505262291627039759 83770767757893437440559639)
      ·
        refine ⟨125656151636840156160839459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83770767757893437440559639 125656151636840156160839459)
        ·
          refine ⟨188484227455260234241259189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125656151636840156160839459 188484227455260234241259189)
          ·
            refine ⟨17670396323930646960118049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188484227455260234241259189 17670396323930646960118049)
            ·
              refine ⟨13252797242947985220088537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670396323930646960118049 13252797242947985220088537)
              ·
                refine ⟨9939597932210988915066403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252797242947985220088537 9939597932210988915066403)
                ·
                  refine ⟨14909396898316483372599605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939597932210988915066403 14909396898316483372599605)
                  ·
                    refine ⟨1397755959217170316181213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909396898316483372599605 1397755959217170316181213)
                    ·
                      refine ⟨524158484706438868567955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397755959217170316181213 524158484706438868567955)
                      ·
                        rfl

theorem cell23_1020795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3].length) (baseStart_1020795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020795 prefixEnd_1020795 := by exact prefixLift 1020795
  have htrace : WordTrace (prefixWord ++ tailWord_1020795) baseStart_1020795 baseEnd_1020795 := by
    simpa [prefixWord, tailWord_1020795, baseEnd_1020795] using wordTrace_append hprefix tailTrace_1020795
  have hstable : (prefixWord ++ tailWord_1020795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020795).length < 2 ^ (prefixWord ++ tailWord_1020795).sum := by decide
  have hdescent : baseEnd_1020795 < baseStart_1020795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020835 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1020835 : Nat := 118140960795 + 1020835 * 2 ^ 59
def prefixEnd_1020835 : Nat := 4983230072969 + 3 ^ 40 * 1020835 * 2
def baseEnd_1020835 : Nat := 524179023932618712067771

theorem tailTrace_1020835 : CollatzResearch.WordTrace tailWord_1020835 prefixEnd_1020835 524179023932618712067771 := by
  unfold tailWord_1020835
  simp only [CollatzResearch.WordTrace]
  refine ⟨37232911256696614582815959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24821940837797743055210639 37232911256696614582815959)
  ·
    refine ⟨55849366885044921874223939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37232911256696614582815959 55849366885044921874223939)
    ·
      refine ⟨83774050327567382811335909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55849366885044921874223939 83774050327567382811335909)
      ·
        refine ⟨15707634436418884277125483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83774050327567382811335909 15707634436418884277125483)
        ·
          refine ⟨23561451654628326415688225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707634436418884277125483 23561451654628326415688225)
          ·
            refine ⟨17671088740971244811766169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23561451654628326415688225 17671088740971244811766169)
            ·
              refine ⟨13253316555728433608824627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17671088740971244811766169 13253316555728433608824627)
              ·
                refine ⟨19879974833592650413236941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253316555728433608824627 19879974833592650413236941)
                ·
                  refine ⟨7454990562597243904963853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19879974833592650413236941 7454990562597243904963853)
                  ·
                    refine ⟨2795621460973966464361445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7454990562597243904963853 2795621460973966464361445)
                    ·
                      refine ⟨524179023932618712067771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2795621460973966464361445 524179023932618712067771)
                      ·
                        rfl

theorem cell23_1020835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1020835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020835 prefixEnd_1020835 := by exact prefixLift 1020835
  have htrace : WordTrace (prefixWord ++ tailWord_1020835) baseStart_1020835 baseEnd_1020835 := by
    simpa [prefixWord, tailWord_1020835, baseEnd_1020835] using wordTrace_append hprefix tailTrace_1020835
  have hstable : (prefixWord ++ tailWord_1020835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020835).length < 2 ^ (prefixWord ++ tailWord_1020835).sum := by decide
  have hdescent : baseEnd_1020835 < baseStart_1020835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020849 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_1020849 : Nat := 118140960795 + 1020849 * 2 ^ 59
def prefixEnd_1020849 : Nat := 4983230072969 + 3 ^ 40 * 1020849 * 2
def baseEnd_1020849 : Nat := 174728737553927219097569

theorem tailTrace_1020849 : CollatzResearch.WordTrace tailWord_1020849 prefixEnd_1020849 174728737553927219097569 := by
  unfold tailWord_1020849
  simp only [CollatzResearch.WordTrace]
  refine ⟨37233421878645894973825601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24822281252430596649217067 37233421878645894973825601)
  ·
    refine ⟨27925066408984421230369201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37233421878645894973825601 27925066408984421230369201)
    ·
      refine ⟨20943799806738315922776901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27925066408984421230369201 20943799806738315922776901)
      ·
        refine ⟨3926962463763434235520669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20943799806738315922776901 3926962463763434235520669)
        ·
          refine ⟨1472610923911287838320251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3926962463763434235520669 1472610923911287838320251)
          ·
            refine ⟨2208916385866931757480377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472610923911287838320251 2208916385866931757480377)
            ·
              refine ⟨1656687289400198818110283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208916385866931757480377 1656687289400198818110283)
              ·
                refine ⟨2485030934100298227165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656687289400198818110283 2485030934100298227165425)
                ·
                  refine ⟨1863773200575223670374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485030934100298227165425 1863773200575223670374069)
                  ·
                    refine ⟨174728737553927219097569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1863773200575223670374069 174728737553927219097569)
                    ·
                      rfl

theorem cell23_1020849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_1020849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020849 prefixEnd_1020849 := by exact prefixLift 1020849
  have htrace : WordTrace (prefixWord ++ tailWord_1020849) baseStart_1020849 baseEnd_1020849 := by
    simpa [prefixWord, tailWord_1020849, baseEnd_1020849] using wordTrace_append hprefix tailTrace_1020849
  have hstable : (prefixWord ++ tailWord_1020849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020849).length < 2 ^ (prefixWord ++ tailWord_1020849).sum := by decide
  have hdescent : baseEnd_1020849 < baseStart_1020849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020886 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1020886 : Nat := 118140960795 + 1020886 * 2 ^ 59
def prefixEnd_1020886 : Nat := 4983230072969 + 3 ^ 40 * 1020886 * 2
def baseEnd_1020886 : Nat := 524205211445998012530037

theorem tailTrace_1020886 : CollatzResearch.WordTrace tailWord_1020886 prefixEnd_1020886 524205211445998012530037 := by
  unfold tailWord_1020886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327173211219490643307657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24823180919674566861948341 2327173211219490643307657)
  ·
    refine ⟨1745379908414617982480743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2327173211219490643307657 1745379908414617982480743)
    ·
      refine ⟨2618069862621926973721115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745379908414617982480743 2618069862621926973721115)
      ·
        refine ⟨3927104793932890460581673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618069862621926973721115 3927104793932890460581673)
        ·
          refine ⟨2945328595449667845436255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927104793932890460581673 2945328595449667845436255)
          ·
            refine ⟨4417992893174501768154383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945328595449667845436255 4417992893174501768154383)
            ·
              refine ⟨6626989339761752652231575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417992893174501768154383 6626989339761752652231575)
              ·
                refine ⟨9940484009642628978347363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626989339761752652231575 9940484009642628978347363)
                ·
                  refine ⟨14910726014463943467521045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940484009642628978347363 14910726014463943467521045)
                  ·
                    refine ⟨698940281927997350040049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14910726014463943467521045 698940281927997350040049)
                    ·
                      refine ⟨524205211445998012530037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 698940281927997350040049 524205211445998012530037)
                      ·
                        rfl

theorem cell23_1020886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1020886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020886 prefixEnd_1020886 := by exact prefixLift 1020886
  have htrace : WordTrace (prefixWord ++ tailWord_1020886) baseStart_1020886 baseEnd_1020886 := by
    simpa [prefixWord, tailWord_1020886, baseEnd_1020886] using wordTrace_append hprefix tailTrace_1020886
  have hstable : (prefixWord ++ tailWord_1020886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020886).length < 2 ^ (prefixWord ++ tailWord_1020886).sum := by decide
  have hdescent : baseEnd_1020886 < baseStart_1020886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020906 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1020906 : Nat := 118140960795 + 1020906 * 2 ^ 59
def prefixEnd_1020906 : Nat := 4983230072969 + 3 ^ 40 * 1020906 * 2
def baseEnd_1020906 : Nat := 524215481059087934279945

theorem tailTrace_1020906 : CollatzResearch.WordTrace tailWord_1020906 prefixEnd_1020906 524215481059087934279945 := by
  unfold tailWord_1020906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308875209859848427162643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24823667226292929139100381 9308875209859848427162643)
  ·
    refine ⟨13963312814789772640743965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9308875209859848427162643 13963312814789772640743965)
    ·
      refine ⟨5236242305546164740278987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13963312814789772640743965 5236242305546164740278987)
      ·
        refine ⟨7854363458319247110418481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236242305546164740278987 7854363458319247110418481)
        ·
          refine ⟨5890772593739435332813861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7854363458319247110418481 5890772593739435332813861)
          ·
            refine ⟨1104519861326144124902599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5890772593739435332813861 1104519861326144124902599)
            ·
              refine ⟨1656779791989216187353899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104519861326144124902599 1656779791989216187353899)
              ·
                refine ⟨2485169687983824281030849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656779791989216187353899 2485169687983824281030849)
                ·
                  refine ⟨1863877265987868210773137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485169687983824281030849 1863877265987868210773137)
                  ·
                    refine ⟨1397907949490901158079853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863877265987868210773137 1397907949490901158079853)
                    ·
                      refine ⟨524215481059087934279945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397907949490901158079853 524215481059087934279945)
                      ·
                        rfl

theorem cell23_1020906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1020906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020906 prefixEnd_1020906 := by exact prefixLift 1020906
  have htrace : WordTrace (prefixWord ++ tailWord_1020906) baseStart_1020906 baseEnd_1020906 := by
    simpa [prefixWord, tailWord_1020906, baseEnd_1020906] using wordTrace_append hprefix tailTrace_1020906
  have hstable : (prefixWord ++ tailWord_1020906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020906).length < 2 ^ (prefixWord ++ tailWord_1020906).sum := by decide
  have hdescent : baseEnd_1020906 < baseStart_1020906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020915 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1020915 : Nat := 118140960795 + 1020915 * 2 ^ 59
def prefixEnd_1020915 : Nat := 4983230072969 + 3 ^ 40 * 1020915 * 2
def baseEnd_1020915 : Nat := 524220102384978399067403

theorem tailTrace_1020915 : CollatzResearch.WordTrace tailWord_1020915 prefixEnd_1020915 524220102384978399067403 := by
  unfold tailWord_1020915
  simp only [CollatzResearch.WordTrace]
  refine ⟨37235829096406788245728199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24823886064271192163818799 37235829096406788245728199)
  ·
    refine ⟨55853743644610182368592299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37235829096406788245728199 55853743644610182368592299)
    ·
      refine ⟨83780615466915273552888449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55853743644610182368592299 83780615466915273552888449)
      ·
        refine ⟨62835461600186455164666337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83780615466915273552888449 62835461600186455164666337)
        ·
          refine ⟨47126596200139841373499753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62835461600186455164666337 47126596200139841373499753)
          ·
            refine ⟨35344947150104881030124815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47126596200139841373499753 35344947150104881030124815)
            ·
              refine ⟨53017420725157321545187223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35344947150104881030124815 53017420725157321545187223)
              ·
                refine ⟨79526131087735982317780835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53017420725157321545187223 79526131087735982317780835)
                ·
                  refine ⟨119289196631603973476671253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79526131087735982317780835 119289196631603973476671253)
                  ·
                    refine ⟨5591681092106436256718965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119289196631603973476671253 5591681092106436256718965)
                    ·
                      refine ⟨524220102384978399067403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5591681092106436256718965 524220102384978399067403)
                      ·
                        rfl

theorem cell23_1020915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1020915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020915 prefixEnd_1020915 := by exact prefixLift 1020915
  have htrace : WordTrace (prefixWord ++ tailWord_1020915) baseStart_1020915 baseEnd_1020915 := by
    simpa [prefixWord, tailWord_1020915, baseEnd_1020915] using wordTrace_append hprefix tailTrace_1020915
  have hstable : (prefixWord ++ tailWord_1020915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020915).length < 2 ^ (prefixWord ++ tailWord_1020915).sum := by decide
  have hdescent : baseEnd_1020915 < baseStart_1020915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020936 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_1020936 : Nat := 118140960795 + 1020936 * 2 ^ 59
def prefixEnd_1020936 : Nat := 4983230072969 + 3 ^ 40 * 1020936 * 2
def baseEnd_1020936 : Nat := 524230885478722816904807

theorem tailTrace_1020936 : CollatzResearch.WordTrace tailWord_1020936 prefixEnd_1020936 524230885478722816904807 := by
  unfold tailWord_1020936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618297514665354416121331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24824396686220472554828441 18618297514665354416121331)
  ·
    refine ⟨27927446271998031624181997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18618297514665354416121331 27927446271998031624181997)
    ·
      refine ⟨10472792351999261859068249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27927446271998031624181997 10472792351999261859068249)
      ·
        refine ⟨7854594263999446394301187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10472792351999261859068249 7854594263999446394301187)
        ·
          refine ⟨11781891395999169591451781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854594263999446394301187 11781891395999169591451781)
          ·
            refine ⟨2209104636749844298397209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11781891395999169591451781 2209104636749844298397209)
            ·
              refine ⟨1656828477562383223797907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209104636749844298397209 1656828477562383223797907)
              ·
                refine ⟨2485242716343574835696861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656828477562383223797907 2485242716343574835696861)
                ·
                  refine ⟨931966018628840563386323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2485242716343574835696861 931966018628840563386323)
                  ·
                    refine ⟨1397949027943260845079485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931966018628840563386323 1397949027943260845079485)
                    ·
                      refine ⟨524230885478722816904807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1397949027943260845079485 524230885478722816904807)
                      ·
                        rfl

theorem cell23_1020936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_1020936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020936 prefixEnd_1020936 := by exact prefixLift 1020936
  have htrace : WordTrace (prefixWord ++ tailWord_1020936) baseStart_1020936 baseEnd_1020936 := by
    simpa [prefixWord, tailWord_1020936, baseEnd_1020936] using wordTrace_append hprefix tailTrace_1020936
  have hstable : (prefixWord ++ tailWord_1020936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020936).length < 2 ^ (prefixWord ++ tailWord_1020936).sum := by decide
  have hdescent : baseEnd_1020936 < baseStart_1020936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020956 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1020956 : Nat := 118140960795 + 1020956 * 2 ^ 59
def prefixEnd_1020956 : Nat := 4983230072969 + 3 ^ 40 * 1020956 * 2
def baseEnd_1020956 : Nat := 174747051697270912884905

theorem tailTrace_1020956 : CollatzResearch.WordTrace tailWord_1020956 prefixEnd_1020956 174747051697270912884905 := by
  unfold tailWord_1020956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618662244629126123985361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24824882992838834831980481 18618662244629126123985361)
  ·
    refine ⟨13963996683471844592989021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18618662244629126123985361 13963996683471844592989021)
    ·
      refine ⟨5236498756301941722370883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13963996683471844592989021 5236498756301941722370883)
      ·
        refine ⟨7854748134452912583556325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236498756301941722370883 7854748134452912583556325)
        ·
          refine ⟨1472765275209921109416811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7854748134452912583556325 1472765275209921109416811)
          ·
            refine ⟨2209147912814881664125217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472765275209921109416811 2209147912814881664125217)
            ·
              refine ⟨1656860934611161248093913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209147912814881664125217 1656860934611161248093913)
              ·
                refine ⟨1242645700958370936070435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656860934611161248093913 1242645700958370936070435)
                ·
                  refine ⟨1863968551437556404105653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242645700958370936070435 1863968551437556404105653)
                  ·
                    refine ⟨174747051697270912884905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1863968551437556404105653 174747051697270912884905)
                    ·
                      rfl

theorem cell23_1020956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1020956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020956 prefixEnd_1020956 := by exact prefixLift 1020956
  have htrace : WordTrace (prefixWord ++ tailWord_1020956) baseStart_1020956 baseEnd_1020956 := by
    simpa [prefixWord, tailWord_1020956, baseEnd_1020956] using wordTrace_append hprefix tailTrace_1020956
  have hstable : (prefixWord ++ tailWord_1020956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020956).length < 2 ^ (prefixWord ++ tailWord_1020956).sum := by decide
  have hdescent : baseEnd_1020956 < baseStart_1020956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020959 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_1020959 : Nat := 118140960795 + 1020959 * 2 ^ 59
def prefixEnd_1020959 : Nat := 4983230072969 + 3 ^ 40 * 1020959 * 2
def baseEnd_1020959 : Nat := 524242695533776226917201

theorem tailTrace_1020959 : CollatzResearch.WordTrace tailWord_1020959 prefixEnd_1020959 524242695533776226917201 := by
  unfold tailWord_1020959
  simp only [CollatzResearch.WordTrace]
  refine ⟨37237433908247383760329931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24824955938831589173553287 37237433908247383760329931)
  ·
    refine ⟨55856150862371075640494897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37237433908247383760329931 55856150862371075640494897)
    ·
      refine ⟨41892113146778306730371173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55856150862371075640494897 41892113146778306730371173)
      ·
        refine ⟨7854771215020932511944595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41892113146778306730371173 7854771215020932511944595)
        ·
          refine ⟨11782156822531398767916893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854771215020932511944595 11782156822531398767916893)
          ·
            refine ⟨4418308808449274537968835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11782156822531398767916893 4418308808449274537968835)
            ·
              refine ⟨6627463212673911806953253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418308808449274537968835 6627463212673911806953253)
              ·
                refine ⟨1242649352376358463803735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6627463212673911806953253 1242649352376358463803735)
                ·
                  refine ⟨1863974028564537695705603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242649352376358463803735 1863974028564537695705603)
                  ·
                    refine ⟨2795961042846806543558405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863974028564537695705603 2795961042846806543558405)
                    ·
                      refine ⟨524242695533776226917201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2795961042846806543558405 524242695533776226917201)
                      ·
                        rfl

theorem cell23_1020959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_1020959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020959 prefixEnd_1020959 := by exact prefixLift 1020959
  have htrace : WordTrace (prefixWord ++ tailWord_1020959) baseStart_1020959 baseEnd_1020959 := by
    simpa [prefixWord, tailWord_1020959, baseEnd_1020959] using wordTrace_append hprefix tailTrace_1020959
  have hstable : (prefixWord ++ tailWord_1020959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020959).length < 2 ^ (prefixWord ++ tailWord_1020959).sum := by decide
  have hdescent : baseEnd_1020959 < baseStart_1020959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020972 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_1020972 : Nat := 118140960795 + 1020972 * 2 ^ 59
def prefixEnd_1020972 : Nat := 4983230072969 + 3 ^ 40 * 1020972 * 2
def baseEnd_1020972 : Nat := 524249370782284676054641

theorem tailTrace_1020972 : CollatzResearch.WordTrace tailWord_1020972 prefixEnd_1020972 524249370782284676054641 := by
  unfold tailWord_1020972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618954028600143490276585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24825272038133524653702113 18618954028600143490276585)
  ·
    refine ⟨13964215521450107617707439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18618954028600143490276585 13964215521450107617707439)
    ·
      refine ⟨20946323282175161426561159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13964215521450107617707439 20946323282175161426561159)
      ·
        refine ⟨31419484923262742139841739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20946323282175161426561159 31419484923262742139841739)
        ·
          refine ⟨47129227384894113209762609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31419484923262742139841739 47129227384894113209762609)
          ·
            refine ⟨35346920538670584907321957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47129227384894113209762609 35346920538670584907321957)
            ·
              refine ⟨6627547601000734670122867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35346920538670584907321957 6627547601000734670122867)
              ·
                refine ⟨9941321401501102005184301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627547601000734670122867 9941321401501102005184301)
                ·
                  refine ⟨3727995525562913251944113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9941321401501102005184301 3727995525562913251944113)
                  ·
                    refine ⟨2795996644172184938958085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3727995525562913251944113 2795996644172184938958085)
                    ·
                      refine ⟨524249370782284676054641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2795996644172184938958085 524249370782284676054641)
                      ·
                        rfl

theorem cell23_1020972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_1020972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1020972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1020972 prefixEnd_1020972 := by exact prefixLift 1020972
  have htrace : WordTrace (prefixWord ++ tailWord_1020972) baseStart_1020972 baseEnd_1020972 := by
    simpa [prefixWord, tailWord_1020972, baseEnd_1020972] using wordTrace_append hprefix tailTrace_1020972
  have hstable : (prefixWord ++ tailWord_1020972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020972).length < 2 ^ (prefixWord ++ tailWord_1020972).sum := by decide
  have hdescent : baseEnd_1020972 < baseStart_1020972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021026 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1021026 : Nat := 118140960795 + 1021026 * 2 ^ 59
def prefixEnd_1021026 : Nat := 4983230072969 + 3 ^ 40 * 1021026 * 2
def baseEnd_1021026 : Nat := 524277098737627464779393

theorem tailTrace_1021026 : CollatzResearch.WordTrace tailWord_1021026 prefixEnd_1021026 524277098737627464779393 := by
  unfold tailWord_1021026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309969399751163550754733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24826585066003102802012621 9309969399751163550754733)
  ·
    refine ⟨3491238524906686331533025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9309969399751163550754733 3491238524906686331533025)
    ·
      refine ⟨2618428893680014748649769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3491238524906686331533025 2618428893680014748649769)
      ·
        refine ⟨1963821670260011061487327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2618428893680014748649769 1963821670260011061487327)
        ·
          refine ⟨2945732505390016592230991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963821670260011061487327 2945732505390016592230991)
          ·
            refine ⟨4418598758085024888346487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945732505390016592230991 4418598758085024888346487)
            ·
              refine ⟨6627898137127537332519731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418598758085024888346487 6627898137127537332519731)
              ·
                refine ⟨9941847205691305998779597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627898137127537332519731 9941847205691305998779597)
                ·
                  refine ⟨3728192702134239749542349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9941847205691305998779597 3728192702134239749542349)
                  ·
                    refine ⟨1398072263300339906078381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728192702134239749542349 1398072263300339906078381)
                    ·
                      refine ⟨524277098737627464779393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1398072263300339906078381 524277098737627464779393)
                      ·
                        rfl

theorem cell23_1021026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1021026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021026 prefixEnd_1021026 := by exact prefixLift 1021026
  have htrace : WordTrace (prefixWord ++ tailWord_1021026) baseStart_1021026 baseEnd_1021026 := by
    simpa [prefixWord, tailWord_1021026, baseEnd_1021026] using wordTrace_append hprefix tailTrace_1021026
  have hstable : (prefixWord ++ tailWord_1021026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021026).length < 2 ^ (prefixWord ++ tailWord_1021026).sum := by decide
  have hdescent : baseEnd_1021026 < baseStart_1021026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021087 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1021087 : Nat := 118140960795 + 1021087 * 2 ^ 59
def prefixEnd_1021087 : Nat := 4983230072969 + 3 ^ 40 * 1021087 * 2
def baseEnd_1021087 : Nat := 524308421057551726116613

theorem tailTrace_1021087 : CollatzResearch.WordTrace tailWord_1021087 prefixEnd_1021087 524308421057551726116613 := by
  unfold tailWord_1021087
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242102451783661620989515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24828068301189107747326343 37242102451783661620989515)
  ·
    refine ⟨55863153677675492431484273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37242102451783661620989515 55863153677675492431484273)
    ·
      refine ⟨41897365258256619323613205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55863153677675492431484273 41897365258256619323613205)
      ·
        refine ⟨1963938996480779030794369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41897365258256619323613205 1963938996480779030794369)
        ·
          refine ⟨1472954247360584273095777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1963938996480779030794369 1472954247360584273095777)
          ·
            refine ⟨1104715685520438204821833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472954247360584273095777 1104715685520438204821833)
            ·
              refine ⟨828536764140328653616375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104715685520438204821833 828536764140328653616375)
              ·
                refine ⟨1242805146210492980424563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828536764140328653616375 1242805146210492980424563)
                ·
                  refine ⟨1864207719315739470636845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242805146210492980424563 1864207719315739470636845)
                  ·
                    refine ⟨699077894743402301488817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864207719315739470636845 699077894743402301488817)
                    ·
                      refine ⟨524308421057551726116613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699077894743402301488817 524308421057551726116613)
                      ·
                        rfl

theorem cell23_1021087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1021087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021087 prefixEnd_1021087 := by exact prefixLift 1021087
  have htrace : WordTrace (prefixWord ++ tailWord_1021087) baseStart_1021087 baseEnd_1021087 := by
    simpa [prefixWord, tailWord_1021087, baseEnd_1021087] using wordTrace_append hprefix tailTrace_1021087
  have hstable : (prefixWord ++ tailWord_1021087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021087).length < 2 ^ (prefixWord ++ tailWord_1021087).sum := by decide
  have hdescent : baseEnd_1021087 < baseStart_1021087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021106 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_1021106 : Nat := 118140960795 + 1021106 * 2 ^ 59
def prefixEnd_1021106 : Nat := 4983230072969 + 3 ^ 40 * 1021106 * 2
def baseEnd_1021106 : Nat := 58257575243331905753225

theorem tailTrace_1021106 : CollatzResearch.WordTrace tailWord_1021106 prefixEnd_1021106 58257575243331905753225 := by
  unfold tailWord_1021106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310698859678706966482793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24828530292476551910620781 9310698859678706966482793)
  ·
    refine ⟨6983024144759030224862095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9310698859678706966482793 6983024144759030224862095)
    ·
      refine ⟨10474536217138545337293143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983024144759030224862095 10474536217138545337293143)
      ·
        refine ⟨15711804325707818005939715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474536217138545337293143 15711804325707818005939715)
        ·
          refine ⟨23567706488561727008909573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15711804325707818005939715 23567706488561727008909573)
          ·
            refine ⟨4418944966605323814170545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23567706488561727008909573 4418944966605323814170545)
            ·
              refine ⟨3314208724953992860627909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418944966605323814170545 3314208724953992860627909)
              ·
                refine ⟨621414135928873661367733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3314208724953992860627909 621414135928873661367733)
                ·
                  refine ⟨58257575243331905753225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621414135928873661367733 58257575243331905753225)
                  ·
                    rfl

theorem cell23_1021106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_1021106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021106 prefixEnd_1021106 := by exact prefixLift 1021106
  have htrace : WordTrace (prefixWord ++ tailWord_1021106) baseStart_1021106 baseEnd_1021106 := by
    simpa [prefixWord, tailWord_1021106, baseEnd_1021106] using wordTrace_append hprefix tailTrace_1021106
  have hstable : (prefixWord ++ tailWord_1021106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021106).length < 2 ^ (prefixWord ++ tailWord_1021106).sum := by decide
  have hdescent : baseEnd_1021106 < baseStart_1021106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021116 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1021116 : Nat := 118140960795 + 1021116 * 2 ^ 59
def prefixEnd_1021116 : Nat := 4983230072969 + 3 ^ 40 * 1021116 * 2
def baseEnd_1021116 : Nat := 524323311996532112653979

theorem tailTrace_1021116 : CollatzResearch.WordTrace tailWord_1021116 prefixEnd_1021116 524323311996532112653979 := by
  unfold tailWord_1021116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18621580084339299786897601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24828773445785733049196801 18621580084339299786897601)
  ·
    refine ⟨13966185063254474840173201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18621580084339299786897601 13966185063254474840173201)
    ·
      refine ⟨10474638797440856130129901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13966185063254474840173201 10474638797440856130129901)
      ·
        refine ⟨3927989549040321048798713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10474638797440856130129901 3927989549040321048798713)
        ·
          refine ⟨2945992161780240786599035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927989549040321048798713 2945992161780240786599035)
          ·
            refine ⟨4418988242670361179898553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945992161780240786599035 4418988242670361179898553)
            ·
              refine ⟨3314241182002770884923915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418988242670361179898553 3314241182002770884923915)
              ·
                refine ⟨4971361773004156327385873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314241182002770884923915 4971361773004156327385873)
                ·
                  refine ⟨3728521329753117245539405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971361773004156327385873 3728521329753117245539405)
                  ·
                    refine ⟨1398195498657418967077277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3728521329753117245539405 1398195498657418967077277)
                    ·
                      refine ⟨524323311996532112653979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1398195498657418967077277 524323311996532112653979)
                      ·
                        rfl

theorem cell23_1021116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1021116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021116 prefixEnd_1021116 := by exact prefixLift 1021116
  have htrace : WordTrace (prefixWord ++ tailWord_1021116) baseStart_1021116 baseEnd_1021116 := by
    simpa [prefixWord, tailWord_1021116, baseEnd_1021116] using wordTrace_append hprefix tailTrace_1021116
  have hstable : (prefixWord ++ tailWord_1021116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021116).length < 2 ^ (prefixWord ++ tailWord_1021116).sum := by decide
  have hdescent : baseEnd_1021116 < baseStart_1021116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021156 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_1021156 : Nat := 118140960795 + 1021156 * 2 ^ 59
def prefixEnd_1021156 : Nat := 4983230072969 + 3 ^ 40 * 1021156 * 2
def baseEnd_1021156 : Nat := 524343851222711956153795

theorem tailTrace_1021156 : CollatzResearch.WordTrace tailWord_1021156 prefixEnd_1021156 524343851222711956153795 := by
  unfold tailWord_1021156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622309544266843202625661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24829746059022457603500881 18622309544266843202625661)
  ·
    refine ⟨6983366079100066200984623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18622309544266843202625661 6983366079100066200984623)
    ·
      refine ⟨10475049118650099301476935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983366079100066200984623 10475049118650099301476935)
      ·
        refine ⟨15712573677975148952215403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475049118650099301476935 15712573677975148952215403)
        ·
          refine ⟨23568860516962723428323105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15712573677975148952215403 23568860516962723428323105)
          ·
            refine ⟨17676645387722042571242329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23568860516962723428323105 17676645387722042571242329)
            ·
              refine ⟨13257484040791531928431747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17676645387722042571242329 13257484040791531928431747)
              ·
                refine ⟨19886226061187297892647621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257484040791531928431747 19886226061187297892647621)
                ·
                  refine ⟨3728667386472618354871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19886226061187297892647621 3728667386472618354871429)
                  ·
                    refine ⟨699125134963615941538393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3728667386472618354871429 699125134963615941538393)
                    ·
                      refine ⟨524343851222711956153795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699125134963615941538393 524343851222711956153795)
                      ·
                        rfl

theorem cell23_1021156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_1021156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021156 prefixEnd_1021156 := by exact prefixLift 1021156
  have htrace : WordTrace (prefixWord ++ tailWord_1021156) baseStart_1021156 baseEnd_1021156 := by
    simpa [prefixWord, tailWord_1021156, baseEnd_1021156] using wordTrace_append hprefix tailTrace_1021156
  have hstable : (prefixWord ++ tailWord_1021156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021156).length < 2 ^ (prefixWord ++ tailWord_1021156).sum := by decide
  have hdescent : baseEnd_1021156 < baseStart_1021156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021213 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 6]
def baseStart_1021213 : Nat := 118140960795 + 1021213 * 2 ^ 59
def prefixEnd_1021213 : Nat := 4983230072969 + 3 ^ 40 * 1021213 * 2
def baseEnd_1021213 : Nat := 58263679957779803682337

theorem tailTrace_1021213 : CollatzResearch.WordTrace tailWord_1021213 prefixEnd_1021213 58263679957779803682337 := by
  unfold tailWord_1021213
  simp only [CollatzResearch.WordTrace]
  refine ⟨37246698049327185140076293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24831132032884790093384195 37246698049327185140076293)
  ·
    refine ⟨6983755884248847213764305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37246698049327185140076293 6983755884248847213764305)
    ·
      refine ⟨5237816913186635410323229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6983755884248847213764305 5237816913186635410323229)
      ·
        refine ⟨1964181342444988278871211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5237816913186635410323229 1964181342444988278871211)
        ·
          refine ⟨2946272013667482418306817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964181342444988278871211 2946272013667482418306817)
          ·
            refine ⟨2209704010250611813730113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2946272013667482418306817 2209704010250611813730113)
            ·
              refine ⟨1657278007687958860297585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209704010250611813730113 1657278007687958860297585)
              ·
                refine ⟨1242958505765969145223189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657278007687958860297585 1242958505765969145223189)
                ·
                  refine ⟨58263679957779803682337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1242958505765969145223189 58263679957779803682337)
                  ·
                    rfl

theorem cell23_1021213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_1021213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021213 prefixEnd_1021213 := by exact prefixLift 1021213
  have htrace : WordTrace (prefixWord ++ tailWord_1021213) baseStart_1021213 baseEnd_1021213 := by
    simpa [prefixWord, tailWord_1021213, baseEnd_1021213] using wordTrace_append hprefix tailTrace_1021213
  have hstable : (prefixWord ++ tailWord_1021213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021213).length < 2 ^ (prefixWord ++ tailWord_1021213).sum := by decide
  have hdescent : baseEnd_1021213 < baseStart_1021213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021236 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1021236 : Nat := 118140960795 + 1021236 * 2 ^ 59
def prefixEnd_1021236 : Nat := 4983230072969 + 3 ^ 40 * 1021236 * 2
def baseEnd_1021236 : Nat := 524384929675071643153427

theorem tailTrace_1021236 : CollatzResearch.WordTrace tailWord_1021236 prefixEnd_1021236 524384929675071643153427 := by
  unfold tailWord_1021236
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623768464121930034081781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24831691285495906712109041 18623768464121930034081781)
  ·
    refine ⟨1745978293511430940695167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18623768464121930034081781 1745978293511430940695167)
    ·
      refine ⟨2618967440267146411042751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745978293511430940695167 2618967440267146411042751)
      ·
        refine ⟨3928451160400719616564127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618967440267146411042751 3928451160400719616564127)
        ·
          refine ⟨5892676740601079424846191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928451160400719616564127 5892676740601079424846191)
          ·
            refine ⟨8839015110901619137269287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892676740601079424846191 8839015110901619137269287)
            ·
              refine ⟨13258522666352428705903931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839015110901619137269287 13258522666352428705903931)
              ·
                refine ⟨19887783999528643058855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13258522666352428705903931 19887783999528643058855897)
                ·
                  refine ⟨14915837999646482294141923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19887783999528643058855897 14915837999646482294141923)
                  ·
                    refine ⟨22373756999469723441212885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14915837999646482294141923 22373756999469723441212885)
                    ·
                      refine ⟨524384929675071643153427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22373756999469723441212885 524384929675071643153427)
                      ·
                        rfl

theorem cell23_1021236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1021236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021236 prefixEnd_1021236 := by exact prefixLift 1021236
  have htrace : WordTrace (prefixWord ++ tailWord_1021236) baseStart_1021236 baseEnd_1021236 := by
    simpa [prefixWord, tailWord_1021236, baseEnd_1021236] using wordTrace_append hprefix tailTrace_1021236
  have hstable : (prefixWord ++ tailWord_1021236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021236).length < 2 ^ (prefixWord ++ tailWord_1021236).sum := by decide
  have hdescent : baseEnd_1021236 < baseStart_1021236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021256 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1021256 : Nat := 118140960795 + 1021256 * 2 ^ 59
def prefixEnd_1021256 : Nat := 4983230072969 + 3 ^ 40 * 1021256 * 2
def baseEnd_1021256 : Nat := 174798399762720521634445

theorem tailTrace_1021256 : CollatzResearch.WordTrace tailWord_1021256 prefixEnd_1021256 174798399762720521634445 := by
  unfold tailWord_1021256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624133194085701741945811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24832177592114268989261081 18624133194085701741945811)
  ·
    refine ⟨27936199791128552612918717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18624133194085701741945811 27936199791128552612918717)
    ·
      refine ⟨10476074921673207229844519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27936199791128552612918717 10476074921673207229844519)
      ·
        refine ⟨15714112382509810844766779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476074921673207229844519 15714112382509810844766779)
        ·
          refine ⟨23571168573764716267150169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714112382509810844766779 23571168573764716267150169)
          ·
            refine ⟨17678376430323537200362627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23571168573764716267150169 17678376430323537200362627)
            ·
              refine ⟨26517564645485305800543941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17678376430323537200362627 26517564645485305800543941)
              ·
                refine ⟨4972043371028494837601989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26517564645485305800543941 4972043371028494837601989)
                ·
                  refine ⟨932258132067842782050373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4972043371028494837601989 932258132067842782050373)
                  ·
                    refine ⟨174798399762720521634445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 932258132067842782050373 174798399762720521634445)
                    ·
                      rfl

theorem cell23_1021256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1021256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021256 prefixEnd_1021256 := by exact prefixLift 1021256
  have htrace : WordTrace (prefixWord ++ tailWord_1021256) baseStart_1021256 baseEnd_1021256 := by
    simpa [prefixWord, tailWord_1021256, baseEnd_1021256] using wordTrace_append hprefix tailTrace_1021256
  have hstable : (prefixWord ++ tailWord_1021256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021256).length < 2 ^ (prefixWord ++ tailWord_1021256).sum := by decide
  have hdescent : baseEnd_1021256 < baseStart_1021256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021259 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_1021259 : Nat := 118140960795 + 1021259 * 2 ^ 59
def prefixEnd_1021259 : Nat := 4983230072969 + 3 ^ 40 * 1021259 * 2
def baseEnd_1021259 : Nat := 524396739730125053165821

theorem tailTrace_1021259 : CollatzResearch.WordTrace tailWord_1021259 prefixEnd_1021259 524396739730125053165821 := by
  unfold tailWord_1021259
  simp only [CollatzResearch.WordTrace]
  refine ⟨37248375807160534996250831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24832250538107023330833887 37248375807160534996250831)
  ·
    refine ⟨55872563710740802494376247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37248375807160534996250831 55872563710740802494376247)
    ·
      refine ⟨83808845566111203741564371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55872563710740802494376247 83808845566111203741564371)
      ·
        refine ⟨125713268349166805612346557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83808845566111203741564371 125713268349166805612346557)
        ·
          refine ⟨47142475630937552104629959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125713268349166805612346557 47142475630937552104629959)
          ·
            refine ⟨70713713446406328156944939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47142475630937552104629959 70713713446406328156944939)
            ·
              refine ⟨106070570169609492235417409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70713713446406328156944939 106070570169609492235417409)
              ·
                refine ⟨79552927627207119176563057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106070570169609492235417409 79552927627207119176563057)
                ·
                  refine ⟨59664695720405339382422293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79552927627207119176563057 59664695720405339382422293)
                  ·
                    refine ⟨2796782611894000283551045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59664695720405339382422293 2796782611894000283551045)
                    ·
                      refine ⟨524396739730125053165821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2796782611894000283551045 524396739730125053165821)
                      ·
                        rfl

theorem cell23_1021259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_1021259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021259 prefixEnd_1021259 := by exact prefixLift 1021259
  have htrace : WordTrace (prefixWord ++ tailWord_1021259) baseStart_1021259 baseEnd_1021259 := by
    simpa [prefixWord, tailWord_1021259, baseEnd_1021259] using wordTrace_append hprefix tailTrace_1021259
  have hstable : (prefixWord ++ tailWord_1021259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021259).length < 2 ^ (prefixWord ++ tailWord_1021259).sum := by decide
  have hdescent : baseEnd_1021259 < baseStart_1021259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021260 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_1021260 : Nat := 118140960795 + 1021260 * 2 ^ 59
def prefixEnd_1021260 : Nat := 4983230072969 + 3 ^ 40 * 1021260 * 2
def baseEnd_1021260 : Nat := 174799084403593183084439

theorem tailTrace_1021260 : CollatzResearch.WordTrace tailWord_1021260 prefixEnd_1021260 174799084403593183084439 := by
  unfold tailWord_1021260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624206140078456083518617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24832274853437941444691489 18624206140078456083518617)
  ·
    refine ⟨13968154605058842062638963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18624206140078456083518617 13968154605058842062638963)
    ·
      refine ⟨20952231907588263093958445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968154605058842062638963 20952231907588263093958445)
      ·
        refine ⟨7857086965345598660234417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20952231907588263093958445 7857086965345598660234417)
        ·
          refine ⟨5892815224009198995175813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7857086965345598660234417 5892815224009198995175813)
          ·
            refine ⟨1104902854501724811595465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5892815224009198995175813 1104902854501724811595465)
            ·
              refine ⟨828677140876293608696599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104902854501724811595465 828677140876293608696599)
              ·
                refine ⟨1243015711314440413044899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828677140876293608696599 1243015711314440413044899)
                ·
                  refine ⟨1864523566971660619567349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243015711314440413044899 1864523566971660619567349)
                  ·
                    refine ⟨174799084403593183084439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1864523566971660619567349 174799084403593183084439)
                    ·
                      rfl

theorem cell23_1021260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_1021260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021260 prefixEnd_1021260 := by exact prefixLift 1021260
  have htrace : WordTrace (prefixWord ++ tailWord_1021260) baseStart_1021260 baseEnd_1021260 := by
    simpa [prefixWord, tailWord_1021260, baseEnd_1021260] using wordTrace_append hprefix tailTrace_1021260
  have hstable : (prefixWord ++ tailWord_1021260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021260).length < 2 ^ (prefixWord ++ tailWord_1021260).sum := by decide
  have hdescent : baseEnd_1021260 < baseStart_1021260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021266 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1021266 : Nat := 118140960795 + 1021266 * 2 ^ 59
def prefixEnd_1021266 : Nat := 4983230072969 + 3 ^ 40 * 1021266 * 2
def baseEnd_1021266 : Nat := 524400334094706525778289

theorem tailTrace_1021266 : CollatzResearch.WordTrace tailWord_1021266 prefixEnd_1021266 524400334094706525778289 := by
  unfold tailWord_1021266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312157779533793797938913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24832420745423450127837101 9312157779533793797938913)
  ·
    refine ⟨6984118334650345348454185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9312157779533793797938913 6984118334650345348454185)
    ·
      refine ⟨5238088750987759011340639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6984118334650345348454185 5238088750987759011340639)
      ·
        refine ⟨7857133126481638517010959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238088750987759011340639 7857133126481638517010959)
        ·
          refine ⟨11785699689722457775516439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857133126481638517010959 11785699689722457775516439)
          ·
            refine ⟨17678549534583686663274659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785699689722457775516439 17678549534583686663274659)
            ·
              refine ⟨26517824301875529994911989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17678549534583686663274659 26517824301875529994911989)
              ·
                refine ⟨2486046028300830937022999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26517824301875529994911989 2486046028300830937022999)
                ·
                  refine ⟨3729069042451246405534499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486046028300830937022999 3729069042451246405534499)
                  ·
                    refine ⟨5593603563676869608301749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729069042451246405534499 5593603563676869608301749)
                    ·
                      refine ⟨524400334094706525778289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5593603563676869608301749 524400334094706525778289)
                      ·
                        rfl

theorem cell23_1021266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1021266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021266 prefixEnd_1021266 := by exact prefixLift 1021266
  have htrace : WordTrace (prefixWord ++ tailWord_1021266) baseStart_1021266 baseEnd_1021266 := by
    simpa [prefixWord, tailWord_1021266, baseEnd_1021266] using wordTrace_append hprefix tailTrace_1021266
  have hstable : (prefixWord ++ tailWord_1021266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021266).length < 2 ^ (prefixWord ++ tailWord_1021266).sum := by decide
  have hdescent : baseEnd_1021266 < baseStart_1021266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021273 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_1021273 : Nat := 118140960795 + 1021273 * 2 ^ 59
def prefixEnd_1021273 : Nat := 4983230072969 + 3 ^ 40 * 1021273 * 2
def baseEnd_1021273 : Nat := 174801309486429332796919

theorem tailTrace_1021273 : CollatzResearch.WordTrace tailWord_1021273 prefixEnd_1021273 174801309486429332796919 := by
  unfold tailWord_1021273
  simp only [CollatzResearch.WordTrace]
  refine ⟨37248886429109815387260473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24832590952739876924840315 37248886429109815387260473)
  ·
    refine ⟨27936664821832361540445355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37248886429109815387260473 27936664821832361540445355)
    ·
      refine ⟨41904997232748542310668033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27936664821832361540445355 41904997232748542310668033)
      ·
        refine ⟨31428747924561406733001025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41904997232748542310668033 31428747924561406733001025)
        ·
          refine ⟨23571560943421055049750769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31428747924561406733001025 23571560943421055049750769)
          ·
            refine ⟨17678670707565791287313077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23571560943421055049750769 17678670707565791287313077)
            ·
              refine ⟨1657375378834292933185601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17678670707565791287313077 1657375378834292933185601)
              ·
                refine ⟨1243031534125719699889201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657375378834292933185601 1243031534125719699889201)
                ·
                  refine ⟨932273650594289774916901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1243031534125719699889201 932273650594289774916901)
                  ·
                    refine ⟨174801309486429332796919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 932273650594289774916901 174801309486429332796919)
                    ·
                      rfl

theorem cell23_1021273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_1021273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021273 prefixEnd_1021273 := by exact prefixLift 1021273
  have htrace : WordTrace (prefixWord ++ tailWord_1021273) baseStart_1021273 baseEnd_1021273 := by
    simpa [prefixWord, tailWord_1021273, baseEnd_1021273] using wordTrace_append hprefix tailTrace_1021273
  have hstable : (prefixWord ++ tailWord_1021273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021273).length < 2 ^ (prefixWord ++ tailWord_1021273).sum := by decide
  have hdescent : baseEnd_1021273 < baseStart_1021273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021279 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1021279 : Nat := 118140960795 + 1021279 * 2 ^ 59
def prefixEnd_1021279 : Nat := 4983230072969 + 3 ^ 40 * 1021279 * 2
def baseEnd_1021279 : Nat := 524407009343214974915729

theorem tailTrace_1021279 : CollatzResearch.WordTrace tailWord_1021279 prefixEnd_1021279 524407009343214974915729 := by
  unfold tailWord_1021279
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249105267088078411978891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24832736844725385607985927 37249105267088078411978891)
  ·
    refine ⟨55873657900632117617968337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37249105267088078411978891 55873657900632117617968337)
    ·
      refine ⟨41905243425474088213476253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55873657900632117617968337 41905243425474088213476253)
      ·
        refine ⟨15714466284552783080053595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41905243425474088213476253 15714466284552783080053595)
        ·
          refine ⟨23571699426829174620080393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714466284552783080053595 23571699426829174620080393)
          ·
            refine ⟨17678774570121880965060295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23571699426829174620080393 17678774570121880965060295)
            ·
              refine ⟨26518161855182821447590443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17678774570121880965060295 26518161855182821447590443)
              ·
                refine ⟨39777242782774232171385665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26518161855182821447590443 39777242782774232171385665)
                ·
                  refine ⟨29832932087080674128539249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39777242782774232171385665 29832932087080674128539249)
                  ·
                    refine ⟨22374699065310505596404437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29832932087080674128539249 22374699065310505596404437)
                    ·
                      refine ⟨524407009343214974915729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22374699065310505596404437 524407009343214974915729)
                      ·
                        rfl

theorem cell23_1021279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1021279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021279 prefixEnd_1021279 := by exact prefixLift 1021279
  have htrace : WordTrace (prefixWord ++ tailWord_1021279) baseStart_1021279 baseEnd_1021279 := by
    simpa [prefixWord, tailWord_1021279, baseEnd_1021279] using wordTrace_append hprefix tailTrace_1021279
  have hstable : (prefixWord ++ tailWord_1021279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021279).length < 2 ^ (prefixWord ++ tailWord_1021279).sum := by decide
  have hdescent : baseEnd_1021279 < baseStart_1021279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021280 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2]
def baseStart_1021280 : Nat := 118140960795 + 1021280 * 2 ^ 59
def prefixEnd_1021280 : Nat := 4983230072969 + 3 ^ 40 * 1021280 * 2
def baseEnd_1021280 : Nat := 524407522823869471003225

theorem tailTrace_1021280 : CollatzResearch.WordTrace tailWord_1021280 prefixEnd_1021280 524407522823869471003225 := by
  unfold tailWord_1021280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624570870042227791382647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24832761160056303721843529 18624570870042227791382647)
  ·
    refine ⟨27936856305063341687073971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18624570870042227791382647 27936856305063341687073971)
    ·
      refine ⟨41905284457595012530610957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27936856305063341687073971 41905284457595012530610957)
      ·
        refine ⟨15714481671598129698979109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41905284457595012530610957 15714481671598129698979109)
        ·
          refine ⟨2946465313424649318558583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15714481671598129698979109 2946465313424649318558583)
          ·
            refine ⟨4419697970136973977837875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946465313424649318558583 4419697970136973977837875)
            ·
              refine ⟨6629546955205460966756813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419697970136973977837875 6629546955205460966756813)
              ·
                refine ⟨2486080108202047862533805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6629546955205460966756813 2486080108202047862533805)
                ·
                  refine ⟨932280040575767948450177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2486080108202047862533805 932280040575767948450177)
                  ·
                    refine ⟨699210030431825961337633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932280040575767948450177 699210030431825961337633)
                    ·
                      refine ⟨524407522823869471003225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699210030431825961337633 524407522823869471003225)
                      ·
                        rfl

theorem cell23_1021280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_1021280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021280 prefixEnd_1021280 := by exact prefixLift 1021280
  have htrace : WordTrace (prefixWord ++ tailWord_1021280) baseStart_1021280 baseEnd_1021280 := by
    simpa [prefixWord, tailWord_1021280, baseEnd_1021280] using wordTrace_append hprefix tailTrace_1021280
  have hstable : (prefixWord ++ tailWord_1021280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021280).length < 2 ^ (prefixWord ++ tailWord_1021280).sum := by decide
  have hdescent : baseEnd_1021280 < baseStart_1021280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021289 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_1021289 : Nat := 118140960795 + 1021289 * 2 ^ 59
def prefixEnd_1021289 : Nat := 4983230072969 + 3 ^ 40 * 1021289 * 2
def baseEnd_1021289 : Nat := 524412144149759935790683

theorem tailTrace_1021289 : CollatzResearch.WordTrace tailWord_1021289 prefixEnd_1021289 524412144149759935790683 := by
  unfold tailWord_1021289
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249469997051850119842921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24832979998034566746561947 37249469997051850119842921)
  ·
    refine ⟨27937102497788887589882191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37249469997051850119842921 27937102497788887589882191)
    ·
      refine ⟨41905653746683331384823287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937102497788887589882191 41905653746683331384823287)
      ·
        refine ⟨62858480620024997077234931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41905653746683331384823287 62858480620024997077234931)
        ·
          refine ⟨94287720930037495615852397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62858480620024997077234931 94287720930037495615852397)
          ·
            refine ⟨35357895348764060855944649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94287720930037495615852397 35357895348764060855944649)
            ·
              refine ⟨26518421511573045641958487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35357895348764060855944649 26518421511573045641958487)
              ·
                refine ⟨39777632267359568462937731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26518421511573045641958487 39777632267359568462937731)
                ·
                  refine ⟨59666448401039352694406597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39777632267359568462937731 59666448401039352694406597)
                  ·
                    refine ⟨11187459075194878630201237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59666448401039352694406597 11187459075194878630201237)
                    ·
                      refine ⟨524412144149759935790683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11187459075194878630201237 524412144149759935790683)
                      ·
                        rfl

theorem cell23_1021289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_1021289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021289 prefixEnd_1021289 := by exact prefixLift 1021289
  have htrace : WordTrace (prefixWord ++ tailWord_1021289) baseStart_1021289 baseEnd_1021289 := by
    simpa [prefixWord, tailWord_1021289, baseEnd_1021289] using wordTrace_append hprefix tailTrace_1021289
  have hstable : (prefixWord ++ tailWord_1021289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021289).length < 2 ^ (prefixWord ++ tailWord_1021289).sum := by decide
  have hdescent : baseEnd_1021289 < baseStart_1021289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021290 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1021290 : Nat := 118140960795 + 1021290 * 2 ^ 59
def prefixEnd_1021290 : Nat := 4983230072969 + 3 ^ 40 * 1021290 * 2
def baseEnd_1021290 : Nat := 174804219210138143959393

theorem tailTrace_1021290 : CollatzResearch.WordTrace tailWord_1021290 prefixEnd_1021290 174804219210138143959393 := by
  unfold tailWord_1021290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312376617512056822657331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24833004313365484860419549 9312376617512056822657331)
  ·
    refine ⟨13968564926268085233985997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9312376617512056822657331 13968564926268085233985997)
    ·
      refine ⟨5238211847350531962744749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13968564926268085233985997 5238211847350531962744749)
      ·
        refine ⟨1964329442756449486029281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5238211847350531962744749 1964329442756449486029281)
        ·
          refine ⟨1473247082067337114521961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964329442756449486029281 1473247082067337114521961)
          ·
            refine ⟨1104935311550502835891471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473247082067337114521961 1104935311550502835891471)
            ·
              refine ⟨1657402967325754253837207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104935311550502835891471 1657402967325754253837207)
              ·
                refine ⟨2486104450988631380755811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657402967325754253837207 2486104450988631380755811)
                ·
                  refine ⟨3729156676482947071133717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486104450988631380755811 3729156676482947071133717)
                  ·
                    refine ⟨174804219210138143959393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3729156676482947071133717 174804219210138143959393)
                    ·
                      rfl

theorem cell23_1021290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1021290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021290 prefixEnd_1021290 := by exact prefixLift 1021290
  have htrace : WordTrace (prefixWord ++ tailWord_1021290) baseStart_1021290 baseEnd_1021290 := by
    simpa [prefixWord, tailWord_1021290, baseEnd_1021290] using wordTrace_append hprefix tailTrace_1021290
  have hstable : (prefixWord ++ tailWord_1021290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021290).length < 2 ^ (prefixWord ++ tailWord_1021290).sum := by decide
  have hdescent : baseEnd_1021290 < baseStart_1021290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021293 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1021293 : Nat := 118140960795 + 1021293 * 2 ^ 59
def prefixEnd_1021293 : Nat := 4983230072969 + 3 ^ 40 * 1021293 * 2
def baseEnd_1021293 : Nat := 524414198072377920140665

theorem tailTrace_1021293 : CollatzResearch.WordTrace tailWord_1021293 prefixEnd_1021293 524414198072377920140665 := by
  unfold tailWord_1021293
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249615889037358802988533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24833077259358239201992355 37249615889037358802988533)
  ·
    refine ⟨3492151489597252387780175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37249615889037358802988533 3492151489597252387780175)
    ·
      refine ⟨5238227234395878581670263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3492151489597252387780175 5238227234395878581670263)
      ·
        refine ⟨7857340851593817872505395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238227234395878581670263 7857340851593817872505395)
        ·
          refine ⟨11786011277390726808758093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857340851593817872505395 11786011277390726808758093)
          ·
            refine ⟨4419754229021522553284285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11786011277390726808758093 4419754229021522553284285)
            ·
              refine ⟨1657407835883070957481607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419754229021522553284285 1657407835883070957481607)
              ·
                refine ⟨2486111753824606436222411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657407835883070957481607 2486111753824606436222411)
                ·
                  refine ⟨3729167630736909654333617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486111753824606436222411 3729167630736909654333617)
                  ·
                    refine ⟨2796875723052682240750213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729167630736909654333617 2796875723052682240750213)
                    ·
                      refine ⟨524414198072377920140665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2796875723052682240750213 524414198072377920140665)
                      ·
                        rfl

theorem cell23_1021293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1021293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021293 prefixEnd_1021293 := by exact prefixLift 1021293
  have htrace : WordTrace (prefixWord ++ tailWord_1021293) baseStart_1021293 baseEnd_1021293 := by
    simpa [prefixWord, tailWord_1021293, baseEnd_1021293] using wordTrace_append hprefix tailTrace_1021293
  have hstable : (prefixWord ++ tailWord_1021293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021293).length < 2 ^ (prefixWord ++ tailWord_1021293).sum := by decide
  have hdescent : baseEnd_1021293 < baseStart_1021293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021356 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_1021356 : Nat := 118140960795 + 1021356 * 2 ^ 59
def prefixEnd_1021356 : Nat := 4983230072969 + 3 ^ 40 * 1021356 * 2
def baseEnd_1021356 : Nat := 524446547353611173652875

theorem tailTrace_1021356 : CollatzResearch.WordTrace tailWord_1021356 prefixEnd_1021356 524446547353611173652875 := by
  unfold tailWord_1021356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625956843904560281265961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24834609125206080375021281 18625956843904560281265961)
  ·
    refine ⟨13969467632928420210949471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18625956843904560281265961 13969467632928420210949471)
    ·
      refine ⟨20954201449392630316424207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13969467632928420210949471 20954201449392630316424207)
      ·
        refine ⟨31431302174088945474636311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20954201449392630316424207 31431302174088945474636311)
        ·
          refine ⟨47146953261133418211954467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31431302174088945474636311 47146953261133418211954467)
          ·
            refine ⟨70720429891700127317931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47146953261133418211954467 70720429891700127317931701)
            ·
              refine ⟨6630040302346886936056097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70720429891700127317931701 6630040302346886936056097)
              ·
                refine ⟨4972530226760165202042073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630040302346886936056097 4972530226760165202042073)
                ·
                  refine ⟨3729397670070123901531555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972530226760165202042073 3729397670070123901531555)
                  ·
                    refine ⟨5594096505105185852297333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729397670070123901531555 5594096505105185852297333)
                    ·
                      refine ⟨524446547353611173652875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5594096505105185852297333 524446547353611173652875)
                      ·
                        rfl

theorem cell23_1021356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_1021356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021356 prefixEnd_1021356 := by exact prefixLift 1021356
  have htrace : WordTrace (prefixWord ++ tailWord_1021356) baseStart_1021356 baseEnd_1021356 := by
    simpa [prefixWord, tailWord_1021356, baseEnd_1021356] using wordTrace_append hprefix tailTrace_1021356
  have hstable : (prefixWord ++ tailWord_1021356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021356).length < 2 ^ (prefixWord ++ tailWord_1021356).sum := by decide
  have hdescent : baseEnd_1021356 < baseStart_1021356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021357 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1021357 : Nat := 118140960795 + 1021357 * 2 ^ 59
def prefixEnd_1021357 : Nat := 4983230072969 + 3 ^ 40 * 1021357 * 2
def baseEnd_1021357 : Nat := 524447060834265669740371

theorem tailTrace_1021357 : CollatzResearch.WordTrace tailWord_1021357 prefixEnd_1021357 524447060834265669740371 := by
  unfold tailWord_1021357
  simp only [CollatzResearch.WordTrace]
  refine ⟨37251950160805497733318325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24834633440536998488878883 37251950160805497733318325)
  ·
    refine ⟨3492370327575515412498593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37251950160805497733318325 3492370327575515412498593)
    ·
      refine ⟨2619277745681636559373945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3492370327575515412498593 2619277745681636559373945)
      ·
        refine ⟨1964458309261227419530459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619277745681636559373945 1964458309261227419530459)
        ·
          refine ⟨2946687463891841129295689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964458309261227419530459 2946687463891841129295689)
          ·
            refine ⟨2210015597918880846971767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2946687463891841129295689 2210015597918880846971767)
            ·
              refine ⟨3315023396878321270457651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210015597918880846971767 3315023396878321270457651)
              ·
                refine ⟨4972535095317481905686477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315023396878321270457651 4972535095317481905686477)
                ·
                  refine ⟨1864700660744055714632429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4972535095317481905686477 1864700660744055714632429)
                  ·
                    refine ⟨699262747779020892987161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864700660744055714632429 699262747779020892987161)
                    ·
                      refine ⟨524447060834265669740371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699262747779020892987161 524447060834265669740371)
                      ·
                        rfl

theorem cell23_1021357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1021357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021357 prefixEnd_1021357 := by exact prefixLift 1021357
  have htrace : WordTrace (prefixWord ++ tailWord_1021357) baseStart_1021357 baseEnd_1021357 := by
    simpa [prefixWord, tailWord_1021357, baseEnd_1021357] using wordTrace_append hprefix tailTrace_1021357
  have hstable : (prefixWord ++ tailWord_1021357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021357).length < 2 ^ (prefixWord ++ tailWord_1021357).sum := by decide
  have hdescent : baseEnd_1021357 < baseStart_1021357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021423 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 2, 5]
def baseStart_1021423 : Nat := 118140960795 + 1021423 * 2 ^ 59
def prefixEnd_1021423 : Nat := 4983230072969 + 3 ^ 40 * 1021423 * 2
def baseEnd_1021423 : Nat := 174826983519154137171689

theorem tailTrace_1021423 : CollatzResearch.WordTrace tailWord_1021423 prefixEnd_1021423 174826983519154137171689 := by
  unfold tailWord_1021423
  simp only [CollatzResearch.WordTrace]
  refine ⟨37254357378566391005220923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24836238252377594003480615 37254357378566391005220923)
  ·
    refine ⟨55881536067849586507831385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37254357378566391005220923 55881536067849586507831385)
    ·
      refine ⟨41911152050887189880873539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55881536067849586507831385 41911152050887189880873539)
      ·
        refine ⟨62866728076330784821310309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41911152050887189880873539 62866728076330784821310309)
        ·
          refine ⟨11787511514312022153995683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62866728076330784821310309 11787511514312022153995683)
          ·
            refine ⟨17681267271468033230993525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787511514312022153995683 17681267271468033230993525)
            ·
              refine ⟨1657618806700128115405643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17681267271468033230993525 1657618806700128115405643)
              ·
                refine ⟨2486428210050192173108465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657618806700128115405643 2486428210050192173108465)
                ·
                  refine ⟨1864821157537644129831349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486428210050192173108465 1864821157537644129831349)
                  ·
                    refine ⟨174826983519154137171689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1864821157537644129831349 174826983519154137171689)
                    ·
                      rfl

theorem cell23_1021423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_1021423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021423 prefixEnd_1021423 := by exact prefixLift 1021423
  have htrace : WordTrace (prefixWord ++ tailWord_1021423) baseStart_1021423 baseEnd_1021423 := by
    simpa [prefixWord, tailWord_1021423, baseEnd_1021423] using wordTrace_append hprefix tailTrace_1021423
  have hstable : (prefixWord ++ tailWord_1021423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021423).length < 2 ^ (prefixWord ++ tailWord_1021423).sum := by decide
  have hdescent : baseEnd_1021423 < baseStart_1021423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021438 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1021438 : Nat := 118140960795 + 1021438 * 2 ^ 59
def prefixEnd_1021438 : Nat := 4983230072969 + 3 ^ 40 * 1021438 * 2
def baseEnd_1021438 : Nat := 524488652767279852827499

theorem tailTrace_1021438 : CollatzResearch.WordTrace tailWord_1021438 prefixEnd_1021438 524488652767279852827499 := by
  unfold tailWord_1021438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656863059189006070877121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24836602982341365711344645 4656863059189006070877121)
  ·
    refine ⟨3492647294391754553157841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4656863059189006070877121 3492647294391754553157841)
    ·
      refine ⟨2619485470793815914868381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3492647294391754553157841 2619485470793815914868381)
      ·
        refine ⟨982307051547680968075643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2619485470793815914868381 982307051547680968075643)
        ·
          refine ⟨1473460577321521452113465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982307051547680968075643 1473460577321521452113465)
          ·
            refine ⟨1105095432991141089085099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473460577321521452113465 1105095432991141089085099)
            ·
              refine ⟨1657643149486711633627649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105095432991141089085099 1657643149486711633627649)
              ·
                refine ⟨1243232362115033725220737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657643149486711633627649 1243232362115033725220737)
                ·
                  refine ⟨932424271586275293915553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1243232362115033725220737 932424271586275293915553)
                  ·
                    refine ⟨699318203689706470436665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932424271586275293915553 699318203689706470436665)
                    ·
                      refine ⟨524488652767279852827499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699318203689706470436665 524488652767279852827499)
                      ·
                        rfl

theorem cell23_1021438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1021438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021438 prefixEnd_1021438 := by exact prefixLift 1021438
  have htrace : WordTrace (prefixWord ++ tailWord_1021438) baseStart_1021438 baseEnd_1021438 := by
    simpa [prefixWord, tailWord_1021438, baseEnd_1021438] using wordTrace_append hprefix tailTrace_1021438
  have hstable : (prefixWord ++ tailWord_1021438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021438).length < 2 ^ (prefixWord ++ tailWord_1021438).sum := by decide
  have hdescent : baseEnd_1021438 < baseStart_1021438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021517 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1021517 : Nat := 118140960795 + 1021517 * 2 ^ 59
def prefixEnd_1021517 : Nat := 4983230072969 + 3 ^ 40 * 1021517 * 2
def baseEnd_1021517 : Nat := 58281024193220560415515

theorem tailTrace_1021517 : CollatzResearch.WordTrace tailWord_1021517 prefixEnd_1021517 58281024193220560415515 := by
  unfold tailWord_1021517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257785840225845059142805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24838523893483896706095203 37257785840225845059142805)
  ·
    refine ⟨1746458711260586487147319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37257785840225845059142805 1746458711260586487147319)
    ·
      refine ⟨2619688066890879730720979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746458711260586487147319 2619688066890879730720979)
      ·
        refine ⟨3929532100336319596081469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619688066890879730720979 3929532100336319596081469)
        ·
          refine ⟨1473574537626119848530551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3929532100336319596081469 1473574537626119848530551)
          ·
            refine ⟨2210361806439179772795827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473574537626119848530551 2210361806439179772795827)
            ·
              refine ⟨3315542709658769659193741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210361806439179772795827 3315542709658769659193741)
              ·
                refine ⟨1243328516122038622197653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315542709658769659193741 1243328516122038622197653)
                ·
                  refine ⟨58281024193220560415515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1243328516122038622197653 58281024193220560415515)
                  ·
                    rfl

theorem cell23_1021517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1021517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021517 prefixEnd_1021517 := by exact prefixLift 1021517
  have htrace : WordTrace (prefixWord ++ tailWord_1021517) baseStart_1021517 baseEnd_1021517 := by
    simpa [prefixWord, tailWord_1021517, baseEnd_1021517] using wordTrace_append hprefix tailTrace_1021517
  have hstable : (prefixWord ++ tailWord_1021517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021517).length < 2 ^ (prefixWord ++ tailWord_1021517).sum := by decide
  have hdescent : baseEnd_1021517 < baseStart_1021517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021520 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2]
def baseStart_1021520 : Nat := 118140960795 + 1021520 * 2 ^ 59
def prefixEnd_1021520 : Nat := 4983230072969 + 3 ^ 40 * 1021520 * 2
def baseEnd_1021520 : Nat := 524530758180948532002121

theorem tailTrace_1021520 : CollatzResearch.WordTrace tailWord_1021520 prefixEnd_1021520 524530758180948532002121 := by
  unfold tailWord_1021520
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628947629607488285751007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24838596839476651047668009 18628947629607488285751007)
  ·
    refine ⟨27943421444411232428626511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18628947629607488285751007 27943421444411232428626511)
    ·
      refine ⟨41915132166616848642939767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27943421444411232428626511 41915132166616848642939767)
      ·
        refine ⟨62872698249925272964409651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41915132166616848642939767 62872698249925272964409651)
        ·
          refine ⟨94309047374887909446614477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62872698249925272964409651 94309047374887909446614477)
          ·
            refine ⟨35365892765582966042480429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94309047374887909446614477 35365892765582966042480429)
            ·
              refine ⟨13262209787093612265930161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35365892765582966042480429 13262209787093612265930161)
              ·
                refine ⟨9946657340320209199447621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13262209787093612265930161 9946657340320209199447621)
                ·
                  refine ⟨1864998251310039224896429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9946657340320209199447621 1864998251310039224896429)
                  ·
                    refine ⟨699374344241264709336161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864998251310039224896429 699374344241264709336161)
                    ·
                      refine ⟨524530758180948532002121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699374344241264709336161 524530758180948532002121)
                      ·
                        rfl

theorem cell23_1021520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2].length) (baseStart_1021520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021520 prefixEnd_1021520 := by exact prefixLift 1021520
  have htrace : WordTrace (prefixWord ++ tailWord_1021520) baseStart_1021520 baseEnd_1021520 := by
    simpa [prefixWord, tailWord_1021520, baseEnd_1021520] using wordTrace_append hprefix tailTrace_1021520
  have hstable : (prefixWord ++ tailWord_1021520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021520).length < 2 ^ (prefixWord ++ tailWord_1021520).sum := by decide
  have hdescent : baseEnd_1021520 < baseStart_1021520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021537 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_1021537 : Nat := 118140960795 + 1021537 * 2 ^ 59
def prefixEnd_1021537 : Nat := 4983230072969 + 3 ^ 40 * 1021537 * 2
def baseEnd_1021537 : Nat := 524539487352074965489543

theorem tailTrace_1021537 : CollatzResearch.WordTrace tailWord_1021537 prefixEnd_1021537 524539487352074965489543 := by
  unfold tailWord_1021537
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258515300153388474870865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24839010200102258983247243 37258515300153388474870865)
  ·
    refine ⟨27943886475115041356153149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37258515300153388474870865 27943886475115041356153149)
    ·
      refine ⟨10478957428168140508557431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27943886475115041356153149 10478957428168140508557431)
      ·
        refine ⟨15718436142252210762836147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478957428168140508557431 15718436142252210762836147)
        ·
          refine ⟨23577654213378316144254221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718436142252210762836147 23577654213378316144254221)
          ·
            refine ⟨8841620330016868554095333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23577654213378316144254221 8841620330016868554095333)
            ·
              refine ⟨1657803811878162853892875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8841620330016868554095333 1657803811878162853892875)
              ·
                refine ⟨2486705717817244280839313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657803811878162853892875 2486705717817244280839313)
                ·
                  refine ⟨1865029288362933210629485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486705717817244280839313 1865029288362933210629485)
                  ·
                    refine ⟨699385983136099953986057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865029288362933210629485 699385983136099953986057)
                    ·
                      refine ⟨524539487352074965489543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699385983136099953986057 524539487352074965489543)
                      ·
                        rfl

theorem cell23_1021537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_1021537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021537 prefixEnd_1021537 := by exact prefixLift 1021537
  have htrace : WordTrace (prefixWord ++ tailWord_1021537) baseStart_1021537 baseEnd_1021537 := by
    simpa [prefixWord, tailWord_1021537, baseEnd_1021537] using wordTrace_append hprefix tailTrace_1021537
  have hstable : (prefixWord ++ tailWord_1021537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021537).length < 2 ^ (prefixWord ++ tailWord_1021537).sum := by decide
  have hdescent : baseEnd_1021537 < baseStart_1021537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021543 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1021543 : Nat := 118140960795 + 1021543 * 2 ^ 59
def prefixEnd_1021543 : Nat := 4983230072969 + 3 ^ 40 * 1021543 * 2
def baseEnd_1021543 : Nat := 174847522745333980671505

theorem tailTrace_1021543 : CollatzResearch.WordTrace tailWord_1021543 prefixEnd_1021543 174847522745333980671505 := by
  unfold tailWord_1021543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258734138131651499589283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24839156092087767666392855 37258734138131651499589283)
  ·
    refine ⟨55888101207197477249383925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37258734138131651499589283 55888101207197477249383925)
    ·
      refine ⟨5239509488174763492129743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55888101207197477249383925 5239509488174763492129743)
      ·
        refine ⟨7859264232262145238194615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5239509488174763492129743 7859264232262145238194615)
        ·
          refine ⟨11788896348393217857291923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7859264232262145238194615 11788896348393217857291923)
          ·
            refine ⟨17683344522589826785937885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11788896348393217857291923 17683344522589826785937885)
            ·
              refine ⟨6631254195971185044726707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17683344522589826785937885 6631254195971185044726707)
              ·
                refine ⟨9946881293956777567090061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631254195971185044726707 9946881293956777567090061)
                ·
                  refine ⟨3730080485233791587658773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9946881293956777567090061 3730080485233791587658773)
                  ·
                    refine ⟨174847522745333980671505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3730080485233791587658773 174847522745333980671505)
                    ·
                      rfl

theorem cell23_1021543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1021543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021543 prefixEnd_1021543 := by exact prefixLift 1021543
  have htrace : WordTrace (prefixWord ++ tailWord_1021543) baseStart_1021543 baseEnd_1021543 := by
    simpa [prefixWord, tailWord_1021543, baseEnd_1021543] using wordTrace_append hprefix tailTrace_1021543
  have hstable : (prefixWord ++ tailWord_1021543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021543).length < 2 ^ (prefixWord ++ tailWord_1021543).sum := by decide
  have hdescent : baseEnd_1021543 < baseStart_1021543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021563 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_1021563 : Nat := 118140960795 + 1021563 * 2 ^ 59
def prefixEnd_1021563 : Nat := 4983230072969 + 3 ^ 40 * 1021563 * 2
def baseEnd_1021563 : Nat := 524552837849091863764423

theorem tailTrace_1021563 : CollatzResearch.WordTrace tailWord_1021563 prefixEnd_1021563 524552837849091863764423 := by
  unfold tailWord_1021563
  simp only [CollatzResearch.WordTrace]
  refine ⟨37259463598059194915317343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24839642398706129943544895 37259463598059194915317343)
  ·
    refine ⟨55889195397088792372976015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37259463598059194915317343 55889195397088792372976015)
    ·
      refine ⟨83833793095633188559464023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55889195397088792372976015 83833793095633188559464023)
      ·
        refine ⟨125750689643449782839196035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83833793095633188559464023 125750689643449782839196035)
        ·
          refine ⟨188626034465174674258794053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125750689643449782839196035 188626034465174674258794053)
          ·
            refine ⟨35367381462220251423523885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188626034465174674258794053 35367381462220251423523885)
            ·
              refine ⟨13262768048332594283821457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35367381462220251423523885 13262768048332594283821457)
              ·
                refine ⟨9947076036249445712866093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13262768048332594283821457 9947076036249445712866093)
                ·
                  refine ⟨3730153513593542142324785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9947076036249445712866093 3730153513593542142324785)
                  ·
                    refine ⟨2797615135195156606743589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730153513593542142324785 2797615135195156606743589)
                    ·
                      refine ⟨524552837849091863764423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2797615135195156606743589 524552837849091863764423)
                      ·
                        rfl

theorem cell23_1021563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_1021563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021563 prefixEnd_1021563 := by exact prefixLift 1021563
  have htrace : WordTrace (prefixWord ++ tailWord_1021563) baseStart_1021563 baseEnd_1021563 := by
    simpa [prefixWord, tailWord_1021563, baseEnd_1021563] using wordTrace_append hprefix tailTrace_1021563
  have hstable : (prefixWord ++ tailWord_1021563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021563).length < 2 ^ (prefixWord ++ tailWord_1021563).sum := by decide
  have hdescent : baseEnd_1021563 < baseStart_1021563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021580 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1021580 : Nat := 118140960795 + 1021580 * 2 ^ 59
def prefixEnd_1021580 : Nat := 4983230072969 + 3 ^ 40 * 1021580 * 2
def baseEnd_1021580 : Nat := 524561567020218297251845

theorem tailTrace_1021580 : CollatzResearch.WordTrace tailWord_1021580 prefixEnd_1021580 524561567020218297251845 := by
  unfold tailWord_1021580
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630041819498803409343097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24840055759331737879124129 18630041819498803409343097)
  ·
    refine ⟨13972531364624102557007323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18630041819498803409343097 13972531364624102557007323)
    ·
      refine ⟨20958797046936153835510985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13972531364624102557007323 20958797046936153835510985)
      ·
        refine ⟨15719097785202115376633239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20958797046936153835510985 15719097785202115376633239)
        ·
          refine ⟨23578646677803173064949859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719097785202115376633239 23578646677803173064949859)
          ·
            refine ⟨35367970016704759597424789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23578646677803173064949859 35367970016704759597424789)
            ·
              refine ⟨1657873594533035606129287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35367970016704759597424789 1657873594533035606129287)
              ·
                refine ⟨2486810391799553409193931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657873594533035606129287 2486810391799553409193931)
                ·
                  refine ⟨3730215587699330113790897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486810391799553409193931 3730215587699330113790897)
                  ·
                    refine ⟨2797661690774497585343173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730215587699330113790897 2797661690774497585343173)
                    ·
                      refine ⟨524561567020218297251845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2797661690774497585343173 524561567020218297251845)
                      ·
                        rfl

theorem cell23_1021580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1021580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021580 prefixEnd_1021580 := by exact prefixLift 1021580
  have htrace : WordTrace (prefixWord ++ tailWord_1021580) baseStart_1021580 baseEnd_1021580 := by
    simpa [prefixWord, tailWord_1021580, baseEnd_1021580] using wordTrace_append hprefix tailTrace_1021580
  have hstable : (prefixWord ++ tailWord_1021580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021580).length < 2 ^ (prefixWord ++ tailWord_1021580).sum := by decide
  have hdescent : baseEnd_1021580 < baseStart_1021580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021588 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1021588 : Nat := 118140960795 + 1021588 * 2 ^ 59
def prefixEnd_1021588 : Nat := 4983230072969 + 3 ^ 40 * 1021588 * 2
def baseEnd_1021588 : Nat := 524565674865454265951809

theorem tailTrace_1021588 : CollatzResearch.WordTrace tailWord_1021588 prefixEnd_1021588 524565674865454265951809 := by
  unfold tailWord_1021588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630187711484312092488709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24840250281979082789984945 18630187711484312092488709)
  ·
    refine ⟨3493160195903308517341633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18630187711484312092488709 3493160195903308517341633)
    ·
      refine ⟨2619870146927481388006225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3493160195903308517341633 2619870146927481388006225)
      ·
        refine ⟨1964902610195611041004669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619870146927481388006225 1964902610195611041004669)
        ·
          refine ⟨736838478823354140376751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1964902610195611041004669 736838478823354140376751)
          ·
            refine ⟨1105257718235031210565127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736838478823354140376751 1105257718235031210565127)
            ·
              refine ⟨1657886577352546815847691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105257718235031210565127 1657886577352546815847691)
              ·
                refine ⟨2486829866028820223771537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657886577352546815847691 2486829866028820223771537)
                ·
                  refine ⟨1865122399521615167828653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486829866028820223771537 1865122399521615167828653)
                  ·
                    refine ⟨699420899820605687935745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865122399521615167828653 699420899820605687935745)
                    ·
                      refine ⟨524565674865454265951809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699420899820605687935745 524565674865454265951809)
                      ·
                        rfl

theorem cell23_1021588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1021588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021588 prefixEnd_1021588 := by exact prefixLift 1021588
  have htrace : WordTrace (prefixWord ++ tailWord_1021588) baseStart_1021588 baseEnd_1021588 := by
    simpa [prefixWord, tailWord_1021588, baseEnd_1021588] using wordTrace_append hprefix tailTrace_1021588
  have hstable : (prefixWord ++ tailWord_1021588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021588).length < 2 ^ (prefixWord ++ tailWord_1021588).sum := by decide
  have hdescent : baseEnd_1021588 < baseStart_1021588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021601 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1021601 : Nat := 118140960795 + 1021601 * 2 ^ 59
def prefixEnd_1021601 : Nat := 4983230072969 + 3 ^ 40 * 1021601 * 2
def baseEnd_1021601 : Nat := 524572350113962715089249

theorem tailTrace_1021601 : CollatzResearch.WordTrace tailWord_1021601 prefixEnd_1021601 524572350113962715089249 := by
  unfold tailWord_1021601
  simp only [CollatzResearch.WordTrace]
  refine ⟨37260849571921527405200657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24840566381281018270133771 37260849571921527405200657)
  ·
    refine ⟨27945637178941145553900493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37260849571921527405200657 27945637178941145553900493)
    ·
      refine ⟨10479613942102929582712685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27945637178941145553900493 10479613942102929582712685)
      ·
        refine ⟨3929855228288598593517257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10479613942102929582712685 3929855228288598593517257)
        ·
          refine ⟨2947391421216448945137943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3929855228288598593517257 2947391421216448945137943)
          ·
            refine ⟨4421087131824673417706915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947391421216448945137943 4421087131824673417706915)
            ·
              refine ⟨6631630697737010126560373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421087131824673417706915 6631630697737010126560373)
              ·
                refine ⟨621715377912844699365035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6631630697737010126560373 621715377912844699365035)
                ·
                  refine ⟨932573066869267049047553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621715377912844699365035 932573066869267049047553)
                  ·
                    refine ⟨699429800151950286785665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932573066869267049047553 699429800151950286785665)
                    ·
                      refine ⟨524572350113962715089249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699429800151950286785665 524572350113962715089249)
                      ·
                        rfl

theorem cell23_1021601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1021601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021601 prefixEnd_1021601 := by exact prefixLift 1021601
  have htrace : WordTrace (prefixWord ++ tailWord_1021601) baseStart_1021601 baseEnd_1021601 := by
    simpa [prefixWord, tailWord_1021601, baseEnd_1021601] using wordTrace_append hprefix tailTrace_1021601
  have hstable : (prefixWord ++ tailWord_1021601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021601).length < 2 ^ (prefixWord ++ tailWord_1021601).sum := by decide
  have hdescent : baseEnd_1021601 < baseStart_1021601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021604 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_1021604 : Nat := 118140960795 + 1021604 * 2 ^ 59
def prefixEnd_1021604 : Nat := 4983230072969 + 3 ^ 40 * 1021604 * 2
def baseEnd_1021604 : Nat := 524573890555926203351735

theorem tailTrace_1021604 : CollatzResearch.WordTrace tailWord_1021604 prefixEnd_1021604 524573890555926203351735 := by
  unfold tailWord_1021604
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630479495455329458779933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24840639327273772611706577 18630479495455329458779933)
  ·
    refine ⟨6986429810795748547042475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18630479495455329458779933 6986429810795748547042475)
    ·
      refine ⟨10479644716193622820563713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6986429810795748547042475 10479644716193622820563713)
      ·
        refine ⟨7859733537145217115422785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10479644716193622820563713 7859733537145217115422785)
        ·
          refine ⟨5894800152858912836567089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7859733537145217115422785 5894800152858912836567089)
          ·
            refine ⟨4421100114644184627425317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894800152858912836567089 4421100114644184627425317)
            ·
              refine ⟨828956271495784617642247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4421100114644184627425317 828956271495784617642247)
              ·
                refine ⟨1243434407243676926463371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828956271495784617642247 1243434407243676926463371)
                ·
                  refine ⟨1865151610865515389695057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243434407243676926463371 1865151610865515389695057)
                  ·
                    refine ⟨1398863708149136542271293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865151610865515389695057 1398863708149136542271293)
                    ·
                      refine ⟨524573890555926203351735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1398863708149136542271293 524573890555926203351735)
                      ·
                        rfl

theorem cell23_1021604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_1021604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021604 prefixEnd_1021604 := by exact prefixLift 1021604
  have htrace : WordTrace (prefixWord ++ tailWord_1021604) baseStart_1021604 baseEnd_1021604 := by
    simpa [prefixWord, tailWord_1021604, baseEnd_1021604] using wordTrace_append hprefix tailTrace_1021604
  have hstable : (prefixWord ++ tailWord_1021604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021604).length < 2 ^ (prefixWord ++ tailWord_1021604).sum := by decide
  have hdescent : baseEnd_1021604 < baseStart_1021604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021638 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1021638 : Nat := 118140960795 + 1021638 * 2 ^ 59
def prefixEnd_1021638 : Nat := 4983230072969 + 3 ^ 40 * 1021638 * 2
def baseEnd_1021638 : Nat := 524591348898179070326579

theorem tailTrace_1021638 : CollatzResearch.WordTrace tailWord_1021638 prefixEnd_1021638 524591348898179070326579 := by
  unfold tailWord_1021638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164443721024608835134299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24841466048524988482865045 1164443721024608835134299)
  ·
    refine ⟨1746665581536913252701449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1164443721024608835134299 1746665581536913252701449)
    ·
      refine ⟨1309999186152684939526087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1746665581536913252701449 1309999186152684939526087)
      ·
        refine ⟨1964998779229027409289131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309999186152684939526087 1964998779229027409289131)
        ·
          refine ⟨2947498168843541113933697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964998779229027409289131 2947498168843541113933697)
          ·
            refine ⟨2210623626632655835450273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2947498168843541113933697 2210623626632655835450273)
            ·
              refine ⟨1657967719974491876587705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210623626632655835450273 1657967719974491876587705)
              ·
                refine ⟨1243475789980868907440779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657967719974491876587705 1243475789980868907440779)
                ·
                  refine ⟨1865213684971303361161169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243475789980868907440779 1865213684971303361161169)
                  ·
                    refine ⟨1398910263728477520870877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865213684971303361161169 1398910263728477520870877)
                    ·
                      refine ⟨524591348898179070326579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1398910263728477520870877 524591348898179070326579)
                      ·
                        rfl

theorem cell23_1021638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1021638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021638 prefixEnd_1021638 := by exact prefixLift 1021638
  have htrace : WordTrace (prefixWord ++ tailWord_1021638) baseStart_1021638 baseEnd_1021638 := by
    simpa [prefixWord, tailWord_1021638, baseEnd_1021638] using wordTrace_append hprefix tailTrace_1021638
  have hstable : (prefixWord ++ tailWord_1021638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021638).length < 2 ^ (prefixWord ++ tailWord_1021638).sum := by decide
  have hdescent : baseEnd_1021638 < baseStart_1021638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021643 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_1021643 : Nat := 118140960795 + 1021643 * 2 ^ 59
def prefixEnd_1021643 : Nat := 4983230072969 + 3 ^ 40 * 1021643 * 2
def baseEnd_1021643 : Nat := 524593916301451550764055

theorem tailTrace_1021643 : CollatzResearch.WordTrace tailWord_1021643 prefixEnd_1021643 524593916301451550764055 := by
  unfold tailWord_1021643
  simp only [CollatzResearch.WordTrace]
  refine ⟨37262381437769368578229583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24841587625179579052153055 37262381437769368578229583)
  ·
    refine ⟨55893572156654052867344375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37262381437769368578229583 55893572156654052867344375)
    ·
      refine ⟨83840358234981079301016563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55893572156654052867344375 83840358234981079301016563)
      ·
        refine ⟨125760537352471618951524845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83840358234981079301016563 125760537352471618951524845)
        ·
          refine ⟨47160201507176857106821817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125760537352471618951524845 47160201507176857106821817)
          ·
            refine ⟨35370151130382642830116363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47160201507176857106821817 35370151130382642830116363)
            ·
              refine ⟨53055226695573964245174545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35370151130382642830116363 53055226695573964245174545)
              ·
                refine ⟨39791420021680473183880909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53055226695573964245174545 39791420021680473183880909)
                ·
                  refine ⟨14921782508130177443955341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39791420021680473183880909 14921782508130177443955341)
                  ·
                    refine ⟨5595668440548816541483253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14921782508130177443955341 5595668440548816541483253)
                    ·
                      refine ⟨524593916301451550764055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5595668440548816541483253 524593916301451550764055)
                      ·
                        rfl

theorem cell23_1021643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_1021643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021643 prefixEnd_1021643 := by exact prefixLift 1021643
  have htrace : WordTrace (prefixWord ++ tailWord_1021643) baseStart_1021643 baseEnd_1021643 := by
    simpa [prefixWord, tailWord_1021643, baseEnd_1021643] using wordTrace_append hprefix tailTrace_1021643
  have hstable : (prefixWord ++ tailWord_1021643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021643).length < 2 ^ (prefixWord ++ tailWord_1021643).sum := by decide
  have hdescent : baseEnd_1021643 < baseStart_1021643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021673 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_1021673 : Nat := 118140960795 + 1021673 * 2 ^ 59
def prefixEnd_1021673 : Nat := 4983230072969 + 3 ^ 40 * 1021673 * 2
def baseEnd_1021673 : Nat := 524609320721086433388917

theorem tailTrace_1021673 : CollatzResearch.WordTrace tailWord_1021673 prefixEnd_1021673 524609320721086433388917 := by
  unfold tailWord_1021673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263475627660683701821673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24842317085107122467881115 37263475627660683701821673)
  ·
    refine ⟨27947606720745512776366255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37263475627660683701821673 27947606720745512776366255)
    ·
      refine ⟨41921410081118269164549383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27947606720745512776366255 41921410081118269164549383)
      ·
        refine ⟨62882115121677403746824075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41921410081118269164549383 62882115121677403746824075)
        ·
          refine ⟨94323172682516105620236113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62882115121677403746824075 94323172682516105620236113)
          ·
            refine ⟨70742379511887079215177085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94323172682516105620236113 70742379511887079215177085)
            ·
              refine ⟨26528392316957654705691407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70742379511887079215177085 26528392316957654705691407)
              ·
                refine ⟨39792588475436482058537111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26528392316957654705691407 39792588475436482058537111)
                ·
                  refine ⟨59688882713154723087805667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39792588475436482058537111 59688882713154723087805667)
                  ·
                    refine ⟨89533324069732084631708501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59688882713154723087805667 89533324069732084631708501)
                    ·
                      refine ⟨524609320721086433388917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 89533324069732084631708501 524609320721086433388917)
                      ·
                        rfl

theorem cell23_1021673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_1021673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021673 prefixEnd_1021673 := by exact prefixLift 1021673
  have htrace : WordTrace (prefixWord ++ tailWord_1021673) baseStart_1021673 baseEnd_1021673 := by
    simpa [prefixWord, tailWord_1021673, baseEnd_1021673] using wordTrace_append hprefix tailTrace_1021673
  have hstable : (prefixWord ++ tailWord_1021673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021673).length < 2 ^ (prefixWord ++ tailWord_1021673).sum := by decide
  have hdescent : baseEnd_1021673 < baseStart_1021673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021674 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_1021674 : Nat := 118140960795 + 1021674 * 2 ^ 59
def prefixEnd_1021674 : Nat := 4983230072969 + 3 ^ 40 * 1021674 * 2
def baseEnd_1021674 : Nat := 524609834201740929476413

theorem tailTrace_1021674 : CollatzResearch.WordTrace tailWord_1021674 prefixEnd_1021674 524609834201740929476413 := by
  unfold tailWord_1021674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9315878025164265218152019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24842341400438040581738717 9315878025164265218152019)
  ·
    refine ⟨13973817037746397827228029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9315878025164265218152019 13973817037746397827228029)
    ·
      refine ⟨5240181389154899185210511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13973817037746397827228029 5240181389154899185210511)
      ·
        refine ⟨7860272083732348777815767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5240181389154899185210511 7860272083732348777815767)
        ·
          refine ⟨11790408125598523166723651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860272083732348777815767 11790408125598523166723651)
          ·
            refine ⟨17685612188397784750085477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790408125598523166723651 17685612188397784750085477)
            ·
              refine ⟨3316052285324584640641027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17685612188397784750085477 3316052285324584640641027)
              ·
                refine ⟨4974078427986876960961541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316052285324584640641027 4974078427986876960961541)
                ·
                  refine ⟨932639705247539430180289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4974078427986876960961541 932639705247539430180289)
                  ·
                    refine ⟨699479778935654572635217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932639705247539430180289 699479778935654572635217)
                    ·
                      refine ⟨524609834201740929476413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699479778935654572635217 524609834201740929476413)
                      ·
                        rfl

theorem cell23_1021674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_1021674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021674 prefixEnd_1021674 := by exact prefixLift 1021674
  have htrace : WordTrace (prefixWord ++ tailWord_1021674) baseStart_1021674 baseEnd_1021674 := by
    simpa [prefixWord, tailWord_1021674, baseEnd_1021674] using wordTrace_append hprefix tailTrace_1021674
  have hstable : (prefixWord ++ tailWord_1021674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021674).length < 2 ^ (prefixWord ++ tailWord_1021674).sum := by decide
  have hdescent : baseEnd_1021674 < baseStart_1021674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021690 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_1021690 : Nat := 118140960795 + 1021690 * 2 ^ 59
def prefixEnd_1021690 : Nat := 4983230072969 + 3 ^ 40 * 1021690 * 2
def baseEnd_1021690 : Nat := 524618049892212866876339

theorem tailTrace_1021690 : CollatzResearch.WordTrace tailWord_1021690 prefixEnd_1021690 524618049892212866876339 := by
  unfold tailWord_1021690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316023917149773901297631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24842730445732730403460349 9316023917149773901297631)
  ·
    refine ⟨13974035875724660851946447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9316023917149773901297631 13974035875724660851946447)
    ·
      refine ⟨20961053813586991277919671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974035875724660851946447 20961053813586991277919671)
      ·
        refine ⟨31441580720380486916879507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20961053813586991277919671 31441580720380486916879507)
        ·
          refine ⟨47162371080570730375319261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31441580720380486916879507 47162371080570730375319261)
          ·
            refine ⟨17685889155214023890744723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47162371080570730375319261 17685889155214023890744723)
            ·
              refine ⟨26528833732821035836117085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17685889155214023890744723 26528833732821035836117085)
              ·
                refine ⟨9948312649807888438543907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26528833732821035836117085 9948312649807888438543907)
                ·
                  refine ⟨14922468974711832657815861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9948312649807888438543907 14922468974711832657815861)
                  ·
                    refine ⟨1398981466379234311670237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14922468974711832657815861 1398981466379234311670237)
                    ·
                      refine ⟨524618049892212866876339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1398981466379234311670237 524618049892212866876339)
                      ·
                        rfl

theorem cell23_1021690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_1021690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021690 prefixEnd_1021690 := by exact prefixLift 1021690
  have htrace : WordTrace (prefixWord ++ tailWord_1021690) baseStart_1021690 baseEnd_1021690 := by
    simpa [prefixWord, tailWord_1021690, baseEnd_1021690] using wordTrace_append hprefix tailTrace_1021690
  have hstable : (prefixWord ++ tailWord_1021690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021690).length < 2 ^ (prefixWord ++ tailWord_1021690).sum := by decide
  have hdescent : baseEnd_1021690 < baseStart_1021690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021710 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1021710 : Nat := 118140960795 + 1021710 * 2 ^ 59
def prefixEnd_1021710 : Nat := 4983230072969 + 3 ^ 40 * 1021710 * 2
def baseEnd_1021710 : Nat := 174876106501767596208749

theorem tailTrace_1021710 : CollatzResearch.WordTrace tailWord_1021710 prefixEnd_1021710 174876106501767596208749 := by
  unfold tailWord_1021710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658103141065829877614823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24843216752351092680612389 4658103141065829877614823)
  ·
    refine ⟨6987154711598744816422235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4658103141065829877614823 6987154711598744816422235)
    ·
      refine ⟨10480732067398117224633353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6987154711598744816422235 10480732067398117224633353)
      ·
        refine ⟨7860549050548587918475015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10480732067398117224633353 7860549050548587918475015)
        ·
          refine ⟨11790823575822881877712523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860549050548587918475015 11790823575822881877712523)
          ·
            refine ⟨17686235363734322816568785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790823575822881877712523 17686235363734322816568785)
            ·
              refine ⟨13264676522800742112426589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686235363734322816568785 13264676522800742112426589)
              ·
                refine ⟨4974253696050278292159971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13264676522800742112426589 4974253696050278292159971)
                ·
                  refine ⟨7461380544075417438239957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974253696050278292159971 7461380544075417438239957)
                  ·
                    refine ⟨174876106501767596208749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7461380544075417438239957 174876106501767596208749)
                    ·
                      rfl

theorem cell23_1021710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1021710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021710 prefixEnd_1021710 := by exact prefixLift 1021710
  have htrace : WordTrace (prefixWord ++ tailWord_1021710) baseStart_1021710 baseEnd_1021710 := by
    simpa [prefixWord, tailWord_1021710, baseEnd_1021710] using wordTrace_append hprefix tailTrace_1021710
  have hstable : (prefixWord ++ tailWord_1021710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021710).length < 2 ^ (prefixWord ++ tailWord_1021710).sum := by decide
  have hdescent : baseEnd_1021710 < baseStart_1021710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021720 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1021720 : Nat := 118140960795 + 1021720 * 2 ^ 59
def prefixEnd_1021720 : Nat := 4983230072969 + 3 ^ 40 * 1021720 * 2
def baseEnd_1021720 : Nat := 524633454311847749501201

theorem tailTrace_1021720 : CollatzResearch.WordTrace tailWord_1021720 prefixEnd_1021720 524633454311847749501201 := by
  unfold tailWord_1021720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632594929245205364391307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24843459905660273819188409 18632594929245205364391307)
  ·
    refine ⟨27948892393867808046586961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18632594929245205364391307 27948892393867808046586961)
    ·
      refine ⟨20961669295400856034940221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27948892393867808046586961 20961669295400856034940221)
      ·
        refine ⟨7860625985775321013102583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20961669295400856034940221 7860625985775321013102583)
        ·
          refine ⟨11790938978662981519653875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860625985775321013102583 11790938978662981519653875)
          ·
            refine ⟨17686408467994472279480813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790938978662981519653875 17686408467994472279480813)
            ·
              refine ⟨6632403175497927104805305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17686408467994472279480813 6632403175497927104805305)
              ·
                refine ⟨4974302381623445328603979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632403175497927104805305 4974302381623445328603979)
                ·
                  refine ⟨7461453572435167992905969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974302381623445328603979 7461453572435167992905969)
                  ·
                    refine ⟨5596090179326375994679477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461453572435167992905969 5596090179326375994679477)
                    ·
                      refine ⟨524633454311847749501201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5596090179326375994679477 524633454311847749501201)
                      ·
                        rfl

theorem cell23_1021720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1021720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021720 prefixEnd_1021720 := by exact prefixLift 1021720
  have htrace : WordTrace (prefixWord ++ tailWord_1021720) baseStart_1021720 baseEnd_1021720 := by
    simpa [prefixWord, tailWord_1021720, baseEnd_1021720] using wordTrace_append hprefix tailTrace_1021720
  have hstable : (prefixWord ++ tailWord_1021720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021720).length < 2 ^ (prefixWord ++ tailWord_1021720).sum := by decide
  have hdescent : baseEnd_1021720 < baseStart_1021720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021770 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_1021770 : Nat := 118140960795 + 1021770 * 2 ^ 59
def prefixEnd_1021770 : Nat := 4983230072969 + 3 ^ 40 * 1021770 * 2
def baseEnd_1021770 : Nat := 58295458704952505986219

theorem tailTrace_1021770 : CollatzResearch.WordTrace tailWord_1021770 prefixEnd_1021770 58295458704952505986219 := by
  unfold tailWord_1021770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316753377077317317025691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24844675672206179512068509 9316753377077317317025691)
  ·
    refine ⟨13975130065615975975538537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9316753377077317317025691 13975130065615975975538537)
    ·
      refine ⟨10481347549211981981653903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13975130065615975975538537 10481347549211981981653903)
      ·
        refine ⟨15722021323817972972480855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481347549211981981653903 15722021323817972972480855)
        ·
          refine ⟨23583031985726959458721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15722021323817972972480855 23583031985726959458721283)
          ·
            refine ⟨35374547978590439188081925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23583031985726959458721283 35374547978590439188081925)
            ·
              refine ⟨6632727745985707347765361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35374547978590439188081925 6632727745985707347765361)
              ·
                refine ⟨4974545809489280510824021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632727745985707347765361 4974545809489280510824021)
                ·
                  refine ⟨58295458704952505986219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4974545809489280510824021 58295458704952505986219)
                  ·
                    rfl

theorem cell23_1021770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_1021770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021770 prefixEnd_1021770 := by exact prefixLift 1021770
  have htrace : WordTrace (prefixWord ++ tailWord_1021770) baseStart_1021770 baseEnd_1021770 := by
    simpa [prefixWord, tailWord_1021770, baseEnd_1021770] using wordTrace_append hprefix tailTrace_1021770
  have hstable : (prefixWord ++ tailWord_1021770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021770).length < 2 ^ (prefixWord ++ tailWord_1021770).sum := by decide
  have hdescent : baseEnd_1021770 < baseStart_1021770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021804 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 6]
def baseStart_1021804 : Nat := 118140960795 + 1021804 * 2 ^ 59
def prefixEnd_1021804 : Nat := 4983230072969 + 3 ^ 40 * 1021804 * 2
def baseEnd_1021804 : Nat := 58297398520758380094535

theorem tailTrace_1021804 : CollatzResearch.WordTrace tailWord_1021804 prefixEnd_1021804 58297398520758380094535 := by
  unfold tailWord_1021804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18634126795093046537420233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24845502393457395383226977 18634126795093046537420233)
  ·
    refine ⟨13975595096319784903065175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18634126795093046537420233 13975595096319784903065175)
    ·
      refine ⟨20963392644479677354597763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13975595096319784903065175 20963392644479677354597763)
      ·
        refine ⟨31445088966719516031896645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20963392644479677354597763 31445088966719516031896645)
        ·
          refine ⟨5895954181259909255980621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31445088966719516031896645 5895954181259909255980621)
          ·
            refine ⟨2210982817972465970992733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5895954181259909255980621 2210982817972465970992733)
            ·
              refine ⟨829118556739674739122275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2210982817972465970992733 829118556739674739122275)
              ·
                refine ⟨1243677835109512108683413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829118556739674739122275 1243677835109512108683413)
                ·
                  refine ⟨58297398520758380094535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1243677835109512108683413 58297398520758380094535)
                  ·
                    rfl

theorem cell23_1021804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_1021804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021804 prefixEnd_1021804 := by exact prefixLift 1021804
  have htrace : WordTrace (prefixWord ++ tailWord_1021804) baseStart_1021804 baseEnd_1021804 := by
    simpa [prefixWord, tailWord_1021804, baseEnd_1021804] using wordTrace_append hprefix tailTrace_1021804
  have hstable : (prefixWord ++ tailWord_1021804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021804).length < 2 ^ (prefixWord ++ tailWord_1021804).sum := by decide
  have hdescent : baseEnd_1021804 < baseStart_1021804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021824 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2]
def baseStart_1021824 : Nat := 118140960795 + 1021824 * 2 ^ 59
def prefixEnd_1021824 : Nat := 4983230072969 + 3 ^ 40 * 1021824 * 2
def baseEnd_1021824 : Nat := 524686856299915342600723

theorem tailTrace_1021824 : CollatzResearch.WordTrace tailWord_1021824 prefixEnd_1021824 524686856299915342600723 := by
  unfold tailWord_1021824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18634491525056818245284263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24845988700075757660379017 18634491525056818245284263)
  ·
    refine ⟨27951737287585227367926395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18634491525056818245284263 27951737287585227367926395)
    ·
      refine ⟨41927605931377841051889593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27951737287585227367926395 41927605931377841051889593)
      ·
        refine ⟨31445704448533380788917195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41927605931377841051889593 31445704448533380788917195)
        ·
          refine ⟨47168556672800071183375793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31445704448533380788917195 47168556672800071183375793)
          ·
            refine ⟨35376417504600053387531845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47168556672800071183375793 35376417504600053387531845)
            ·
              refine ⟨6633078282112510010162221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35376417504600053387531845 6633078282112510010162221)
              ·
                refine ⟨2487404355792191253810833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633078282112510010162221 2487404355792191253810833)
                ·
                  refine ⟨1865553266844143440358125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2487404355792191253810833 1865553266844143440358125)
                  ·
                    refine ⟨699582475066553790134297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865553266844143440358125 699582475066553790134297)
                    ·
                      refine ⟨524686856299915342600723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699582475066553790134297 524686856299915342600723)
                      ·
                        rfl

theorem cell23_1021824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_1021824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021824 prefixEnd_1021824 := by exact prefixLift 1021824
  have htrace : WordTrace (prefixWord ++ tailWord_1021824) baseStart_1021824 baseEnd_1021824 := by
    simpa [prefixWord, tailWord_1021824, baseEnd_1021824] using wordTrace_append hprefix tailTrace_1021824
  have hstable : (prefixWord ++ tailWord_1021824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021824).length < 2 ^ (prefixWord ++ tailWord_1021824).sum := by decide
  have hdescent : baseEnd_1021824 < baseStart_1021824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021825 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1021825 : Nat := 118140960795 + 1021825 * 2 ^ 59
def prefixEnd_1021825 : Nat := 4983230072969 + 3 ^ 40 * 1021825 * 2
def baseEnd_1021825 : Nat := 174895789926856612896073

theorem tailTrace_1021825 : CollatzResearch.WordTrace tailWord_1021825 prefixEnd_1021825 174895789926856612896073 := by
  unfold tailWord_1021825
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269019523110013661354929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24846013015406675774236619 37269019523110013661354929)
  ·
    refine ⟨27951764642332510246016197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37269019523110013661354929 27951764642332510246016197)
    ·
      refine ⟨5240955870437345671128037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27951764642332510246016197 5240955870437345671128037)
      ·
        refine ⟨982679225707002313336507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5240955870437345671128037 982679225707002313336507)
        ·
          refine ⟨1474018838560503470004761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982679225707002313336507 1474018838560503470004761)
          ·
            refine ⟨1105514128920377602503571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474018838560503470004761 1105514128920377602503571)
            ·
              refine ⟨1658271193380566403755357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105514128920377602503571 1658271193380566403755357)
              ·
                refine ⟨621851697517712401408259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1658271193380566403755357 621851697517712401408259)
                ·
                  refine ⟨932777546276568602112389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621851697517712401408259 932777546276568602112389)
                  ·
                    refine ⟨174895789926856612896073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 932777546276568602112389 174895789926856612896073)
                    ·
                      rfl

theorem cell23_1021825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1021825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021825 prefixEnd_1021825 := by exact prefixLift 1021825
  have htrace : WordTrace (prefixWord ++ tailWord_1021825) baseStart_1021825 baseEnd_1021825 := by
    simpa [prefixWord, tailWord_1021825, baseEnd_1021825] using wordTrace_append hprefix tailTrace_1021825
  have hstable : (prefixWord ++ tailWord_1021825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021825).length < 2 ^ (prefixWord ++ tailWord_1021825).sum := by decide
  have hdescent : baseEnd_1021825 < baseStart_1021825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021877 : List Nat := [1, 3, 3, 2, 1, 2, 2, 9]
def baseStart_1021877 : Nat := 118140960795 + 1021877 * 2 ^ 59
def prefixEnd_1021877 : Nat := 4983230072969 + 3 ^ 40 * 1021877 * 2
def baseEnd_1021877 : Nat := 19433854473133467971777

theorem tailTrace_1021877 : CollatzResearch.WordTrace tailWord_1021877 prefixEnd_1021877 19433854473133467971777 := by
  unfold tailWord_1021877
  simp only [CollatzResearch.WordTrace]
  refine ⟨37270916118921626542247885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24847277412614417694831923 37270916118921626542247885)
  ·
    refine ⟨13976593544595609953342957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37270916118921626542247885 13976593544595609953342957)
    ·
      refine ⟨5241222579223353732503609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13976593544595609953342957 5241222579223353732503609)
      ·
        refine ⟨3930916934417515299377707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241222579223353732503609 3930916934417515299377707)
        ·
          refine ⟨5896375401626272949066561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930916934417515299377707 5896375401626272949066561)
          ·
            refine ⟨4422281551219704711799921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896375401626272949066561 4422281551219704711799921)
            ·
              refine ⟨3316711163414778533849941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422281551219704711799921 3316711163414778533849941)
              ·
                refine ⟨19433854473133467971777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3316711163414778533849941 19433854473133467971777)
                ·
                  rfl

theorem cell23_1021877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 9].length) (baseStart_1021877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021877 prefixEnd_1021877 := by exact prefixLift 1021877
  have htrace : WordTrace (prefixWord ++ tailWord_1021877) baseStart_1021877 baseEnd_1021877 := by
    simpa [prefixWord, tailWord_1021877, baseEnd_1021877] using wordTrace_append hprefix tailTrace_1021877
  have hstable : (prefixWord ++ tailWord_1021877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021877).length < 2 ^ (prefixWord ++ tailWord_1021877).sum := by decide
  have hdescent : baseEnd_1021877 < baseStart_1021877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021888 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 1, 2, 2]
def baseStart_1021888 : Nat := 118140960795 + 1021888 * 2 ^ 59
def prefixEnd_1021888 : Nat := 4983230072969 + 3 ^ 40 * 1021888 * 2
def baseEnd_1021888 : Nat := 524719719061803092200429

theorem tailTrace_1021888 : CollatzResearch.WordTrace tailWord_1021888 prefixEnd_1021888 524719719061803092200429 := by
  unfold tailWord_1021888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635658660940887710449159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24847544881254516947265545 18635658660940887710449159)
  ·
    refine ⟨27953487991411331565673739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635658660940887710449159 27953487991411331565673739)
    ·
      refine ⟨41930231987116997348510609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27953487991411331565673739 41930231987116997348510609)
      ·
        refine ⟨31447673990337748011382957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41930231987116997348510609 31447673990337748011382957)
        ·
          refine ⟨11792877746376655504268609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31447673990337748011382957 11792877746376655504268609)
          ·
            refine ⟨8844658309782491628201457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11792877746376655504268609 8844658309782491628201457)
            ·
              refine ⟨6633493732336868721151093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8844658309782491628201457 6633493732336868721151093)
              ·
                refine ⟨621890037406581442607915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6633493732336868721151093 621890037406581442607915)
                ·
                  refine ⟨932835056109872163911873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621890037406581442607915 932835056109872163911873)
                  ·
                    refine ⟨699626292082404122933905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932835056109872163911873 699626292082404122933905)
                    ·
                      refine ⟨524719719061803092200429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699626292082404122933905 524719719061803092200429)
                      ·
                        rfl

theorem cell23_1021888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_1021888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021888 prefixEnd_1021888 := by exact prefixLift 1021888
  have htrace : WordTrace (prefixWord ++ tailWord_1021888) baseStart_1021888 baseEnd_1021888 := by
    simpa [prefixWord, tailWord_1021888, baseEnd_1021888] using wordTrace_append hprefix tailTrace_1021888
  have hstable : (prefixWord ++ tailWord_1021888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021888).length < 2 ^ (prefixWord ++ tailWord_1021888).sum := by decide
  have hdescent : baseEnd_1021888 < baseStart_1021888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021904 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3]
def baseStart_1021904 : Nat := 118140960795 + 1021904 * 2 ^ 59
def prefixEnd_1021904 : Nat := 4983230072969 + 3 ^ 40 * 1021904 * 2
def baseEnd_1021904 : Nat := 524727934752275029600355

theorem tailTrace_1021904 : CollatzResearch.WordTrace tailWord_1021904 prefixEnd_1021904 524727934752275029600355 := by
  unfold tailWord_1021904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635950444911905076740383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24847933926549206768987177 18635950444911905076740383)
  ·
    refine ⟨27953925667367857615110575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635950444911905076740383 27953925667367857615110575)
    ·
      refine ⟨41930888501051786422665863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27953925667367857615110575 41930888501051786422665863)
      ·
        refine ⟨62896332751577679633998795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41930888501051786422665863 62896332751577679633998795)
        ·
          refine ⟨94344499127366519450998193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62896332751577679633998795 94344499127366519450998193)
          ·
            refine ⟨70758374345524889588248645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94344499127366519450998193 70758374345524889588248645)
            ·
              refine ⟨13267195189785916797796621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70758374345524889588248645 13267195189785916797796621)
              ·
                refine ⟨4975198196169718799173733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13267195189785916797796621 4975198196169718799173733)
                ·
                  refine ⟨932849661781822274845075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4975198196169718799173733 932849661781822274845075)
                  ·
                    refine ⟨1399274492672733412267613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 932849661781822274845075 1399274492672733412267613)
                    ·
                      refine ⟨524727934752275029600355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399274492672733412267613 524727934752275029600355)
                      ·
                        rfl

theorem cell23_1021904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_1021904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021904 prefixEnd_1021904 := by exact prefixLift 1021904
  have htrace : WordTrace (prefixWord ++ tailWord_1021904) baseStart_1021904 baseEnd_1021904 := by
    simpa [prefixWord, tailWord_1021904, baseEnd_1021904] using wordTrace_append hprefix tailTrace_1021904
  have hstable : (prefixWord ++ tailWord_1021904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021904).length < 2 ^ (prefixWord ++ tailWord_1021904).sum := by decide
  have hdescent : baseEnd_1021904 < baseStart_1021904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021921 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_1021921 : Nat := 118140960795 + 1021921 * 2 ^ 59
def prefixEnd_1021921 : Nat := 4983230072969 + 3 ^ 40 * 1021921 * 2
def baseEnd_1021921 : Nat := 524736663923401463087777

theorem tailTrace_1021921 : CollatzResearch.WordTrace tailWord_1021921 prefixEnd_1021921 524736663923401463087777 := by
  unfold tailWord_1021921
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272520930762222056849617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24848347287174814704566411 37272520930762222056849617)
  ·
    refine ⟨27954390698071666542637213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37272520930762222056849617 27954390698071666542637213)
    ·
      refine ⟨10482896511776874953488955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27954390698071666542637213 10482896511776874953488955)
      ·
        refine ⟨15724344767665312430233433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10482896511776874953488955 15724344767665312430233433)
        ·
          refine ⟨11793258575748984322675075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15724344767665312430233433 11793258575748984322675075)
          ·
            refine ⟨17689887863623476484012613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11793258575748984322675075 17689887863623476484012613)
            ·
              refine ⟨3316853974429401840752365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17689887863623476484012613 3316853974429401840752365)
              ·
                refine ⟨1243820240411025690282137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3316853974429401840752365 1243820240411025690282137)
                ·
                  refine ⟨932865180308269267711603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1243820240411025690282137 932865180308269267711603)
                  ·
                    refine ⟨1399297770462403901567405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 932865180308269267711603 1399297770462403901567405)
                    ·
                      refine ⟨524736663923401463087777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399297770462403901567405 524736663923401463087777)
                      ·
                        rfl

theorem cell23_1021921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_1021921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021921 prefixEnd_1021921 := by exact prefixLift 1021921
  have htrace : WordTrace (prefixWord ++ tailWord_1021921) baseStart_1021921 baseEnd_1021921 := by
    simpa [prefixWord, tailWord_1021921, baseEnd_1021921] using wordTrace_append hprefix tailTrace_1021921
  have hstable : (prefixWord ++ tailWord_1021921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021921).length < 2 ^ (prefixWord ++ tailWord_1021921).sum := by decide
  have hdescent : baseEnd_1021921 < baseStart_1021921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021942 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_1021942 : Nat := 118140960795 + 1021942 * 2 ^ 59
def prefixEnd_1021942 : Nat := 4983230072969 + 3 ^ 40 * 1021942 * 2
def baseEnd_1021942 : Nat := 524747447017145880925181

theorem tailTrace_1021942 : CollatzResearch.WordTrace tailWord_1021942 prefixEnd_1021942 524747447017145880925181 := by
  unfold tailWord_1021942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329580428980383915210255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24848857909124095095576053 2329580428980383915210255)
  ·
    refine ⟨3494370643470575872815383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329580428980383915210255 3494370643470575872815383)
    ·
      refine ⟨5241555965205863809223075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494370643470575872815383 5241555965205863809223075)
      ·
        refine ⟨7862333947808795713834613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241555965205863809223075 7862333947808795713834613)
        ·
          refine ⟨737093807607074598171995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7862333947808795713834613 737093807607074598171995)
          ·
            refine ⟨1105640711410611897257993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737093807607074598171995 1105640711410611897257993)
            ·
              refine ⟨829230533557958922943495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105640711410611897257993 829230533557958922943495)
              ·
                refine ⟨1243845800336938384415243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829230533557958922943495 1243845800336938384415243)
                ·
                  refine ⟨1865768700505407576622865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243845800336938384415243 1865768700505407576622865)
                  ·
                    refine ⟨1399326525379055682467149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865768700505407576622865 1399326525379055682467149)
                    ·
                      refine ⟨524747447017145880925181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399326525379055682467149 524747447017145880925181)
                      ·
                        rfl

theorem cell23_1021942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_1021942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021942 prefixEnd_1021942 := by exact prefixLift 1021942
  have htrace : WordTrace (prefixWord ++ tailWord_1021942) baseStart_1021942 baseEnd_1021942 := by
    simpa [prefixWord, tailWord_1021942, baseEnd_1021942] using wordTrace_append hprefix tailTrace_1021942
  have hstable : (prefixWord ++ tailWord_1021942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021942).length < 2 ^ (prefixWord ++ tailWord_1021942).sum := by decide
  have hdescent : baseEnd_1021942 < baseStart_1021942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021947 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_1021947 : Nat := 118140960795 + 1021947 * 2 ^ 59
def prefixEnd_1021947 : Nat := 4983230072969 + 3 ^ 40 * 1021947 * 2
def baseEnd_1021947 : Nat := 524750014420418361362657

theorem tailTrace_1021947 : CollatzResearch.WordTrace tailWord_1021947 prefixEnd_1021947 524750014420418361362657 := by
  unfold tailWord_1021947
  simp only [CollatzResearch.WordTrace]
  refine ⟨37273469228668028497296095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24848979485778685664864063 37273469228668028497296095)
  ·
    refine ⟨55910203843002042745944143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37273469228668028497296095 55910203843002042745944143)
    ·
      refine ⟨83865305764503064118916215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55910203843002042745944143 83865305764503064118916215)
      ·
        refine ⟨125797958646754596178374323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83865305764503064118916215 125797958646754596178374323)
        ·
          refine ⟨188696937970131894267561485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125797958646754596178374323 188696937970131894267561485)
          ·
            refine ⟨70761351738799460350335557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188696937970131894267561485 70761351738799460350335557)
            ·
              refine ⟨13267753451024898815687917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70761351738799460350335557 13267753451024898815687917)
              ·
                refine ⟨4975407544134337055882969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13267753451024898815687917 4975407544134337055882969)
                ·
                  refine ⟨3731555658100752791912227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975407544134337055882969 3731555658100752791912227)
                  ·
                    refine ⟨5597333487151129187868341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731555658100752791912227 5597333487151129187868341)
                    ·
                      refine ⟨524750014420418361362657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5597333487151129187868341 524750014420418361362657)
                      ·
                        rfl

theorem cell23_1021947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_1021947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021947 prefixEnd_1021947 := by exact prefixLift 1021947
  have htrace : WordTrace (prefixWord ++ tailWord_1021947) baseStart_1021947 baseEnd_1021947 := by
    simpa [prefixWord, tailWord_1021947, baseEnd_1021947] using wordTrace_append hprefix tailTrace_1021947
  have hstable : (prefixWord ++ tailWord_1021947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021947).length < 2 ^ (prefixWord ++ tailWord_1021947).sum := by decide
  have hdescent : baseEnd_1021947 < baseStart_1021947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021972 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1021972 : Nat := 118140960795 + 1021972 * 2 ^ 59
def prefixEnd_1021972 : Nat := 4983230072969 + 3 ^ 40 * 1021972 * 2
def baseEnd_1021972 : Nat := 524762851436780763550043

theorem tailTrace_1021972 : CollatzResearch.WordTrace tailWord_1021972 prefixEnd_1021972 524762851436780763550043 := by
  unfold tailWord_1021972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637190526788728883478085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24849587369051638511304113 18637190526788728883478085)
  ·
    refine ⟨3494473223772886665652141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18637190526788728883478085 3494473223772886665652141)
    ·
      refine ⟨1310427458914832499619553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3494473223772886665652141 1310427458914832499619553)
      ·
        refine ⟨982820594186124374714665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310427458914832499619553 982820594186124374714665)
        ·
          refine ⟨737115445639593281035999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982820594186124374714665 737115445639593281035999)
          ·
            refine ⟨1105673168459389921553999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737115445639593281035999 1105673168459389921553999)
            ·
              refine ⟨1658509752689084882330999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105673168459389921553999 1658509752689084882330999)
              ·
                refine ⟨2487764629033627323496499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658509752689084882330999 2487764629033627323496499)
                ·
                  refine ⟨3731646943550440985244749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487764629033627323496499 3731646943550440985244749)
                  ·
                    refine ⟨1399367603831415369466781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731646943550440985244749 1399367603831415369466781)
                    ·
                      refine ⟨524762851436780763550043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399367603831415369466781 524762851436780763550043)
                      ·
                        rfl

theorem cell23_1021972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1021972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021972 prefixEnd_1021972 := by exact prefixLift 1021972
  have htrace : WordTrace (prefixWord ++ tailWord_1021972) baseStart_1021972 baseEnd_1021972 := by
    simpa [prefixWord, tailWord_1021972, baseEnd_1021972] using wordTrace_append hprefix tailTrace_1021972
  have hstable : (prefixWord ++ tailWord_1021972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021972).length < 2 ^ (prefixWord ++ tailWord_1021972).sum := by decide
  have hdescent : baseEnd_1021972 < baseStart_1021972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021978 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_1021978 : Nat := 118140960795 + 1021978 * 2 ^ 59
def prefixEnd_1021978 : Nat := 4983230072969 + 3 ^ 40 * 1021978 * 2
def baseEnd_1021978 : Nat := 524765932320707740075015

theorem tailTrace_1021978 : CollatzResearch.WordTrace tailWord_1021978 prefixEnd_1021978 524765932320707740075015 := by
  unfold tailWord_1021978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318649972888930197918647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24849733261037147194449725 9318649972888930197918647)
  ·
    refine ⟨13977974959333395296877971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9318649972888930197918647 13977974959333395296877971)
    ·
      refine ⟨20966962439000092945316957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13977974959333395296877971 20966962439000092945316957)
      ·
        refine ⟨7862610914625034854493859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20966962439000092945316957 7862610914625034854493859)
        ·
          refine ⟨11793916371937552281740789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862610914625034854493859 11793916371937552281740789)
          ·
            refine ⟨1105679659869145526413199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11793916371937552281740789 1105679659869145526413199)
            ·
              refine ⟨1658519489803718289619799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105679659869145526413199 1658519489803718289619799)
              ·
                refine ⟨2487779234705577434429699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658519489803718289619799 2487779234705577434429699)
                ·
                  refine ⟨3731668852058366151644549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487779234705577434429699 3731668852058366151644549)
                  ·
                    refine ⟨699687909760943653433353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3731668852058366151644549 699687909760943653433353)
                    ·
                      refine ⟨524765932320707740075015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699687909760943653433353 524765932320707740075015)
                      ·
                        rfl

theorem cell23_1021978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_1021978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1021978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1021978 prefixEnd_1021978 := by exact prefixLift 1021978
  have htrace : WordTrace (prefixWord ++ tailWord_1021978) baseStart_1021978 baseEnd_1021978 := by
    simpa [prefixWord, tailWord_1021978, baseEnd_1021978] using wordTrace_append hprefix tailTrace_1021978
  have hstable : (prefixWord ++ tailWord_1021978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021978).length < 2 ^ (prefixWord ++ tailWord_1021978).sum := by decide
  have hdescent : baseEnd_1021978 < baseStart_1021978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022001 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 5]
def baseStart_1022001 : Nat := 118140960795 + 1022001 * 2 ^ 59
def prefixEnd_1022001 : Nat := 4983230072969 + 3 ^ 40 * 1022001 * 2
def baseEnd_1022001 : Nat := 58308638041751238898601

theorem tailTrace_1022001 : CollatzResearch.WordTrace tailWord_1022001 prefixEnd_1022001 58308638041751238898601 := by
  unfold tailWord_1022001
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275438770472395719761857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24850292513648263813174571 37275438770472395719761857)
  ·
    refine ⟨27956579077854296789821393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37275438770472395719761857 27956579077854296789821393)
    ·
      refine ⟨20967434308390722592366045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27956579077854296789821393 20967434308390722592366045)
      ·
        refine ⟨7862787865646520972137267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20967434308390722592366045 7862787865646520972137267)
        ·
          refine ⟨11794181798469781458205901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862787865646520972137267 11794181798469781458205901)
          ·
            refine ⟨4422818174426168046827213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11794181798469781458205901 4422818174426168046827213)
            ·
              refine ⟨1658556815409813017560205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4422818174426168046827213 1658556815409813017560205)
              ·
                refine ⟨621958805778679881585077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1658556815409813017560205 621958805778679881585077)
                ·
                  refine ⟨58308638041751238898601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621958805778679881585077 58308638041751238898601)
                  ·
                    rfl

theorem cell23_1022001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 5].length) (baseStart_1022001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022001 prefixEnd_1022001 := by exact prefixLift 1022001
  have htrace : WordTrace (prefixWord ++ tailWord_1022001) baseStart_1022001 baseEnd_1022001 := by
    simpa [prefixWord, tailWord_1022001, baseEnd_1022001] using wordTrace_append hprefix tailTrace_1022001
  have hstable : (prefixWord ++ tailWord_1022001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022001).length < 2 ^ (prefixWord ++ tailWord_1022001).sum := by decide
  have hdescent : baseEnd_1022001 < baseStart_1022001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022071 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1022071 : Nat := 118140960795 + 1022071 * 2 ^ 59
def prefixEnd_1022071 : Nat := 4983230072969 + 3 ^ 40 * 1022071 * 2
def baseEnd_1022071 : Nat := 524813686021575876212087

theorem tailTrace_1022071 : CollatzResearch.WordTrace tailWord_1022071 prefixEnd_1022071 524813686021575876212087 := by
  unfold tailWord_1022071
  simp only [CollatzResearch.WordTrace]
  refine ⟨37277991880218797674810067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24851994586812531783206711 37277991880218797674810067)
  ·
    refine ⟨55916987820328196512215101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37277991880218797674810067 55916987820328196512215101)
    ·
      refine ⟨20968870432623073692080663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55916987820328196512215101 20968870432623073692080663)
      ·
        refine ⟨31453305648934610538120995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20968870432623073692080663 31453305648934610538120995)
        ·
          refine ⟨47179958473401915807181493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31453305648934610538120995 47179958473401915807181493)
          ·
            refine ⟨4423121106881429606923265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47179958473401915807181493 4423121106881429606923265)
            ·
              refine ⟨3317340830161072205192449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423121106881429606923265 3317340830161072205192449)
              ·
                refine ⟨2488005622620804153894337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317340830161072205192449 2488005622620804153894337)
                ·
                  refine ⟨1866004216965603115420753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488005622620804153894337 1866004216965603115420753)
                  ·
                    refine ⟨1399503162724202336565565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866004216965603115420753 1399503162724202336565565)
                    ·
                      refine ⟨524813686021575876212087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399503162724202336565565 524813686021575876212087)
                      ·
                        rfl

theorem cell23_1022071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1022071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022071 prefixEnd_1022071 := by exact prefixLift 1022071
  have htrace : WordTrace (prefixWord ++ tailWord_1022071) baseStart_1022071 baseEnd_1022071 := by
    simpa [prefixWord, tailWord_1022071, baseEnd_1022071] using wordTrace_append hprefix tailTrace_1022071
  have hstable : (prefixWord ++ tailWord_1022071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022071).length < 2 ^ (prefixWord ++ tailWord_1022071).sum := by decide
  have hdescent : baseEnd_1022071 < baseStart_1022071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022135 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 1, 1, 3]
def baseStart_1022135 : Nat := 118140960795 + 1022135 * 2 ^ 59
def prefixEnd_1022135 : Nat := 4983230072969 + 3 ^ 40 * 1022135 * 2
def baseEnd_1022135 : Nat := 524846548783463625811793

theorem tailTrace_1022135 : CollatzResearch.WordTrace tailWord_1022135 prefixEnd_1022135 524846548783463625811793 := by
  unfold tailWord_1022135
  simp only [CollatzResearch.WordTrace]
  refine ⟨37280326151986936605139859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24853550767991291070093239 37280326151986936605139859)
  ·
    refine ⟨55920489227980404907709789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37280326151986936605139859 55920489227980404907709789)
    ·
      refine ⟨20970183460492651840391171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55920489227980404907709789 20970183460492651840391171)
      ·
        refine ⟨31455275190738977760586757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970183460492651840391171 31455275190738977760586757)
        ·
          refine ⟨5897864098263558330110017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31455275190738977760586757 5897864098263558330110017)
          ·
            refine ⟨4423398073697668747582513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897864098263558330110017 4423398073697668747582513)
            ·
              refine ⟨3317548555273251560686885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423398073697668747582513 3317548555273251560686885)
              ·
                refine ⟨622040354113734667628791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3317548555273251560686885 622040354113734667628791)
                ·
                  refine ⟨933060531170602001443187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622040354113734667628791 933060531170602001443187)
                  ·
                    refine ⟨1399590796755903002164781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 933060531170602001443187 1399590796755903002164781)
                    ·
                      refine ⟨524846548783463625811793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399590796755903002164781 524846548783463625811793)
                      ·
                        rfl

theorem cell23_1022135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_1022135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022135 prefixEnd_1022135 := by exact prefixLift 1022135
  have htrace : WordTrace (prefixWord ++ tailWord_1022135) baseStart_1022135 baseEnd_1022135 := by
    simpa [prefixWord, tailWord_1022135, baseEnd_1022135] using wordTrace_append hprefix tailTrace_1022135
  have hstable : (prefixWord ++ tailWord_1022135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022135).length < 2 ^ (prefixWord ++ tailWord_1022135).sum := by decide
  have hdescent : baseEnd_1022135 < baseStart_1022135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022158 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_1022158 : Nat := 118140960795 + 1022158 * 2 ^ 59
def prefixEnd_1022158 : Nat := 4983230072969 + 3 ^ 40 * 1022158 * 2
def baseEnd_1022158 : Nat := 524858358838517035824187

theorem tailTrace_1022158 : CollatzResearch.WordTrace tailWord_1022158 prefixEnd_1022158 524858358838517035824187 := by
  unfold tailWord_1022158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660145628862951441653391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24854110020602407688818085 4660145628862951441653391)
  ·
    refine ⟨6990218443294427162480087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660145628862951441653391 6990218443294427162480087)
    ·
      refine ⟨10485327664941640743720131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990218443294427162480087 10485327664941640743720131)
      ·
        refine ⟨15727991497412461115580197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485327664941640743720131 15727991497412461115580197)
        ·
          refine ⟨2948998405764836459171287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15727991497412461115580197 2948998405764836459171287)
          ·
            refine ⟨4423497608647254688756931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948998405764836459171287 4423497608647254688756931)
            ·
              refine ⟨6635246412970882033135397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423497608647254688756931 6635246412970882033135397)
              ·
                refine ⟨1244108702432040381212887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6635246412970882033135397 1244108702432040381212887)
                ·
                  refine ⟨1866163053648060571819331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244108702432040381212887 1866163053648060571819331)
                  ·
                    refine ⟨2799244580472090857728997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1866163053648060571819331 2799244580472090857728997)
                    ·
                      refine ⟨524858358838517035824187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2799244580472090857728997 524858358838517035824187)
                      ·
                        rfl

theorem cell23_1022158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_1022158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022158 prefixEnd_1022158 := by exact prefixLift 1022158
  have htrace : WordTrace (prefixWord ++ tailWord_1022158) baseStart_1022158 baseEnd_1022158 := by
    simpa [prefixWord, tailWord_1022158, baseEnd_1022158] using wordTrace_append hprefix tailTrace_1022158
  have hstable : (prefixWord ++ tailWord_1022158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022158).length < 2 ^ (prefixWord ++ tailWord_1022158).sum := by decide
  have hdescent : baseEnd_1022158 < baseStart_1022158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022161 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_1022161 : Nat := 118140960795 + 1022161 * 2 ^ 59
def prefixEnd_1022161 : Nat := 4983230072969 + 3 ^ 40 * 1022161 * 2
def baseEnd_1022161 : Nat := 524859899280480524086673

theorem tailTrace_1022161 : CollatzResearch.WordTrace tailWord_1022161 prefixEnd_1022161 524859899280480524086673 := by
  unfold tailWord_1022161
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281274449892743045586337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24854182966595162030390891 37281274449892743045586337)
  ·
    refine ⟨27960955837419557284189753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37281274449892743045586337 27960955837419557284189753)
    ·
      refine ⟨20970716878064667963142315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27960955837419557284189753 20970716878064667963142315)
      ·
        refine ⟨31456075317097001944713473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970716878064667963142315 31456075317097001944713473)
        ·
          refine ⟨23592056487822751458535105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31456075317097001944713473 23592056487822751458535105)
          ·
            refine ⟨17694042365867063593901329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23592056487822751458535105 17694042365867063593901329)
            ·
              refine ⟨13270531774400297695425997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17694042365867063593901329 13270531774400297695425997)
              ·
                refine ⟨4976449415400111635784749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270531774400297695425997 4976449415400111635784749)
                ·
                  refine ⟨1866168530775041863419281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4976449415400111635784749 1866168530775041863419281)
                  ·
                    refine ⟨1399626398081281397564461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866168530775041863419281 1399626398081281397564461)
                    ·
                      refine ⟨524859899280480524086673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399626398081281397564461 524859899280480524086673)
                      ·
                        rfl

theorem cell23_1022161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_1022161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022161 prefixEnd_1022161 := by exact prefixLift 1022161
  have htrace : WordTrace (prefixWord ++ tailWord_1022161) baseStart_1022161 baseEnd_1022161 := by
    simpa [prefixWord, tailWord_1022161, baseEnd_1022161] using wordTrace_append hprefix tailTrace_1022161
  have hstable : (prefixWord ++ tailWord_1022161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022161).length < 2 ^ (prefixWord ++ tailWord_1022161).sum := by decide
  have hdescent : baseEnd_1022161 < baseStart_1022161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022181 : List Nat := [1, 3, 1, 4, 2, 3, 9]
def baseStart_1022181 : Nat := 118140960795 + 1022181 * 2 ^ 59
def prefixEnd_1022181 : Nat := 4983230072969 + 3 ^ 40 * 1022181 * 2
def baseEnd_1022181 : Nat := 6479878628315684516501

theorem tailTrace_1022181 : CollatzResearch.WordTrace tailWord_1022181 prefixEnd_1022181 6479878628315684516501 := by
  unfold tailWord_1022181
  simp only [CollatzResearch.WordTrace]
  refine ⟨37282003909820286461314397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24854669273213524307542931 37282003909820286461314397)
  ·
    refine ⟨13980751466182607422992899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37282003909820286461314397 13980751466182607422992899)
    ·
      refine ⟨20971127199273911134489349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980751466182607422992899 20971127199273911134489349)
      ·
        refine ⟨3932086349863858337716753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20971127199273911134489349 3932086349863858337716753)
        ·
          refine ⟨2949064762397893753287565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932086349863858337716753 2949064762397893753287565)
          ·
            refine ⟨1105899285899210157482837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2949064762397893753287565 1105899285899210157482837)
            ·
              refine ⟨6479878628315684516501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1105899285899210157482837 6479878628315684516501)
              ·
                rfl

theorem cell23_1022181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 9].length) (baseStart_1022181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022181 prefixEnd_1022181 := by exact prefixLift 1022181
  have htrace : WordTrace (prefixWord ++ tailWord_1022181) baseStart_1022181 baseEnd_1022181 := by
    simpa [prefixWord, tailWord_1022181, baseEnd_1022181] using wordTrace_append hprefix tailTrace_1022181
  have hstable : (prefixWord ++ tailWord_1022181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022181).length < 2 ^ (prefixWord ++ tailWord_1022181).sum := by decide
  have hdescent : baseEnd_1022181 < baseStart_1022181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022212 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1022212 : Nat := 118140960795 + 1022212 * 2 ^ 59
def prefixEnd_1022212 : Nat := 4983230072969 + 3 ^ 40 * 1022212 * 2
def baseEnd_1022212 : Nat := 524886086793859824548939

theorem tailTrace_1022212 : CollatzResearch.WordTrace tailWord_1022212 prefixEnd_1022212 524886086793859824548939 := by
  unfold tailWord_1022212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18641567286353989377846445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24855423048471985837128593 18641567286353989377846445)
  ·
    refine ⟨6990587732382746016692417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18641567286353989377846445 6990587732382746016692417)
    ·
      refine ⟨5242940799287059512519313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6990587732382746016692417 5242940799287059512519313)
      ·
        refine ⟨3932205599465294634389485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242940799287059512519313 3932205599465294634389485)
        ·
          refine ⟨1474577099799485487896057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3932205599465294634389485 1474577099799485487896057)
          ·
            refine ⟨1105932824849614115922043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474577099799485487896057 1105932824849614115922043)
            ·
              refine ⟨1658899237274421173883065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105932824849614115922043 1658899237274421173883065)
              ·
                refine ⟨1244174427955815880412299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658899237274421173883065 1244174427955815880412299)
                ·
                  refine ⟨1866261641933723820618449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244174427955815880412299 1866261641933723820618449)
                  ·
                    refine ⟨1399696231450292865463837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866261641933723820618449 1399696231450292865463837)
                    ·
                      refine ⟨524886086793859824548939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399696231450292865463837 524886086793859824548939)
                      ·
                        rfl

theorem cell23_1022212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1022212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022212 prefixEnd_1022212 := by exact prefixLift 1022212
  have htrace : WordTrace (prefixWord ++ tailWord_1022212) baseStart_1022212 baseEnd_1022212 := by
    simpa [prefixWord, tailWord_1022212, baseEnd_1022212] using wordTrace_append hprefix tailTrace_1022212
  have hstable : (prefixWord ++ tailWord_1022212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022212).length < 2 ^ (prefixWord ++ tailWord_1022212).sum := by decide
  have hdescent : baseEnd_1022212 < baseStart_1022212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022242 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1022242 : Nat := 118140960795 + 1022242 * 2 ^ 59
def prefixEnd_1022242 : Nat := 4983230072969 + 3 ^ 40 * 1022242 * 2
def baseEnd_1022242 : Nat := 524901491213494707173801

theorem tailTrace_1022242 : CollatzResearch.WordTrace tailWord_1022242 prefixEnd_1022242 524901491213494707173801 := by
  unfold tailWord_1022242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321057190649823469821245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24856152508399529252856653 9321057190649823469821245)
  ·
    refine ⟨3495396446493683801182967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9321057190649823469821245 3495396446493683801182967)
    ·
      refine ⟨5243094669740525701774451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495396446493683801182967 5243094669740525701774451)
      ·
        refine ⟨7864642004610788552661677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243094669740525701774451 7864642004610788552661677)
        ·
          refine ⟨2949240751729045707248129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7864642004610788552661677 2949240751729045707248129)
          ·
            refine ⟨2211930563796784280436097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949240751729045707248129 2211930563796784280436097)
            ·
              refine ⟨1658947922847588210327073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211930563796784280436097 1658947922847588210327073)
              ·
                refine ⟨1244210942135691157745305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658947922847588210327073 1244210942135691157745305)
                ·
                  refine ⟨933158206601768368308979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1244210942135691157745305 933158206601768368308979)
                  ·
                    refine ⟨1399737309902652552463469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 933158206601768368308979 1399737309902652552463469)
                    ·
                      refine ⟨524901491213494707173801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399737309902652552463469 524901491213494707173801)
                      ·
                        rfl

theorem cell23_1022242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1022242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022242 prefixEnd_1022242 := by exact prefixLift 1022242
  have htrace : WordTrace (prefixWord ++ tailWord_1022242) baseStart_1022242 baseEnd_1022242 := by
    simpa [prefixWord, tailWord_1022242, baseEnd_1022242] using wordTrace_append hprefix tailTrace_1022242
  have hstable : (prefixWord ++ tailWord_1022242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022242).length < 2 ^ (prefixWord ++ tailWord_1022242).sum := by decide
  have hdescent : baseEnd_1022242 < baseStart_1022242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022258 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1022258 : Nat := 118140960795 + 1022258 * 2 ^ 59
def prefixEnd_1022258 : Nat := 4983230072969 + 3 ^ 40 * 1022258 * 2
def baseEnd_1022258 : Nat := 174969902301322214857909

theorem tailTrace_1022258 : CollatzResearch.WordTrace tailWord_1022258 prefixEnd_1022258 174969902301322214857909 := by
  unfold tailWord_1022258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321203082635332152966857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24856541553694219074578285 9321203082635332152966857)
  ·
    refine ⟨6990902311976499114725143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9321203082635332152966857 6990902311976499114725143)
    ·
      refine ⟨10486353467964748672087715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990902311976499114725143 10486353467964748672087715)
      ·
        refine ⟨15729530201947123008131573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10486353467964748672087715 15729530201947123008131573)
        ·
          refine ⟨1474643456432542782012335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15729530201947123008131573 1474643456432542782012335)
          ·
            refine ⟨2211965184648814173018503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474643456432542782012335 2211965184648814173018503)
            ·
              refine ⟨3317947776973221259527755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211965184648814173018503 3317947776973221259527755)
              ·
                refine ⟨4976921665459831889291633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317947776973221259527755 4976921665459831889291633)
                ·
                  refine ⟨3732691249094873916968725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976921665459831889291633 3732691249094873916968725)
                  ·
                    refine ⟨174969902301322214857909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3732691249094873916968725 174969902301322214857909)
                    ·
                      rfl

theorem cell23_1022258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1022258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022258 prefixEnd_1022258 := by exact prefixLift 1022258
  have htrace : WordTrace (prefixWord ++ tailWord_1022258) baseStart_1022258 baseEnd_1022258 := by
    simpa [prefixWord, tailWord_1022258, baseEnd_1022258] using wordTrace_append hprefix tailTrace_1022258
  have hstable : (prefixWord ++ tailWord_1022258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022258).length < 2 ^ (prefixWord ++ tailWord_1022258).sum := by decide
  have hdescent : baseEnd_1022258 < baseStart_1022258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022265 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1022265 : Nat := 118140960795 + 1022265 * 2 ^ 59
def prefixEnd_1022265 : Nat := 4983230072969 + 3 ^ 40 * 1022265 * 2
def baseEnd_1022265 : Nat := 524913301268548117186195

theorem tailTrace_1022265 : CollatzResearch.WordTrace tailWord_1022265 prefixEnd_1022265 524913301268548117186195 := by
  unfold tailWord_1022265
  simp only [CollatzResearch.WordTrace]
  refine ⟨37285067641515968807372249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24856711761010645871581499 37285067641515968807372249)
  ·
    refine ⟨27963800731136976605529187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37285067641515968807372249 27963800731136976605529187)
    ·
      refine ⟨41945701096705464908293781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27963800731136976605529187 41945701096705464908293781)
      ·
        refine ⟨1966204738908068667576271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41945701096705464908293781 1966204738908068667576271)
        ·
          refine ⟨2949307108362103001364407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966204738908068667576271 2949307108362103001364407)
          ·
            refine ⟨4423960662543154502046611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949307108362103001364407 4423960662543154502046611)
            ·
              refine ⟨6635940993814731753069917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423960662543154502046611 6635940993814731753069917)
              ·
                refine ⟨2488477872680524407401219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635940993814731753069917 2488477872680524407401219)
                ·
                  refine ⟨3732716809020786611101829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488477872680524407401219 3732716809020786611101829)
                  ·
                    refine ⟨699884401691397489581593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732716809020786611101829 699884401691397489581593)
                    ·
                      refine ⟨524913301268548117186195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 699884401691397489581593 524913301268548117186195)
                      ·
                        rfl

theorem cell23_1022265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1022265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022265 prefixEnd_1022265 := by exact prefixLift 1022265
  have htrace : WordTrace (prefixWord ++ tailWord_1022265) baseStart_1022265 baseEnd_1022265 := by
    simpa [prefixWord, tailWord_1022265, baseEnd_1022265] using wordTrace_append hprefix tailTrace_1022265
  have hstable : (prefixWord ++ tailWord_1022265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022265).length < 2 ^ (prefixWord ++ tailWord_1022265).sum := by decide
  have hdescent : baseEnd_1022265 < baseStart_1022265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022271 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 7]
def baseStart_1022271 : Nat := 118140960795 + 1022271 * 2 ^ 59
def prefixEnd_1022271 : Nat := 4983230072969 + 3 ^ 40 * 1022271 * 2
def baseEnd_1022271 : Nat := 58324042461386121523463

theorem tailTrace_1022271 : CollatzResearch.WordTrace tailWord_1022271 prefixEnd_1022271 58324042461386121523463 := by
  unfold tailWord_1022271
  simp only [CollatzResearch.WordTrace]
  refine ⟨37285286479494231832090667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24856857652996154554727111 37285286479494231832090667)
  ·
    refine ⟨55927929719241347748136001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37285286479494231832090667 55927929719241347748136001)
    ·
      refine ⟨41945947289431010811102001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55927929719241347748136001 41945947289431010811102001)
      ·
        refine ⟨31459460467073258108326501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41945947289431010811102001 31459460467073258108326501)
        ·
          refine ⟨5898648837576235895311219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31459460467073258108326501 5898648837576235895311219)
          ·
            refine ⟨8847973256364353842966829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898648837576235895311219 8847973256364353842966829)
            ·
              refine ⟨3317989971136632691112561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8847973256364353842966829 3317989971136632691112561)
              ·
                refine ⟨2488492478352474518334421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317989971136632691112561 2488492478352474518334421)
                ·
                  refine ⟨58324042461386121523463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2488492478352474518334421 58324042461386121523463)
                  ·
                    rfl

theorem cell23_1022271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 7].length) (baseStart_1022271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022271 prefixEnd_1022271 := by exact prefixLift 1022271
  have htrace : WordTrace (prefixWord ++ tailWord_1022271) baseStart_1022271 baseEnd_1022271 := by
    simpa [prefixWord, tailWord_1022271, baseEnd_1022271] using wordTrace_append hprefix tailTrace_1022271
  have hstable : (prefixWord ++ tailWord_1022271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022271).length < 2 ^ (prefixWord ++ tailWord_1022271).sum := by decide
  have hdescent : baseEnd_1022271 < baseStart_1022271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022281 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_1022281 : Nat := 118140960795 + 1022281 * 2 ^ 59
def prefixEnd_1022281 : Nat := 4983230072969 + 3 ^ 40 * 1022281 * 2
def baseEnd_1022281 : Nat := 524921516959020054586121

theorem tailTrace_1022281 : CollatzResearch.WordTrace tailWord_1022281 prefixEnd_1022281 524921516959020054586121 := by
  unfold tailWord_1022281
  simp only [CollatzResearch.WordTrace]
  refine ⟨37285651209458003539954697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24857100806305335693303131 37285651209458003539954697)
  ·
    refine ⟨27964238407093502654966023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37285651209458003539954697 27964238407093502654966023)
    ·
      refine ⟨41946357610640253982449035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27964238407093502654966023 41946357610640253982449035)
      ·
        refine ⟨62919536415960380973673553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41946357610640253982449035 62919536415960380973673553)
        ·
          refine ⟨47189652311970285730255165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62919536415960380973673553 47189652311970285730255165)
          ·
            refine ⟨17696119616988857148845687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47189652311970285730255165 17696119616988857148845687)
            ·
              refine ⟨26544179425483285723268531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17696119616988857148845687 26544179425483285723268531)
              ·
                refine ⟨39816269138224928584902797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26544179425483285723268531 39816269138224928584902797)
                ·
                  refine ⟨14931100926834348219338549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39816269138224928584902797 14931100926834348219338549)
                  ·
                    refine ⟨1399790711890720145562989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14931100926834348219338549 1399790711890720145562989)
                    ·
                      refine ⟨524921516959020054586121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1399790711890720145562989 524921516959020054586121)
                      ·
                        rfl

theorem cell23_1022281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_1022281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022281 prefixEnd_1022281 := by exact prefixLift 1022281
  have htrace : WordTrace (prefixWord ++ tailWord_1022281) baseStart_1022281 baseEnd_1022281 := by
    simpa [prefixWord, tailWord_1022281, baseEnd_1022281] using wordTrace_append hprefix tailTrace_1022281
  have hstable : (prefixWord ++ tailWord_1022281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022281).length < 2 ^ (prefixWord ++ tailWord_1022281).sum := by decide
  have hdescent : baseEnd_1022281 < baseStart_1022281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022288 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 5]
def baseStart_1022288 : Nat := 118140960795 + 1022288 * 2 ^ 59
def prefixEnd_1022288 : Nat := 4983230072969 + 3 ^ 40 * 1022288 * 2
def baseEnd_1022288 : Nat := 58325012369289058577621

theorem tailTrace_1022288 : CollatzResearch.WordTrace tailWord_1022288 prefixEnd_1022288 58325012369289058577621 := by
  unfold tailWord_1022288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18642953260216321867729759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24857271013621762490306345 18642953260216321867729759)
  ·
    refine ⟨27964429890324482801594639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18642953260216321867729759 27964429890324482801594639)
    ·
      refine ⟨41946644835486724202391959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27964429890324482801594639 41946644835486724202391959)
      ·
        refine ⟨62919967253230086303587939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41946644835486724202391959 62919967253230086303587939)
        ·
          refine ⟨94379950879845129455381909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62919967253230086303587939 94379950879845129455381909)
          ·
            refine ⟨4424060197492740443221027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94379950879845129455381909 4424060197492740443221027)
            ·
              refine ⟨6636090296239110664831541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424060197492740443221027 6636090296239110664831541)
              ·
                refine ⟨622133465272416624827957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6636090296239110664831541 622133465272416624827957)
                ·
                  refine ⟨58325012369289058577621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622133465272416624827957 58325012369289058577621)
                  ·
                    rfl

theorem cell23_1022288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 5].length) (baseStart_1022288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022288 prefixEnd_1022288 := by exact prefixLift 1022288
  have htrace : WordTrace (prefixWord ++ tailWord_1022288) baseStart_1022288 baseEnd_1022288 := by
    simpa [prefixWord, tailWord_1022288, baseEnd_1022288] using wordTrace_append hprefix tailTrace_1022288
  have hstable : (prefixWord ++ tailWord_1022288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022288).length < 2 ^ (prefixWord ++ tailWord_1022288).sum := by decide
  have hdescent : baseEnd_1022288 < baseStart_1022288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022341 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_1022341 : Nat := 118140960795 + 1022341 * 2 ^ 59
def prefixEnd_1022341 : Nat := 4983230072969 + 3 ^ 40 * 1022341 * 2
def baseEnd_1022341 : Nat := 524952325798289819835845

theorem tailTrace_1022341 : CollatzResearch.WordTrace tailWord_1022341 prefixEnd_1022341 524952325798289819835845 := by
  unfold tailWord_1022341
  simp only [CollatzResearch.WordTrace]
  refine ⟨37287839589240633787138877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24858559726160422524759251 37287839589240633787138877)
  ·
    refine ⟨13982939845965237670177079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37287839589240633787138877 13982939845965237670177079)
    ·
      refine ⟨20974409768947856505265619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13982939845965237670177079 20974409768947856505265619)
      ·
        refine ⟨31461614653421784757898429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20974409768947856505265619 31461614653421784757898429)
        ·
          refine ⟨11798105495033169284211911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31461614653421784757898429 11798105495033169284211911)
          ·
            refine ⟨17697158242549753926317867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798105495033169284211911 17697158242549753926317867)
            ·
              refine ⟨26545737363824630889476801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17697158242549753926317867 26545737363824630889476801)
              ·
                refine ⟨19909303022868473167107601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26545737363824630889476801 19909303022868473167107601)
                ·
                  refine ⟨14931977267151354875330701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19909303022868473167107601 14931977267151354875330701)
                  ·
                    refine ⟨5599491475181758078249013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14931977267151354875330701 5599491475181758078249013)
                    ·
                      refine ⟨524952325798289819835845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5599491475181758078249013 524952325798289819835845)
                      ·
                        rfl

theorem cell23_1022341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_1022341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022341 prefixEnd_1022341 := by exact prefixLift 1022341
  have htrace : WordTrace (prefixWord ++ tailWord_1022341) baseStart_1022341 baseEnd_1022341 := by
    simpa [prefixWord, tailWord_1022341, baseEnd_1022341] using wordTrace_append hprefix tailTrace_1022341
  have hstable : (prefixWord ++ tailWord_1022341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022341).length < 2 ^ (prefixWord ++ tailWord_1022341).sum := by decide
  have hdescent : baseEnd_1022341 < baseStart_1022341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022361 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 8]
def baseStart_1022361 : Nat := 118140960795 + 1022361 * 2 ^ 59
def prefixEnd_1022361 : Nat := 4983230072969 + 3 ^ 40 * 1022361 * 2
def baseEnd_1022361 : Nat := 58329177267931082398417

theorem tailTrace_1022361 : CollatzResearch.WordTrace tailWord_1022361 prefixEnd_1022361 58329177267931082398417 := by
  unfold tailWord_1022361
  simp only [CollatzResearch.WordTrace]
  refine ⟨37288569049168177202866937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24859046032778784801911291 37288569049168177202866937)
  ·
    refine ⟨27966426786876132902150203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37288569049168177202866937 27966426786876132902150203)
    ·
      refine ⟨41949640180314199353225305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27966426786876132902150203 41949640180314199353225305)
      ·
        refine ⟨31462230135235649514918979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41949640180314199353225305 31462230135235649514918979)
        ·
          refine ⟨47193345202853474272378469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31462230135235649514918979 47193345202853474272378469)
          ·
            refine ⟨8848752225535026426070963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47193345202853474272378469 8848752225535026426070963)
            ·
              refine ⟨13273128338302539639106445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848752225535026426070963 13273128338302539639106445)
              ·
                refine ⟨4977423126863452364664917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13273128338302539639106445 4977423126863452364664917)
                ·
                  refine ⟨58329177267931082398417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4977423126863452364664917 58329177267931082398417)
                  ·
                    rfl

theorem cell23_1022361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_1022361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022361 prefixEnd_1022361 := by exact prefixLift 1022361
  have htrace : WordTrace (prefixWord ++ tailWord_1022361) baseStart_1022361 baseEnd_1022361 := by
    simpa [prefixWord, tailWord_1022361, baseEnd_1022361] using wordTrace_append hprefix tailTrace_1022361
  have hstable : (prefixWord ++ tailWord_1022361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022361).length < 2 ^ (prefixWord ++ tailWord_1022361).sum := by decide
  have hdescent : baseEnd_1022361 < baseStart_1022361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022458 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1022458 : Nat := 118140960795 + 1022458 * 2 ^ 59
def prefixEnd_1022458 : Nat := 4983230072969 + 3 ^ 40 * 1022458 * 2
def baseEnd_1022458 : Nat := 525012403034865862072807

theorem tailTrace_1022458 : CollatzResearch.WordTrace tailWord_1022458 prefixEnd_1022458 525012403034865862072807 := by
  unfold tailWord_1022458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323026732454190692287007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24861404619877841846098685 9323026732454190692287007)
  ·
    refine ⟨13984540098681286038430511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9323026732454190692287007 13984540098681286038430511)
    ·
      refine ⟨20976810148021929057645767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13984540098681286038430511 20976810148021929057645767)
      ·
        refine ⟨31465215222032893586468651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20976810148021929057645767 31465215222032893586468651)
        ·
          refine ⟨47197822833049340379702977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31465215222032893586468651 47197822833049340379702977)
          ·
            refine ⟨35398367124787005284777233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47197822833049340379702977 35398367124787005284777233)
            ·
              refine ⟨26548775343590253963582925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35398367124787005284777233 26548775343590253963582925)
              ·
                refine ⟨9955790753846345236343597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26548775343590253963582925 9955790753846345236343597)
                ·
                  refine ⟨3733421532692379463628849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9955790753846345236343597 3733421532692379463628849)
                  ·
                    refine ⟨2800066149519284597721637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3733421532692379463628849 2800066149519284597721637)
                    ·
                      refine ⟨525012403034865862072807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2800066149519284597721637 525012403034865862072807)
                      ·
                        rfl

theorem cell23_1022458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1022458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022458 prefixEnd_1022458 := by exact prefixLift 1022458
  have htrace : WordTrace (prefixWord ++ tailWord_1022458) baseStart_1022458 baseEnd_1022458 := by
    simpa [prefixWord, tailWord_1022458, baseEnd_1022458] using wordTrace_append hprefix tailTrace_1022458
  have hstable : (prefixWord ++ tailWord_1022458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022458).length < 2 ^ (prefixWord ++ tailWord_1022458).sum := by decide
  have hdescent : baseEnd_1022458 < baseStart_1022458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022492 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1022492 : Nat := 118140960795 + 1022492 * 2 ^ 59
def prefixEnd_1022492 : Nat := 4983230072969 + 3 ^ 40 * 1022492 * 2
def baseEnd_1022492 : Nat := 525029861377118729047651

theorem tailTrace_1022492 : CollatzResearch.WordTrace tailWord_1022492 prefixEnd_1022492 525029861377118729047651 := by
  unfold tailWord_1022492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646673505846793287942865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24862231341129057717257153 18646673505846793287942865)
  ·
    refine ⟨13985005129385094965957149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18646673505846793287942865 13985005129385094965957149)
    ·
      refine ⟨5244376923519410612233931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13985005129385094965957149 5244376923519410612233931)
      ·
        refine ⟨7866565385279115918350897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244376923519410612233931 7866565385279115918350897)
        ·
          refine ⟨5899924038959336938763173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7866565385279115918350897 5899924038959336938763173)
          ·
            refine ⟨1106235757304875676018095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5899924038959336938763173 1106235757304875676018095)
            ·
              refine ⟨1659353635957313514027143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106235757304875676018095 1659353635957313514027143)
              ·
                refine ⟨2489030453935970271040715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659353635957313514027143 2489030453935970271040715)
                ·
                  refine ⟨3733545680903955406561073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489030453935970271040715 3733545680903955406561073)
                  ·
                    refine ⟨2800159260677966554920805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3733545680903955406561073 2800159260677966554920805)
                    ·
                      refine ⟨525029861377118729047651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2800159260677966554920805 525029861377118729047651)
                      ·
                        rfl

theorem cell23_1022492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1022492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022492 prefixEnd_1022492 := by exact prefixLift 1022492
  have htrace : WordTrace (prefixWord ++ tailWord_1022492) baseStart_1022492 baseEnd_1022492 := by
    simpa [prefixWord, tailWord_1022492, baseEnd_1022492] using wordTrace_append hprefix tailTrace_1022492
  have hstable : (prefixWord ++ tailWord_1022492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022492).length < 2 ^ (prefixWord ++ tailWord_1022492).sum := by decide
  have hdescent : baseEnd_1022492 < baseStart_1022492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022528 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_1022528 : Nat := 118140960795 + 1022528 * 2 ^ 59
def prefixEnd_1022528 : Nat := 4983230072969 + 3 ^ 40 * 1022528 * 2
def baseEnd_1022528 : Nat := 175016115560226862732495

theorem tailTrace_1022528 : CollatzResearch.WordTrace tailWord_1022528 prefixEnd_1022528 175016115560226862732495 := by
  unfold tailWord_1022528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18647330019781582362098119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24863106693042109816130825 18647330019781582362098119)
  ·
    refine ⟨27970995029672373543147179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18647330019781582362098119 27970995029672373543147179)
    ·
      refine ⟨41956492544508560314720769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27970995029672373543147179 41956492544508560314720769)
      ·
        refine ⟨31467369408381420236040577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41956492544508560314720769 31467369408381420236040577)
        ·
          refine ⟨23600527056286065177030433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31467369408381420236040577 23600527056286065177030433)
          ·
            refine ⟨17700395292214548882772825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23600527056286065177030433 17700395292214548882772825)
            ·
              refine ⟨13275296469160911662079619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17700395292214548882772825 13275296469160911662079619)
              ·
                refine ⟨19912944703741367493119429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275296469160911662079619 19912944703741367493119429)
                ·
                  refine ⟨3733677131951506404959893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19912944703741367493119429 3733677131951506404959893)
                  ·
                    refine ⟨175016115560226862732495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3733677131951506404959893 175016115560226862732495)
                    ·
                      rfl

theorem cell23_1022528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_1022528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022528 prefixEnd_1022528 := by exact prefixLift 1022528
  have htrace : WordTrace (prefixWord ++ tailWord_1022528) baseStart_1022528 baseEnd_1022528 := by
    simpa [prefixWord, tailWord_1022528, baseEnd_1022528] using wordTrace_append hprefix tailTrace_1022528
  have hstable : (prefixWord ++ tailWord_1022528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022528).length < 2 ^ (prefixWord ++ tailWord_1022528).sum := by decide
  have hdescent : baseEnd_1022528 < baseStart_1022528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022592 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 5]
def baseStart_1022592 : Nat := 118140960795 + 1022592 * 2 ^ 59
def prefixEnd_1022592 : Nat := 4983230072969 + 3 ^ 40 * 1022592 * 2
def baseEnd_1022592 : Nat := 58342356604729815310799

theorem tailTrace_1022592 : CollatzResearch.WordTrace tailWord_1022592 prefixEnd_1022592 58342356604729815310799 := by
  unfold tailWord_1022592
  simp only [CollatzResearch.WordTrace]
  refine ⟨18648497155665651827263015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24864662874220869103017353 18648497155665651827263015)
  ·
    refine ⟨27972745733498477740894523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18648497155665651827263015 27972745733498477740894523)
    ·
      refine ⟨41959118600247716611341785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972745733498477740894523 41959118600247716611341785)
      ·
        refine ⟨31469338950185787458506339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41959118600247716611341785 31469338950185787458506339)
        ·
          refine ⟨47204008425278681187759509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31469338950185787458506339 47204008425278681187759509)
          ·
            refine ⟨2212687894934938180676227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47204008425278681187759509 2212687894934938180676227)
            ·
              refine ⟨3319031842402407271014341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212687894934938180676227 3319031842402407271014341)
              ·
                refine ⟨622318470450451363315189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3319031842402407271014341 622318470450451363315189)
                ·
                  refine ⟨58342356604729815310799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622318470450451363315189 58342356604729815310799)
                  ·
                    rfl

theorem cell23_1022592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 5].length) (baseStart_1022592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022592 prefixEnd_1022592 := by exact prefixLift 1022592
  have htrace : WordTrace (prefixWord ++ tailWord_1022592) baseStart_1022592 baseEnd_1022592 := by
    simpa [prefixWord, tailWord_1022592, baseEnd_1022592] using wordTrace_append hprefix tailTrace_1022592
  have hstable : (prefixWord ++ tailWord_1022592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022592).length < 2 ^ (prefixWord ++ tailWord_1022592).sum := by decide
  have hdescent : baseEnd_1022592 < baseStart_1022592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022622 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1022622 : Nat := 118140960795 + 1022622 * 2 ^ 59
def prefixEnd_1022622 : Nat := 4983230072969 + 3 ^ 40 * 1022622 * 2
def baseEnd_1022622 : Nat := 175032204620734406807351

theorem tailTrace_1022622 : CollatzResearch.WordTrace tailWord_1022622 prefixEnd_1022622 175032204620734406807351 := by
  unfold tailWord_1022622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662261062652827347264765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24865392334148412518745413 4662261062652827347264765)
  ·
    refine ⟨1748347898494810255224287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4662261062652827347264765 1748347898494810255224287)
    ·
      refine ⟨2622521847742215382836431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748347898494810255224287 2622521847742215382836431)
      ·
        refine ⟨3933782771613323074254647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622521847742215382836431 3933782771613323074254647)
        ·
          refine ⟨5900674157419984611381971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933782771613323074254647 5900674157419984611381971)
          ·
            refine ⟨8851011236129976917072957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900674157419984611381971 8851011236129976917072957)
            ·
              refine ⟨3319129213548741343902359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8851011236129976917072957 3319129213548741343902359)
              ·
                refine ⟨4978693820323112015853539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319129213548741343902359 4978693820323112015853539)
                ·
                  refine ⟨7468040730484668023780309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978693820323112015853539 7468040730484668023780309)
                  ·
                    refine ⟨175032204620734406807351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7468040730484668023780309 175032204620734406807351)
                    ·
                      rfl

theorem cell23_1022622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1022622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022622 prefixEnd_1022622 := by exact prefixLift 1022622
  have htrace : WordTrace (prefixWord ++ tailWord_1022622) baseStart_1022622 baseEnd_1022622 := by
    simpa [prefixWord, tailWord_1022622, baseEnd_1022622] using wordTrace_append hprefix tailTrace_1022622
  have hstable : (prefixWord ++ tailWord_1022622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022622).length < 2 ^ (prefixWord ++ tailWord_1022622).sum := by decide
  have hdescent : baseEnd_1022622 < baseStart_1022622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022725 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_1022725 : Nat := 118140960795 + 1022725 * 2 ^ 59
def prefixEnd_1022725 : Nat := 4983230072969 + 3 ^ 40 * 1022725 * 2
def baseEnd_1022725 : Nat := 175049834123205439144693

theorem tailTrace_1022725 : CollatzResearch.WordTrace tailWord_1022725 prefixEnd_1022725 175049834123205439144693 := by
  unfold tailWord_1022725
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301845219849467369117629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24867896813232978246078419 37301845219849467369117629)
  ·
    refine ⟨13988191957443550263419111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37301845219849467369117629 13988191957443550263419111)
    ·
      refine ⟨20982287936165325395128667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13988191957443550263419111 20982287936165325395128667)
      ·
        refine ⟨31473431904247988092693001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20982287936165325395128667 31473431904247988092693001)
        ·
          refine ⟨23605073928185991069519751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31473431904247988092693001 23605073928185991069519751)
          ·
            refine ⟨35407610892278986604279627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605073928185991069519751 35407610892278986604279627)
            ·
              refine ⟨53111416338418479906419441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35407610892278986604279627 53111416338418479906419441)
              ·
                refine ⟨39833562253813859929814581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53111416338418479906419441 39833562253813859929814581)
                ·
                  refine ⟨3734396461295049368420117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39833562253813859929814581 3734396461295049368420117)
                  ·
                    refine ⟨175049834123205439144693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3734396461295049368420117 175049834123205439144693)
                    ·
                      rfl

theorem cell23_1022725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_1022725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022725 prefixEnd_1022725 := by exact prefixLift 1022725
  have htrace : WordTrace (prefixWord ++ tailWord_1022725) baseStart_1022725 baseEnd_1022725 := by
    simpa [prefixWord, tailWord_1022725, baseEnd_1022725] using wordTrace_append hprefix tailTrace_1022725
  have hstable : (prefixWord ++ tailWord_1022725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022725).length < 2 ^ (prefixWord ++ tailWord_1022725).sum := by decide
  have hdescent : baseEnd_1022725 < baseStart_1022725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022745 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1022745 : Nat := 118140960795 + 1022745 * 2 ^ 59
def prefixEnd_1022745 : Nat := 4983230072969 + 3 ^ 40 * 1022745 * 2
def baseEnd_1022745 : Nat := 525159771982706239183987

theorem tailTrace_1022745 : CollatzResearch.WordTrace tailWord_1022745 prefixEnd_1022745 525159771982706239183987 := by
  unfold tailWord_1022745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37302574679777010784845689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24868383119851340523230459 37302574679777010784845689)
  ·
    refine ⟨27976931009832758088634267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37302574679777010784845689 27976931009832758088634267)
    ·
      refine ⟨41965396514749137132951401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27976931009832758088634267 41965396514749137132951401)
      ·
        refine ⟨31474047386061852849713551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41965396514749137132951401 31474047386061852849713551)
        ·
          refine ⟨47211071079092779274570327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31474047386061852849713551 47211071079092779274570327)
          ·
            refine ⟨70816606618639168911855491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47211071079092779274570327 70816606618639168911855491)
            ·
              refine ⟨106224909927958753367783237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70816606618639168911855491 106224909927958753367783237)
              ·
                refine ⟨19917170611492266256459357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106224909927958753367783237 19917170611492266256459357)
                ·
                  refine ⟨7468938979309599846172259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19917170611492266256459357 7468938979309599846172259)
                  ·
                    refine ⟨11203408468964399769258389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7468938979309599846172259 11203408468964399769258389)
                    ·
                      refine ⟨525159771982706239183987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11203408468964399769258389 525159771982706239183987)
                      ·
                        rfl

theorem cell23_1022745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1022745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022745 prefixEnd_1022745 := by exact prefixLift 1022745
  have htrace : WordTrace (prefixWord ++ tailWord_1022745) baseStart_1022745 baseEnd_1022745 := by
    simpa [prefixWord, tailWord_1022745, baseEnd_1022745] using wordTrace_append hprefix tailTrace_1022745
  have hstable : (prefixWord ++ tailWord_1022745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022745).length < 2 ^ (prefixWord ++ tailWord_1022745).sum := by decide
  have hdescent : baseEnd_1022745 < baseStart_1022745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022832 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_1022832 : Nat := 118140960795 + 1022832 * 2 ^ 59
def prefixEnd_1022832 : Nat := 4983230072969 + 3 ^ 40 * 1022832 * 2
def baseEnd_1022832 : Nat := 175068148266549132932029

theorem tailTrace_1022832 : CollatzResearch.WordTrace tailWord_1022832 prefixEnd_1022832 175068148266549132932029 := by
  unfold tailWord_1022832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18652873915230912321631375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24870498553641216428841833 18652873915230912321631375)
  ·
    refine ⟨27979310872846368482447063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18652873915230912321631375 27979310872846368482447063)
    ·
      refine ⟨41968966309269552723670595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27979310872846368482447063 41968966309269552723670595)
      ·
        refine ⟨62953449463904329085505893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41968966309269552723670595 62953449463904329085505893)
        ·
          refine ⟨11803771774482061703532355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62953449463904329085505893 11803771774482061703532355)
          ·
            refine ⟨17705657661723092555298533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803771774482061703532355 17705657661723092555298533)
            ·
              refine ⟨3319810811573079854118475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17705657661723092555298533 3319810811573079854118475)
              ·
                refine ⟨4979716217359619781177713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319810811573079854118475 4979716217359619781177713)
                ·
                  refine ⟨3734787163019714835883285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979716217359619781177713 3734787163019714835883285)
                  ·
                    refine ⟨175068148266549132932029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3734787163019714835883285 175068148266549132932029)
                    ·
                      rfl

theorem cell23_1022832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_1022832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022832 prefixEnd_1022832 := by exact prefixLift 1022832
  have htrace : WordTrace (prefixWord ++ tailWord_1022832) baseStart_1022832 baseEnd_1022832 := by
    simpa [prefixWord, tailWord_1022832, baseEnd_1022832] using wordTrace_append hprefix tailTrace_1022832
  have hstable : (prefixWord ++ tailWord_1022832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022832).length < 2 ^ (prefixWord ++ tailWord_1022832).sum := by decide
  have hdescent : baseEnd_1022832 < baseStart_1022832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022833 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_1022833 : Nat := 118140960795 + 1022833 * 2 ^ 59
def prefixEnd_1022833 : Nat := 4983230072969 + 3 ^ 40 * 1022833 * 2
def baseEnd_1022833 : Nat := 525204958280301894883583

theorem tailTrace_1022833 : CollatzResearch.WordTrace tailWord_1022833 prefixEnd_1022833 525204958280301894883583 := by
  unfold tailWord_1022833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37305784303458201814049153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24870522868972134542699435 37305784303458201814049153)
  ·
    refine ⟨27979338227593651360536865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37305784303458201814049153 27979338227593651360536865)
    ·
      refine ⟨20984503670695238520402649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27979338227593651360536865 20984503670695238520402649)
      ·
        refine ⟨15738377753021428890301987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20984503670695238520402649 15738377753021428890301987)
        ·
          refine ⟨23607566629532143335452981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15738377753021428890301987 23607566629532143335452981)
          ·
            refine ⟨2213209371518638437698717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23607566629532143335452981 2213209371518638437698717)
            ·
              refine ⟨829953514319489414137019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213209371518638437698717 829953514319489414137019)
              ·
                refine ⟨1244930271479234121205529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829953514319489414137019 1244930271479234121205529)
                ·
                  refine ⟨933697703609425590904147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1244930271479234121205529 933697703609425590904147)
                  ·
                    refine ⟨1400546555414138386356221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 933697703609425590904147 1400546555414138386356221)
                    ·
                      refine ⟨525204958280301894883583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1400546555414138386356221 525204958280301894883583)
                      ·
                        rfl

theorem cell23_1022833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_1022833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022833 prefixEnd_1022833 := by exact prefixLift 1022833
  have htrace : WordTrace (prefixWord ++ tailWord_1022833) baseStart_1022833 baseEnd_1022833 := by
    simpa [prefixWord, tailWord_1022833, baseEnd_1022833] using wordTrace_append hprefix tailTrace_1022833
  have hstable : (prefixWord ++ tailWord_1022833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022833).length < 2 ^ (prefixWord ++ tailWord_1022833).sum := by decide
  have hdescent : baseEnd_1022833 < baseStart_1022833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022842 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1022842 : Nat := 118140960795 + 1022842 * 2 ^ 59
def prefixEnd_1022842 : Nat := 4983230072969 + 3 ^ 40 * 1022842 * 2
def baseEnd_1022842 : Nat := 525209579606192359671041

theorem tailTrace_1022842 : CollatzResearch.WordTrace tailWord_1022842 prefixEnd_1022842 525209579606192359671041 := by
  unfold tailWord_1022842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326528140106399087781695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24870741706950397567417853 9326528140106399087781695)
  ·
    refine ⟨13989792210159598631672543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9326528140106399087781695 13989792210159598631672543)
    ·
      refine ⟨20984688315239397947508815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13989792210159598631672543 20984688315239397947508815)
      ·
        refine ⟨31477032472859096921263223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984688315239397947508815 31477032472859096921263223)
        ·
          refine ⟨47215548709288645381894835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31477032472859096921263223 47215548709288645381894835)
          ·
            refine ⟨70823323063932968072842253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47215548709288645381894835 70823323063932968072842253)
            ·
              refine ⟨26558746148974863027315845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70823323063932968072842253 26558746148974863027315845)
              ·
                refine ⟨4979764902932786817621721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26558746148974863027315845 4979764902932786817621721)
                ·
                  refine ⟨3734823677199590113216291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979764902932786817621721 3734823677199590113216291)
                  ·
                    refine ⟨5602235515799385169824437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734823677199590113216291 5602235515799385169824437)
                    ·
                      refine ⟨525209579606192359671041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5602235515799385169824437 525209579606192359671041)
                      ·
                        rfl

theorem cell23_1022842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1022842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022842 prefixEnd_1022842 := by exact prefixLift 1022842
  have htrace : WordTrace (prefixWord ++ tailWord_1022842) baseStart_1022842 baseEnd_1022842 := by
    simpa [prefixWord, tailWord_1022842, baseEnd_1022842] using wordTrace_append hprefix tailTrace_1022842
  have hstable : (prefixWord ++ tailWord_1022842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022842).length < 2 ^ (prefixWord ++ tailWord_1022842).sum := by decide
  have hdescent : baseEnd_1022842 < baseStart_1022842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022879 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 7]
def baseStart_1022879 : Nat := 118140960795 + 1022879 * 2 ^ 59
def prefixEnd_1022879 : Nat := 4983230072969 + 3 ^ 40 * 1022879 * 2
def baseEnd_1022879 : Nat := 58358730932267634989819

theorem tailTrace_1022879 : CollatzResearch.WordTrace tailWord_1022879 prefixEnd_1022879 58358730932267634989819 := by
  unfold tailWord_1022879
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307462061291551670223691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24871641374194367780149127 37307462061291551670223691)
  ·
    refine ⟨55961193091937327505335537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37307462061291551670223691 55961193091937327505335537)
    ·
      refine ⟨41970894818952995629001653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55961193091937327505335537 41970894818952995629001653)
      ·
        refine ⟨3934771389276843340218905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41970894818952995629001653 3934771389276843340218905)
        ·
          refine ⟨2951078541957632505164179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934771389276843340218905 2951078541957632505164179)
          ·
            refine ⟨4426617812936448757746269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951078541957632505164179 4426617812936448757746269)
            ·
              refine ⟨1659981679851168284154851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4426617812936448757746269 1659981679851168284154851)
              ·
                refine ⟨2489972519776752426232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659981679851168284154851 2489972519776752426232277)
                ·
                  refine ⟨58358730932267634989819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2489972519776752426232277 58358730932267634989819)
                  ·
                    rfl

theorem cell23_1022879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 7].length) (baseStart_1022879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022879 prefixEnd_1022879 := by exact prefixLift 1022879
  have htrace : WordTrace (prefixWord ++ tailWord_1022879) baseStart_1022879 baseEnd_1022879 := by
    simpa [prefixWord, tailWord_1022879, baseEnd_1022879] using wordTrace_append hprefix tailTrace_1022879
  have hstable : (prefixWord ++ tailWord_1022879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022879).length < 2 ^ (prefixWord ++ tailWord_1022879).sum := by decide
  have hdescent : baseEnd_1022879 < baseStart_1022879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022899 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 5, 2]
def baseStart_1022899 : Nat := 118140960795 + 1022899 * 2 ^ 59
def prefixEnd_1022899 : Nat := 4983230072969 + 3 ^ 40 * 1022899 * 2
def baseEnd_1022899 : Nat := 525238848003498636658279

theorem tailTrace_1022899 : CollatzResearch.WordTrace tailWord_1022899 prefixEnd_1022899 525238848003498636658279 := by
  unfold tailWord_1022899
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308191521219095085951751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24872127680812730057301167 37308191521219095085951751)
  ·
    refine ⟨55962287281828642628927627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37308191521219095085951751 55962287281828642628927627)
    ·
      refine ⟨83943430922742963943391441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55962287281828642628927627 83943430922742963943391441)
      ·
        refine ⟨62957573192057222957543581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83943430922742963943391441 62957573192057222957543581)
        ·
          refine ⟨23609089947021458609078843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62957573192057222957543581 23609089947021458609078843)
          ·
            refine ⟨35413634920532187913618265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23609089947021458609078843 35413634920532187913618265)
            ·
              refine ⟨26560226190399140935213699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35413634920532187913618265 26560226190399140935213699)
              ·
                refine ⟨39840339285598711402820549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26560226190399140935213699 39840339285598711402820549)
                ·
                  refine ⟨7470063616049758388028853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39840339285598711402820549 7470063616049758388028853)
                  ·
                    refine ⟨700318464004664848877705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7470063616049758388028853 700318464004664848877705)
                    ·
                      refine ⟨525238848003498636658279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 700318464004664848877705 525238848003498636658279)
                      ·
                        rfl

theorem cell23_1022899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5, 2].length) (baseStart_1022899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022899 prefixEnd_1022899 := by exact prefixLift 1022899
  have htrace : WordTrace (prefixWord ++ tailWord_1022899) baseStart_1022899 baseEnd_1022899 := by
    simpa [prefixWord, tailWord_1022899, baseEnd_1022899] using wordTrace_append hprefix tailTrace_1022899
  have hstable : (prefixWord ++ tailWord_1022899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022899).length < 2 ^ (prefixWord ++ tailWord_1022899).sum := by decide
  have hdescent : baseEnd_1022899 < baseStart_1022899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022929 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_1022929 : Nat := 118140960795 + 1022929 * 2 ^ 59
def prefixEnd_1022929 : Nat := 4983230072969 + 3 ^ 40 * 1022929 * 2
def baseEnd_1022929 : Nat := 525254252423133519283141

theorem tailTrace_1022929 : CollatzResearch.WordTrace tailWord_1022929 prefixEnd_1022929 525254252423133519283141 := by
  unfold tailWord_1022929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37309285711110410209543841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24872857140740273473029227 37309285711110410209543841)
  ·
    refine ⟨27981964283332807657157881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37309285711110410209543841 27981964283332807657157881)
    ·
      refine ⟨20986473212499605742868411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27981964283332807657157881 20986473212499605742868411)
      ·
        refine ⟨31479709818749408614302617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20986473212499605742868411 31479709818749408614302617)
        ·
          refine ⟨23609782364062056460726963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31479709818749408614302617 23609782364062056460726963)
          ·
            refine ⟨35414673546093084691090445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23609782364062056460726963 35414673546093084691090445)
            ·
              refine ⟨13280502579784906759158917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35414673546093084691090445 13280502579784906759158917)
              ·
                refine ⟨2490094233709670017342297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13280502579784906759158917 2490094233709670017342297)
                ·
                  refine ⟨1867570675282252513006723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490094233709670017342297 1867570675282252513006723)
                  ·
                    refine ⟨2801356012923378769510085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1867570675282252513006723 2801356012923378769510085)
                    ·
                      refine ⟨525254252423133519283141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2801356012923378769510085 525254252423133519283141)
                      ·
                        rfl

theorem cell23_1022929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_1022929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022929 prefixEnd_1022929 := by exact prefixLift 1022929
  have htrace : WordTrace (prefixWord ++ tailWord_1022929) baseStart_1022929 baseEnd_1022929 := by
    simpa [prefixWord, tailWord_1022929, baseEnd_1022929] using wordTrace_append hprefix tailTrace_1022929
  have hstable : (prefixWord ++ tailWord_1022929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022929).length < 2 ^ (prefixWord ++ tailWord_1022929).sum := by decide
  have hdescent : baseEnd_1022929 < baseStart_1022929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022930 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_1022930 : Nat := 118140960795 + 1022930 * 2 ^ 59
def prefixEnd_1022930 : Nat := 4983230072969 + 3 ^ 40 * 1022930 * 2
def baseEnd_1022930 : Nat := 58361640655976446152293

theorem tailTrace_1022930 : CollatzResearch.WordTrace tailWord_1022930 prefixEnd_1022930 58361640655976446152293 := by
  unfold tailWord_1022930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327330546026696845082561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24872881456071191586886829 9327330546026696845082561)
  ·
    refine ⟨6995497909520022633811921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9327330546026696845082561 6995497909520022633811921)
    ·
      refine ⟨5246623432140016975358941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6995497909520022633811921 5246623432140016975358941)
      ·
        refine ⟨1967483787052506365759603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5246623432140016975358941 1967483787052506365759603)
        ·
          refine ⟨2951225680578759548639405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967483787052506365759603 2951225680578759548639405)
          ·
            refine ⟨1106709630217034830739777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2951225680578759548639405 1106709630217034830739777)
            ·
              refine ⟨830032222662776123054833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106709630217034830739777 830032222662776123054833)
              ·
                refine ⟨622524166997082092291125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830032222662776123054833 622524166997082092291125)
                ·
                  refine ⟨58361640655976446152293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622524166997082092291125 58361640655976446152293)
                  ·
                    rfl

theorem cell23_1022930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_1022930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022930 prefixEnd_1022930 := by exact prefixLift 1022930
  have htrace : WordTrace (prefixWord ++ tailWord_1022930) baseStart_1022930 baseEnd_1022930 := by
    simpa [prefixWord, tailWord_1022930, baseEnd_1022930] using wordTrace_append hprefix tailTrace_1022930
  have hstable : (prefixWord ++ tailWord_1022930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022930).length < 2 ^ (prefixWord ++ tailWord_1022930).sum := by decide
  have hdescent : baseEnd_1022930 < baseStart_1022930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022964 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1022964 : Nat := 118140960795 + 1022964 * 2 ^ 59
def prefixEnd_1022964 : Nat := 4983230072969 + 3 ^ 40 * 1022964 * 2
def baseEnd_1022964 : Nat := 58363580471782320260609

theorem tailTrace_1022964 : CollatzResearch.WordTrace tailWord_1022964 prefixEnd_1022964 58363580471782320260609 := by
  unfold tailWord_1022964
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655281132991805593533973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24873708177322407458045297 18655281132991805593533973)
  ·
    refine ⟨874466303108990887196905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18655281132991805593533973 874466303108990887196905)
    ·
      refine ⟨655849727331743165397679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874466303108990887196905 655849727331743165397679)
      ·
        refine ⟨983774590997614748096519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655849727331743165397679 983774590997614748096519)
        ·
          refine ⟨1475661886496422122144779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983774590997614748096519 1475661886496422122144779)
          ·
            refine ⟨2213492829744633183217169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475661886496422122144779 2213492829744633183217169)
            ·
              refine ⟨1660119622308474887412877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213492829744633183217169 1660119622308474887412877)
              ·
                refine ⟨622544858365678082779829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1660119622308474887412877 622544858365678082779829)
                ·
                  refine ⟨58363580471782320260609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622544858365678082779829 58363580471782320260609)
                  ·
                    rfl

theorem cell23_1022964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1022964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022964 prefixEnd_1022964 := by exact prefixLift 1022964
  have htrace : WordTrace (prefixWord ++ tailWord_1022964) baseStart_1022964 baseEnd_1022964 := by
    simpa [prefixWord, tailWord_1022964, baseEnd_1022964] using wordTrace_append hprefix tailTrace_1022964
  have hstable : (prefixWord ++ tailWord_1022964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022964).length < 2 ^ (prefixWord ++ tailWord_1022964).sum := by decide
  have hdescent : baseEnd_1022964 < baseStart_1022964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022986 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_1022986 : Nat := 118140960795 + 1022986 * 2 ^ 59
def prefixEnd_1022986 : Nat := 4983230072969 + 3 ^ 40 * 1022986 * 2
def baseEnd_1022986 : Nat := 58364835646715532918931

theorem tailTrace_1022986 : CollatzResearch.WordTrace tailWord_1022986 prefixEnd_1022986 58364835646715532918931 := by
  unfold tailWord_1022986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327841167975977236092203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24874243114602605962912541 9327841167975977236092203)
  ·
    refine ⟨13991761751963965854138305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327841167975977236092203 13991761751963965854138305)
    ·
      refine ⟨10493821313972974390603729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991761751963965854138305 10493821313972974390603729)
      ·
        refine ⟨7870365985479730792952797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10493821313972974390603729 7870365985479730792952797)
        ·
          refine ⟨2951387244554899047357299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7870365985479730792952797 2951387244554899047357299)
          ·
            refine ⟨4427080866832348571035949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951387244554899047357299 4427080866832348571035949)
            ·
              refine ⟨1660155325062130714138481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4427080866832348571035949 1660155325062130714138481)
              ·
                refine ⟨1245116493796598035603861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660155325062130714138481 1245116493796598035603861)
                ·
                  refine ⟨58364835646715532918931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1245116493796598035603861 58364835646715532918931)
                  ·
                    rfl

theorem cell23_1022986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_1022986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1022986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1022986 prefixEnd_1022986 := by exact prefixLift 1022986
  have htrace : WordTrace (prefixWord ++ tailWord_1022986) baseStart_1022986 baseEnd_1022986 := by
    simpa [prefixWord, tailWord_1022986, baseEnd_1022986] using wordTrace_append hprefix tailTrace_1022986
  have hstable : (prefixWord ++ tailWord_1022986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022986).length < 2 ^ (prefixWord ++ tailWord_1022986).sum := by decide
  have hdescent : baseEnd_1022986 < baseStart_1022986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023029 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1023029 : Nat := 118140960795 + 1023029 * 2 ^ 59
def prefixEnd_1023029 : Nat := 4983230072969 + 3 ^ 40 * 1023029 * 2
def baseEnd_1023029 : Nat := 175101866829527709344227

theorem tailTrace_1023029 : CollatzResearch.WordTrace tailWord_1023029 prefixEnd_1023029 175101866829527709344227 := by
  unfold tailWord_1023029
  simp only [CollatzResearch.WordTrace]
  refine ⟨37312933010748127288184141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24875288673832084858789427 37312933010748127288184141)
  ·
    refine ⟨13992349879030547733069053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37312933010748127288184141 13992349879030547733069053)
    ·
      refine ⟨5247131204636455399900895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13992349879030547733069053 5247131204636455399900895)
      ·
        refine ⟨7870696806954683099851343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247131204636455399900895 7870696806954683099851343)
        ·
          refine ⟨11806045210432024649777015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870696806954683099851343 11806045210432024649777015)
          ·
            refine ⟨17709067815648036974665523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806045210432024649777015 17709067815648036974665523)
            ·
              refine ⟨26563601723472055461998285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17709067815648036974665523 26563601723472055461998285)
              ·
                refine ⟨9961350646302020798249357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26563601723472055461998285 9961350646302020798249357)
                ·
                  refine ⟨3735506492363257799343509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9961350646302020798249357 3735506492363257799343509)
                  ·
                    refine ⟨175101866829527709344227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3735506492363257799343509 175101866829527709344227)
                    ·
                      rfl

theorem cell23_1023029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1023029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023029 prefixEnd_1023029 := by exact prefixLift 1023029
  have htrace : WordTrace (prefixWord ++ tailWord_1023029) baseStart_1023029 baseEnd_1023029 := by
    simpa [prefixWord, tailWord_1023029, baseEnd_1023029] using wordTrace_append hprefix tailTrace_1023029
  have hstable : (prefixWord ++ tailWord_1023029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023029).length < 2 ^ (prefixWord ++ tailWord_1023029).sum := by decide
  have hdescent : baseEnd_1023029 < baseStart_1023029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1023047 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_1023047 : Nat := 118140960795 + 1023047 * 2 ^ 59
def prefixEnd_1023047 : Nat := 4983230072969 + 3 ^ 40 * 1023047 * 2
def baseEnd_1023047 : Nat := 525314843140364057607599

theorem tailTrace_1023047 : CollatzResearch.WordTrace tailWord_1023047 prefixEnd_1023047 525314843140364057607599 := by
  unfold tailWord_1023047
  simp only [CollatzResearch.WordTrace]
  refine ⟨37313589524682916362339395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24875726349788610908226263 37313589524682916362339395)
  ·
    refine ⟨55970384287024374543509093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37313589524682916362339395 55970384287024374543509093)
    ·
      refine ⟨10494447053817070226907955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55970384287024374543509093 10494447053817070226907955)
      ·
        refine ⟨15741670580725605340361933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494447053817070226907955 15741670580725605340361933)
        ·
          refine ⟨5903126467772102002635725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15741670580725605340361933 5903126467772102002635725)
          ·
            refine ⟨2213672425414538250988397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5903126467772102002635725 2213672425414538250988397)
            ·
              refine ⟨830127159530451844120649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2213672425414538250988397 830127159530451844120649)
              ·
                refine ⟨622595369647838883090487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830127159530451844120649 622595369647838883090487)
                ·
                  refine ⟨933893054471758324635731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622595369647838883090487 933893054471758324635731)
                  ·
                    refine ⟨1400839581707637486953597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 933893054471758324635731 1400839581707637486953597)
                    ·
                      refine ⟨525314843140364057607599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1400839581707637486953597 525314843140364057607599)
                      ·
                        rfl

theorem cell23_1023047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_1023047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1023047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1023047 prefixEnd_1023047 := by exact prefixLift 1023047
  have htrace : WordTrace (prefixWord ++ tailWord_1023047) baseStart_1023047 baseEnd_1023047 := by
    simpa [prefixWord, tailWord_1023047, baseEnd_1023047] using wordTrace_append hprefix tailTrace_1023047
  have hstable : (prefixWord ++ tailWord_1023047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1023047).length < 2 ^ (prefixWord ++ tailWord_1023047).sum := by decide
  have hdescent : baseEnd_1023047 < baseStart_1023047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1023047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
