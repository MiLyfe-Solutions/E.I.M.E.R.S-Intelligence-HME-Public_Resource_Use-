import V185TrunkScan23Chunk0496

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2939546 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2939546 : Nat := 118140960795 + 2939546 * 2 ^ 59
def prefixEnd_2939546 : Nat := 4983230072969 + 3 ^ 40 * 2939546 * 2
def baseEnd_2939546 : Nat := 1509400004001461246456281

theorem tailTrace_2939546 : CollatzResearch.WordTrace tailWord_2939546 prefixEnd_2939546 1509400004001461246456281 := by
  unfold tailWord_2939546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26803512652133587833225623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71476033739022900888601661 26803512652133587833225623)
  ·
    refine ⟨40205268978200381749838435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26803512652133587833225623 40205268978200381749838435)
    ·
      refine ⟨60307903467300572624757653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40205268978200381749838435 60307903467300572624757653)
      ·
        refine ⟨2826932975029714341785515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60307903467300572624757653 2826932975029714341785515)
        ·
          refine ⟨4240399462544571512678273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826932975029714341785515 4240399462544571512678273)
          ·
            refine ⟨3180299596908428634508705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4240399462544571512678273 3180299596908428634508705)
            ·
              refine ⟨2385224697681321475881529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180299596908428634508705 2385224697681321475881529)
              ·
                refine ⟨1788918523260991106911147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2385224697681321475881529 1788918523260991106911147)
                ·
                  refine ⟨2683377784891486660366721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788918523260991106911147 2683377784891486660366721)
                  ·
                    refine ⟨2012533338668614995275041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2683377784891486660366721 2012533338668614995275041)
                    ·
                      refine ⟨1509400004001461246456281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012533338668614995275041 1509400004001461246456281)
                      ·
                        rfl

theorem cell23_2939546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2939546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939546 prefixEnd_2939546 := by exact prefixLift 2939546
  have htrace : WordTrace (prefixWord ++ tailWord_2939546) baseStart_2939546 baseEnd_2939546 := by
    simpa [prefixWord, tailWord_2939546, baseEnd_2939546] using wordTrace_append hprefix tailTrace_2939546
  have hstable : (prefixWord ++ tailWord_2939546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939546).length < 2 ^ (prefixWord ++ tailWord_2939546).sum := by decide
  have hdescent : baseEnd_2939546 < baseStart_2939546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939641 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 6, 2]
def baseStart_2939641 : Nat := 118140960795 + 2939641 * 2 ^ 59
def prefixEnd_2939641 : Nat := 4983230072969 + 3 ^ 40 * 2939641 * 2
def baseEnd_2939641 : Nat := 1509448784663638374768343

theorem tailTrace_2939641 : CollatzResearch.WordTrace tailWord_2939641 prefixEnd_2939641 1509448784663638374768343 := by
  unfold tailWord_2939641
  simp only [CollatzResearch.WordTrace]
  refine ⟨107217515543190182557610777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71478343695460121705073851 107217515543190182557610777)
  ·
    refine ⟨80413136657392636918208083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107217515543190182557610777 80413136657392636918208083)
    ·
      refine ⟨120619704986088955377312125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80413136657392636918208083 120619704986088955377312125)
      ·
        refine ⟨45232389369783358266492047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120619704986088955377312125 45232389369783358266492047)
        ·
          refine ⟨67848584054675037399738071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45232389369783358266492047 67848584054675037399738071)
          ·
            refine ⟨101772876082012556099607107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67848584054675037399738071 101772876082012556099607107)
            ·
              refine ⟨152659314123018834149410661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101772876082012556099607107 152659314123018834149410661)
              ·
                refine ⟨28623621398066031403014499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152659314123018834149410661 28623621398066031403014499)
                ·
                  refine ⟨42935432097099047104521749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28623621398066031403014499 42935432097099047104521749)
                  ·
                    refine ⟨2012598379551517833024457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42935432097099047104521749 2012598379551517833024457)
                    ·
                      refine ⟨1509448784663638374768343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012598379551517833024457 1509448784663638374768343)
                      ·
                        rfl

theorem cell23_2939641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_2939641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939641 prefixEnd_2939641 := by exact prefixLift 2939641
  have htrace : WordTrace (prefixWord ++ tailWord_2939641) baseStart_2939641 baseEnd_2939641 := by
    simpa [prefixWord, tailWord_2939641, baseEnd_2939641] using wordTrace_append hprefix tailTrace_2939641
  have hstable : (prefixWord ++ tailWord_2939641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939641).length < 2 ^ (prefixWord ++ tailWord_2939641).sum := by decide
  have hdescent : baseEnd_2939641 < baseStart_2939641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939681 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 6]
def baseStart_2939681 : Nat := 118140960795 + 2939681 * 2 ^ 59
def prefixEnd_2939681 : Nat := 4983230072969 + 3 ^ 40 * 2939681 * 2
def baseEnd_2939681 : Nat := 167718813765535357585351

theorem tailTrace_2939681 : CollatzResearch.WordTrace tailWord_2939681 prefixEnd_2939681 167718813765535357585351 := by
  unfold tailWord_2939681
  simp only [CollatzResearch.WordTrace]
  refine ⟨107218974463045269389066897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71479316308696846259377931 107218974463045269389066897)
  ·
    refine ⟨80414230847283952041800173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107218974463045269389066897 80414230847283952041800173)
    ·
      refine ⟨30155336567731482015675065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80414230847283952041800173 30155336567731482015675065)
      ·
        refine ⟨22616502425798611511756299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30155336567731482015675065 22616502425798611511756299)
        ·
          refine ⟨33924753638697917267634449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22616502425798611511756299 33924753638697917267634449)
          ·
            refine ⟨25443565229023437950725837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33924753638697917267634449 25443565229023437950725837)
            ·
              refine ⟨9541336960883789231522189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25443565229023437950725837 9541336960883789231522189)
              ·
                refine ⟨3578001360331420961820821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9541336960883789231522189 3578001360331420961820821)
                ·
                  refine ⟨167718813765535357585351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3578001360331420961820821 167718813765535357585351)
                  ·
                    rfl

theorem cell23_2939681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_2939681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939681 prefixEnd_2939681 := by exact prefixLift 2939681
  have htrace : WordTrace (prefixWord ++ tailWord_2939681) baseStart_2939681 baseEnd_2939681 := by
    simpa [prefixWord, tailWord_2939681, baseEnd_2939681] using wordTrace_append hprefix tailTrace_2939681
  have hstable : (prefixWord ++ tailWord_2939681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939681).length < 2 ^ (prefixWord ++ tailWord_2939681).sum := by decide
  have hdescent : baseEnd_2939681 < baseStart_2939681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939748 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2939748 : Nat := 118140960795 + 2939748 * 2 ^ 59
def prefixEnd_2939748 : Nat := 4983230072969 + 3 ^ 40 * 2939748 * 2
def baseEnd_2939748 : Nat := 1509503727093669456130351

theorem tailTrace_2939748 : CollatzResearch.WordTrace tailWord_2939748 prefixEnd_2939748 1509503727093669456130351 := by
  unfold tailWord_2939748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53610709076901269915877949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71480945435868359887837265 53610709076901269915877949)
  ·
    refine ⟨20104015903837976218454231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53610709076901269915877949 20104015903837976218454231)
    ·
      refine ⟨30156023855756964327681347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20104015903837976218454231 30156023855756964327681347)
      ·
        refine ⟨45234035783635446491522021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30156023855756964327681347 45234035783635446491522021)
        ·
          refine ⟨8481381709431646217160379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45234035783635446491522021 8481381709431646217160379)
          ·
            refine ⟨12722072564147469325740569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8481381709431646217160379 12722072564147469325740569)
            ·
              refine ⟨9541554423110601994305427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12722072564147469325740569 9541554423110601994305427)
              ·
                refine ⟨14312331634665902991458141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541554423110601994305427 14312331634665902991458141)
                ·
                  refine ⟨5367124362999713621796803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14312331634665902991458141 5367124362999713621796803)
                  ·
                    refine ⟨8050686544499570432695205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367124362999713621796803 8050686544499570432695205)
                    ·
                      refine ⟨1509503727093669456130351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8050686544499570432695205 1509503727093669456130351)
                      ·
                        rfl

theorem cell23_2939748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2939748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939748 prefixEnd_2939748 := by exact prefixLift 2939748
  have htrace : WordTrace (prefixWord ++ tailWord_2939748) baseStart_2939748 baseEnd_2939748 := by
    simpa [prefixWord, tailWord_2939748, baseEnd_2939748] using wordTrace_append hprefix tailTrace_2939748
  have hstable : (prefixWord ++ tailWord_2939748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939748).length < 2 ^ (prefixWord ++ tailWord_2939748).sum := by decide
  have hdescent : baseEnd_2939748 < baseStart_2939748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939752 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2939752 : Nat := 118140960795 + 2939752 * 2 ^ 59
def prefixEnd_2939752 : Nat := 4983230072969 + 3 ^ 40 * 2939752 * 2
def baseEnd_2939752 : Nat := 1509505781016287440480333

theorem tailTrace_2939752 : CollatzResearch.WordTrace tailWord_2939752 prefixEnd_2939752 1509505781016287440480333 := by
  unfold tailWord_2939752
  simp only [CollatzResearch.WordTrace]
  refine ⟨53610782022894024257450755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71481042697192032343267673 53610782022894024257450755)
  ·
    refine ⟨80416173034341036386176133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53610782022894024257450755 80416173034341036386176133)
    ·
      refine ⟨15078032443938944322408025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80416173034341036386176133 15078032443938944322408025)
      ·
        refine ⟨11308524332954208241806019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15078032443938944322408025 11308524332954208241806019)
        ·
          refine ⟨16962786499431312362709029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11308524332954208241806019 16962786499431312362709029)
          ·
            refine ⟨3180522468643371068007943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16962786499431312362709029 3180522468643371068007943)
            ·
              refine ⟨4770783702965056602011915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180522468643371068007943 4770783702965056602011915)
              ·
                refine ⟨7156175554447584903017873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770783702965056602011915 7156175554447584903017873)
                ·
                  refine ⟨5367131665835688677263405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7156175554447584903017873 5367131665835688677263405)
                  ·
                    refine ⟨2012674374688383253973777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5367131665835688677263405 2012674374688383253973777)
                    ·
                      refine ⟨1509505781016287440480333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012674374688383253973777 1509505781016287440480333)
                      ·
                        rfl

theorem cell23_2939752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2939752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939752 prefixEnd_2939752 := by exact prefixLift 2939752
  have htrace : WordTrace (prefixWord ++ tailWord_2939752) baseStart_2939752 baseEnd_2939752 := by
    simpa [prefixWord, tailWord_2939752, baseEnd_2939752] using wordTrace_append hprefix tailTrace_2939752
  have hstable : (prefixWord ++ tailWord_2939752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939752).length < 2 ^ (prefixWord ++ tailWord_2939752).sum := by decide
  have hdescent : baseEnd_2939752 < baseStart_2939752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939765 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2939765 : Nat := 118140960795 + 2939765 * 2 ^ 59
def prefixEnd_2939765 : Nat := 4983230072969 + 3 ^ 40 * 2939765 * 2
def baseEnd_2939765 : Nat := 1509512456264795889617773

theorem tailTrace_2939765 : CollatzResearch.WordTrace tailWord_2939765 prefixEnd_2939765 1509512456264795889617773 := by
  unfold tailWord_2939765
  simp only [CollatzResearch.WordTrace]
  refine ⟨107222038194740951735124749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71481358796493967823416499 107222038194740951735124749)
  ·
    refine ⟨40208264323027856900671781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107222038194740951735124749 40208264323027856900671781)
    ·
      refine ⟨7539049560567723168875959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40208264323027856900671781 7539049560567723168875959)
      ·
        refine ⟨11308574340851584753313939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539049560567723168875959 11308574340851584753313939)
        ·
          refine ⟨16962861511277377129970909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11308574340851584753313939 16962861511277377129970909)
          ·
            refine ⟨6361073066729016423739091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16962861511277377129970909 6361073066729016423739091)
            ·
              refine ⟨9541609600093524635608637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361073066729016423739091 9541609600093524635608637)
              ·
                refine ⟨3578103600035071738353239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9541609600093524635608637 3578103600035071738353239)
                ·
                  refine ⟨5367155400052607607529859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578103600035071738353239 5367155400052607607529859)
                  ·
                    refine ⟨8050733100078911411294789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367155400052607607529859 8050733100078911411294789)
                    ·
                      refine ⟨1509512456264795889617773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8050733100078911411294789 1509512456264795889617773)
                      ·
                        rfl

theorem cell23_2939765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2939765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939765 prefixEnd_2939765 := by exact prefixLift 2939765
  have htrace : WordTrace (prefixWord ++ tailWord_2939765) baseStart_2939765 baseEnd_2939765 := by
    simpa [prefixWord, tailWord_2939765, baseEnd_2939765] using wordTrace_append hprefix tailTrace_2939765
  have hstable : (prefixWord ++ tailWord_2939765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939765).length < 2 ^ (prefixWord ++ tailWord_2939765).sum := by decide
  have hdescent : baseEnd_2939765 < baseStart_2939765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939802 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2939802 : Nat := 118140960795 + 2939802 * 2 ^ 59
def prefixEnd_2939802 : Nat := 4983230072969 + 3 ^ 40 * 2939802 * 2
def baseEnd_2939802 : Nat := 1509531455049012244855103

theorem tailTrace_2939802 : CollatzResearch.WordTrace tailWord_2939802 prefixEnd_2939802 1509531455049012244855103 := by
  unfold tailWord_2939802
  simp only [CollatzResearch.WordTrace]
  refine ⟨26805846923901726763555415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71482258463737938036147773 26805846923901726763555415)
  ·
    refine ⟨40208770385852590145333123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26805846923901726763555415 40208770385852590145333123)
    ·
      refine ⟨60313155578778885217999685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40208770385852590145333123 60313155578778885217999685)
      ·
        refine ⟨11308716671021040978374941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60313155578778885217999685 11308716671021040978374941)
        ·
          refine ⟨4240768751632890366890603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11308716671021040978374941 4240768751632890366890603)
          ·
            refine ⟨6361153127449335550335905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240768751632890366890603 6361153127449335550335905)
            ·
              refine ⟨4770864845587001662751929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6361153127449335550335905 4770864845587001662751929)
              ·
                refine ⟨3578148634190251247063947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770864845587001662751929 3578148634190251247063947)
                ·
                  refine ⟨5367222951285376870595921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578148634190251247063947 5367222951285376870595921)
                  ·
                    refine ⟨4025417213464032652946941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5367222951285376870595921 4025417213464032652946941)
                    ·
                      refine ⟨1509531455049012244855103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025417213464032652946941 1509531455049012244855103)
                      ·
                        rfl

theorem cell23_2939802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2939802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939802 prefixEnd_2939802 := by exact prefixLift 2939802
  have htrace : WordTrace (prefixWord ++ tailWord_2939802) baseStart_2939802 baseEnd_2939802 := by
    simpa [prefixWord, tailWord_2939802, baseEnd_2939802] using wordTrace_append hprefix tailTrace_2939802
  have hstable : (prefixWord ++ tailWord_2939802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939802).length < 2 ^ (prefixWord ++ tailWord_2939802).sum := by decide
  have hdescent : baseEnd_2939802 < baseStart_2939802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939811 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2939811 : Nat := 118140960795 + 2939811 * 2 ^ 59
def prefixEnd_2939811 : Nat := 4983230072969 + 3 ^ 40 * 2939811 * 2
def baseEnd_2939811 : Nat := 1509536076374902709642561

theorem tailTrace_2939811 : CollatzResearch.WordTrace tailWord_2939811 prefixEnd_2939811 1509536076374902709642561 := by
  unfold tailWord_2939811
  simp only [CollatzResearch.WordTrace]
  refine ⟨107223715952574301591299287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71482477301716201060866191 107223715952574301591299287)
  ·
    refine ⟨160835573928861452386948931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107223715952574301591299287 160835573928861452386948931)
    ·
      refine ⟨241253360893292178580423397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160835573928861452386948931 241253360893292178580423397)
      ·
        refine ⟨45235005167492283483829387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241253360893292178580423397 45235005167492283483829387)
        ·
          refine ⟨67852507751238425225744081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45235005167492283483829387 67852507751238425225744081)
          ·
            refine ⟨50889380813428818919308061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67852507751238425225744081 50889380813428818919308061)
            ·
              refine ⟨19083517805035807094740523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50889380813428818919308061 19083517805035807094740523)
              ·
                refine ⟨28625276707553710642110785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19083517805035807094740523 28625276707553710642110785)
                ·
                  refine ⟨21468957530665282981583089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28625276707553710642110785 21468957530665282981583089)
                  ·
                    refine ⟨16101718147998962236187317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21468957530665282981583089 16101718147998962236187317)
                    ·
                      refine ⟨1509536076374902709642561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16101718147998962236187317 1509536076374902709642561)
                      ·
                        rfl

theorem cell23_2939811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2939811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939811 prefixEnd_2939811 := by exact prefixLift 2939811
  have htrace : WordTrace (prefixWord ++ tailWord_2939811) baseStart_2939811 baseEnd_2939811 := by
    simpa [prefixWord, tailWord_2939811, baseEnd_2939811] using wordTrace_append hprefix tailTrace_2939811
  have hstable : (prefixWord ++ tailWord_2939811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939811).length < 2 ^ (prefixWord ++ tailWord_2939811).sum := by decide
  have hdescent : baseEnd_2939811 < baseStart_2939811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939831 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 4, 6]
def baseStart_2939831 : Nat := 118140960795 + 2939831 * 2 ^ 59
def prefixEnd_2939831 : Nat := 4983230072969 + 3 ^ 40 * 2939831 * 2
def baseEnd_2939831 : Nat := 503182115329330877130823

theorem tailTrace_2939831 : CollatzResearch.WordTrace tailWord_2939831 prefixEnd_2939831 503182115329330877130823 := by
  unfold tailWord_2939831
  simp only [CollatzResearch.WordTrace]
  refine ⟨107224445412501845007027347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71482963608334563338018231 107224445412501845007027347)
  ·
    refine ⟨160836668118752767510541021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107224445412501845007027347 160836668118752767510541021)
    ·
      refine ⟨60313750544532287816452883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160836668118752767510541021 60313750544532287816452883)
      ·
        refine ⟨90470625816798431724679325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60313750544532287816452883 90470625816798431724679325)
        ·
          refine ⟨33926484681299411896754747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90470625816798431724679325 33926484681299411896754747)
          ·
            refine ⟨50889727021949117845132121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33926484681299411896754747 50889727021949117845132121)
            ·
              refine ⟨38167295266461838383849091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50889727021949117845132121 38167295266461838383849091)
              ·
                refine ⟨57250942899692757575773637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38167295266461838383849091 57250942899692757575773637)
                ·
                  refine ⟨10734551793692392045457557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57250942899692757575773637 10734551793692392045457557)
                  ·
                    refine ⟨503182115329330877130823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10734551793692392045457557 503182115329330877130823)
                    ·
                      rfl

theorem cell23_2939831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_2939831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939831 prefixEnd_2939831 := by exact prefixLift 2939831
  have htrace : WordTrace (prefixWord ++ tailWord_2939831) baseStart_2939831 baseEnd_2939831 := by
    simpa [prefixWord, tailWord_2939831, baseEnd_2939831] using wordTrace_append hprefix tailTrace_2939831
  have hstable : (prefixWord ++ tailWord_2939831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939831).length < 2 ^ (prefixWord ++ tailWord_2939831).sum := by decide
  have hdescent : baseEnd_2939831 < baseStart_2939831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939838 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2939838 : Nat := 118140960795 + 2939838 * 2 ^ 59
def prefixEnd_2939838 : Nat := 4983230072969 + 3 ^ 40 * 2939838 * 2
def baseEnd_2939838 : Nat := 1509549940352574104004937

theorem tailTrace_2939838 : CollatzResearch.WordTrace tailWord_2939838 prefixEnd_2939838 1509549940352574104004937 := by
  unfold tailWord_2939838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403087590434560650316521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71483133815650990135021445 13403087590434560650316521)
  ·
    refine ⟨10052315692825920487737391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13403087590434560650316521 10052315692825920487737391)
    ·
      refine ⟨15078473539238880731606087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052315692825920487737391 15078473539238880731606087)
      ·
        refine ⟨22617710308858321097409131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078473539238880731606087 22617710308858321097409131)
        ·
          refine ⟨33926565463287481646113697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22617710308858321097409131 33926565463287481646113697)
          ·
            refine ⟨25444924097465611234585273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33926565463287481646113697 25444924097465611234585273)
            ·
              refine ⟨19083693073099208425938955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25444924097465611234585273 19083693073099208425938955)
              ·
                refine ⟨28625539609648812638908433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19083693073099208425938955 28625539609648812638908433)
                ·
                  refine ⟨21469154707236609479181325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28625539609648812638908433 21469154707236609479181325)
                  ·
                    refine ⟨8050933015213728554692997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21469154707236609479181325 8050933015213728554692997)
                    ·
                      refine ⟨1509549940352574104004937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8050933015213728554692997 1509549940352574104004937)
                      ·
                        rfl

theorem cell23_2939838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2939838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939838 prefixEnd_2939838 := by exact prefixLift 2939838
  have htrace : WordTrace (prefixWord ++ tailWord_2939838) baseStart_2939838 baseEnd_2939838 := by
    simpa [prefixWord, tailWord_2939838, baseEnd_2939838] using wordTrace_append hprefix tailTrace_2939838
  have hstable : (prefixWord ++ tailWord_2939838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939838).length < 2 ^ (prefixWord ++ tailWord_2939838).sum := by decide
  have hdescent : baseEnd_2939838 < baseStart_2939838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939853 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2939853 : Nat := 118140960795 + 2939853 * 2 ^ 59
def prefixEnd_2939853 : Nat := 4983230072969 + 3 ^ 40 * 2939853 * 2
def baseEnd_2939853 : Nat := 1509557642562391545317369

theorem tailTrace_2939853 : CollatzResearch.WordTrace tailWord_2939853 prefixEnd_2939853 1509557642562391545317369 := by
  unfold tailWord_2939853
  simp only [CollatzResearch.WordTrace]
  refine ⟨107225247818422142764328213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71483498545614761842885475 107225247818422142764328213)
  ·
    refine ⟨5026183491488537942077885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107225247818422142764328213 5026183491488537942077885)
    ·
      refine ⟨1884818809308201728279207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5026183491488537942077885 1884818809308201728279207)
      ·
        refine ⟨2827228213962302592418811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884818809308201728279207 2827228213962302592418811)
        ·
          refine ⟨4240842320943453888628217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827228213962302592418811 4240842320943453888628217)
          ·
            refine ⟨3180631740707590416471163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4240842320943453888628217 3180631740707590416471163)
            ·
              refine ⟨4770947611061385624706745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180631740707590416471163 4770947611061385624706745)
              ·
                refine ⟨3578210708296039218530059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770947611061385624706745 3578210708296039218530059)
                ·
                  refine ⟨5367316062444058827795089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578210708296039218530059 5367316062444058827795089)
                  ·
                    refine ⟨4025487046833044120846317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5367316062444058827795089 4025487046833044120846317)
                    ·
                      refine ⟨1509557642562391545317369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025487046833044120846317 1509557642562391545317369)
                      ·
                        rfl

theorem cell23_2939853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2939853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939853 prefixEnd_2939853 := by exact prefixLift 2939853
  have htrace : WordTrace (prefixWord ++ tailWord_2939853) baseStart_2939853 baseEnd_2939853 := by
    simpa [prefixWord, tailWord_2939853, baseEnd_2939853] using wordTrace_append hprefix tailTrace_2939853
  have hstable : (prefixWord ++ tailWord_2939853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939853).length < 2 ^ (prefixWord ++ tailWord_2939853).sum := by decide
  have hdescent : baseEnd_2939853 < baseStart_2939853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939888 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_2939888 : Nat := 118140960795 + 2939888 * 2 ^ 59
def prefixEnd_2939888 : Nat := 4983230072969 + 3 ^ 40 * 2939888 * 2
def baseEnd_2939888 : Nat := 1509575614385298908379707

theorem tailTrace_2939888 : CollatzResearch.WordTrace tailWord_2939888 prefixEnd_2939888 1509575614385298908379707 := by
  unfold tailWord_2939888
  simp only [CollatzResearch.WordTrace]
  refine ⟨53613262186647671870926159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71484349582196895827901545 53613262186647671870926159)
  ·
    refine ⟨80419893279971507806389239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53613262186647671870926159 80419893279971507806389239)
    ·
      refine ⟨120629839919957261709583859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80419893279971507806389239 120629839919957261709583859)
      ·
        refine ⟨180944759879935892564375789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120629839919957261709583859 180944759879935892564375789)
        ·
          refine ⟨67854284954975959711640921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180944759879935892564375789 67854284954975959711640921)
          ·
            refine ⟨50890713716231969783730691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67854284954975959711640921 50890713716231969783730691)
            ·
              refine ⟨76336070574347954675596037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50890713716231969783730691 76336070574347954675596037)
              ·
                refine ⟨14313013232690241501674257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76336070574347954675596037 14313013232690241501674257)
                ·
                  refine ⟨10734759924517681126255693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14313013232690241501674257 10734759924517681126255693)
                  ·
                    refine ⟨4025534971694130422345885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10734759924517681126255693 4025534971694130422345885)
                    ·
                      refine ⟨1509575614385298908379707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025534971694130422345885 1509575614385298908379707)
                      ·
                        rfl

theorem cell23_2939888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_2939888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939888 prefixEnd_2939888 := by exact prefixLift 2939888
  have htrace : WordTrace (prefixWord ++ tailWord_2939888) baseStart_2939888 baseEnd_2939888 := by
    simpa [prefixWord, tailWord_2939888, baseEnd_2939888] using wordTrace_append hprefix tailTrace_2939888
  have hstable : (prefixWord ++ tailWord_2939888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939888).length < 2 ^ (prefixWord ++ tailWord_2939888).sum := by decide
  have hdescent : baseEnd_2939888 < baseStart_2939888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939889 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_2939889 : Nat := 118140960795 + 2939889 * 2 ^ 59
def prefixEnd_2939889 : Nat := 4983230072969 + 3 ^ 40 * 2939889 * 2
def baseEnd_2939889 : Nat := 1509576127865953404467203

theorem tailTrace_2939889 : CollatzResearch.WordTrace tailWord_2939889 prefixEnd_2939889 1509576127865953404467203 := by
  unfold tailWord_2939889
  simp only [CollatzResearch.WordTrace]
  refine ⟨107226560846291720912638721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71484373897527813941759147 107226560846291720912638721)
  ·
    refine ⟨80419920634718790684479041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107226560846291720912638721 80419920634718790684479041)
    ·
      refine ⟨60314940476039093013359281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80419920634718790684479041 60314940476039093013359281)
      ·
        refine ⟨45236205357029319760019461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60314940476039093013359281 45236205357029319760019461)
        ·
          refine ⟨8481788504442997455003649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45236205357029319760019461 8481788504442997455003649)
          ·
            refine ⟨6361341378332248091252737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8481788504442997455003649 6361341378332248091252737)
            ·
              refine ⟨4771006033749186068439553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6361341378332248091252737 4771006033749186068439553)
              ·
                refine ⟨3578254525311889551329665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771006033749186068439553 3578254525311889551329665)
                ·
                  refine ⟨2683690893983917163497249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578254525311889551329665 2683690893983917163497249)
                  ·
                    refine ⟨2012768170487937872622937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2683690893983917163497249 2012768170487937872622937)
                    ·
                      refine ⟨1509576127865953404467203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012768170487937872622937 1509576127865953404467203)
                      ·
                        rfl

theorem cell23_2939889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_2939889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939889 prefixEnd_2939889 := by exact prefixLift 2939889
  have htrace : WordTrace (prefixWord ++ tailWord_2939889) baseStart_2939889 baseEnd_2939889 := by
    simpa [prefixWord, tailWord_2939889, baseEnd_2939889] using wordTrace_append hprefix tailTrace_2939889
  have hstable : (prefixWord ++ tailWord_2939889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939889).length < 2 ^ (prefixWord ++ tailWord_2939889).sum := by decide
  have hdescent : baseEnd_2939889 < baseStart_2939889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939891 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 7]
def baseStart_2939891 : Nat := 118140960795 + 2939891 * 2 ^ 59
def prefixEnd_2939891 : Nat := 4983230072969 + 3 ^ 40 * 2939891 * 2
def baseEnd_2939891 : Nat := 503192384942420798880731

theorem tailTrace_2939891 : CollatzResearch.WordTrace tailWord_2939891 prefixEnd_2939891 503192384942420798880731 := by
  unfold tailWord_2939891
  simp only [CollatzResearch.WordTrace]
  refine ⟨107226633792284475254211527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71484422528189650169474351 107226633792284475254211527)
  ·
    refine ⟨160839950688426712881317291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107226633792284475254211527 160839950688426712881317291)
    ·
      refine ⟨241259926032640069321975937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160839950688426712881317291 241259926032640069321975937)
      ·
        refine ⟨180944944524480051991481953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241259926032640069321975937 180944944524480051991481953)
        ·
          refine ⟨135708708393360038993611465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180944944524480051991481953 135708708393360038993611465)
          ·
            refine ⟨101781531295020029245208599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135708708393360038993611465 101781531295020029245208599)
            ·
              refine ⟨152672296942530043867812899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101781531295020029245208599 152672296942530043867812899)
              ·
                refine ⟨229008445413795065801719349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152672296942530043867812899 229008445413795065801719349)
                ·
                  refine ⟨21469541757543287418911189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229008445413795065801719349 21469541757543287418911189)
                  ·
                    refine ⟨503192384942420798880731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21469541757543287418911189 503192384942420798880731)
                    ·
                      rfl

theorem cell23_2939891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_2939891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939891 prefixEnd_2939891 := by exact prefixLift 2939891
  have htrace : WordTrace (prefixWord ++ tailWord_2939891) baseStart_2939891 baseEnd_2939891 := by
    simpa [prefixWord, tailWord_2939891, baseEnd_2939891] using wordTrace_append hprefix tailTrace_2939891
  have hstable : (prefixWord ++ tailWord_2939891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939891).length < 2 ^ (prefixWord ++ tailWord_2939891).sum := by decide
  have hdescent : baseEnd_2939891 < baseStart_2939891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939902 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2939902 : Nat := 118140960795 + 2939902 * 2 ^ 59
def prefixEnd_2939902 : Nat := 4983230072969 + 3 ^ 40 * 2939902 * 2
def baseEnd_2939902 : Nat := 1509582803114461853604643

theorem tailTrace_2939902 : CollatzResearch.WordTrace tailWord_2939902 prefixEnd_2939902 1509582803114461853604643 := by
  unfold tailWord_2939902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403379374405578016607745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71484689996829749421907973 13403379374405578016607745)
  ·
    refine ⟨10052534530804183512455809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13403379374405578016607745 10052534530804183512455809)
    ·
      refine ⟨7539400898103137634341857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10052534530804183512455809 7539400898103137634341857)
      ·
        refine ⟨5654550673577353225756393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7539400898103137634341857 5654550673577353225756393)
        ·
          refine ⟨4240913005183014919317295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5654550673577353225756393 4240913005183014919317295)
          ·
            refine ⟨6361369507774522378975943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240913005183014919317295 6361369507774522378975943)
            ·
              refine ⟨9542054261661783568463915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361369507774522378975943 9542054261661783568463915)
              ·
                refine ⟨14313081392492675352695873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542054261661783568463915 14313081392492675352695873)
                ·
                  refine ⟨10734811044369506514521905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14313081392492675352695873 10734811044369506514521905)
                  ·
                    refine ⟨8051108283277129885891429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10734811044369506514521905 8051108283277129885891429)
                    ·
                      refine ⟨1509582803114461853604643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8051108283277129885891429 1509582803114461853604643)
                      ·
                        rfl

theorem cell23_2939902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2939902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939902 prefixEnd_2939902 := by exact prefixLift 2939902
  have htrace : WordTrace (prefixWord ++ tailWord_2939902) baseStart_2939902 baseEnd_2939902 := by
    simpa [prefixWord, tailWord_2939902, baseEnd_2939902] using wordTrace_append hprefix tailTrace_2939902
  have hstable : (prefixWord ++ tailWord_2939902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939902).length < 2 ^ (prefixWord ++ tailWord_2939902).sum := by decide
  have hdescent : baseEnd_2939902 < baseStart_2939902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939905 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_2939905 : Nat := 118140960795 + 2939905 * 2 ^ 59
def prefixEnd_2939905 : Nat := 4983230072969 + 3 ^ 40 * 2939905 * 2
def baseEnd_2939905 : Nat := 1509584343556425341867129

theorem tailTrace_2939905 : CollatzResearch.WordTrace tailWord_2939905 prefixEnd_2939905 1509584343556425341867129 := by
  unfold tailWord_2939905
  simp only [CollatzResearch.WordTrace]
  refine ⟨107227144414233755645221169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71484762942822503763480779 107227144414233755645221169)
  ·
    refine ⟨80420358310675316733915877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107227144414233755645221169 80420358310675316733915877)
    ·
      refine ⟨15078817183251621887609227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80420358310675316733915877 15078817183251621887609227)
      ·
        refine ⟨22618225774877432831413841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078817183251621887609227 22618225774877432831413841)
        ·
          refine ⟨16963669331158074623560381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22618225774877432831413841 16963669331158074623560381)
          ·
            refine ⟨6361375999184277983835143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16963669331158074623560381 6361375999184277983835143)
            ·
              refine ⟨9542063998776416975752715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361375999184277983835143 9542063998776416975752715)
              ·
                refine ⟨14313095998164625463629073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542063998776416975752715 14313095998164625463629073)
                ·
                  refine ⟨10734821998623469097721805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14313095998164625463629073 10734821998623469097721805)
                  ·
                    refine ⟨4025558249483800911645677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10734821998623469097721805 4025558249483800911645677)
                    ·
                      refine ⟨1509584343556425341867129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025558249483800911645677 1509584343556425341867129)
                      ·
                        rfl

theorem cell23_2939905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_2939905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939905 prefixEnd_2939905 := by exact prefixLift 2939905
  have htrace : WordTrace (prefixWord ++ tailWord_2939905) baseStart_2939905 baseEnd_2939905 := by
    simpa [prefixWord, tailWord_2939905, baseEnd_2939905] using wordTrace_append hprefix tailTrace_2939905
  have hstable : (prefixWord ++ tailWord_2939905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939905).length < 2 ^ (prefixWord ++ tailWord_2939905).sum := by decide
  have hdescent : baseEnd_2939905 < baseStart_2939905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939906 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2939906 : Nat := 118140960795 + 2939906 * 2 ^ 59
def prefixEnd_2939906 : Nat := 4983230072969 + 3 ^ 40 * 2939906 * 2
def baseEnd_2939906 : Nat := 1509584857037079837954625

theorem tailTrace_2939906 : CollatzResearch.WordTrace tailWord_2939906 prefixEnd_2939906 1509584857037079837954625 := by
  unfold tailWord_2939906
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806795221807533204001893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71484787258153421877338381 26806795221807533204001893)
  ·
    refine ⟨5026274104088912475750355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26806795221807533204001893 5026274104088912475750355)
    ·
      refine ⟨7539411156133368713625533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5026274104088912475750355 7539411156133368713625533)
      ·
        refine ⟨2827279183550013267609575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7539411156133368713625533 2827279183550013267609575)
        ·
          refine ⟨4240918775325019901414363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827279183550013267609575 4240918775325019901414363)
          ·
            refine ⟨6361378162987529852121545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240918775325019901414363 6361378162987529852121545)
            ·
              refine ⟨4771033622240647389091159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6361378162987529852121545 4771033622240647389091159)
              ·
                refine ⟨7156550433360971083636739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771033622240647389091159 7156550433360971083636739)
                ·
                  refine ⟨10734825650041456625455109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7156550433360971083636739 10734825650041456625455109)
                  ·
                    refine ⟨2012779809382773117272833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10734825650041456625455109 2012779809382773117272833)
                    ·
                      refine ⟨1509584857037079837954625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012779809382773117272833 1509584857037079837954625)
                      ·
                        rfl

theorem cell23_2939906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2939906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939906 prefixEnd_2939906 := by exact prefixLift 2939906
  have htrace : WordTrace (prefixWord ++ tailWord_2939906) baseStart_2939906 baseEnd_2939906 := by
    simpa [prefixWord, tailWord_2939906, baseEnd_2939906] using wordTrace_append hprefix tailTrace_2939906
  have hstable : (prefixWord ++ tailWord_2939906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939906).length < 2 ^ (prefixWord ++ tailWord_2939906).sum := by decide
  have hdescent : baseEnd_2939906 < baseStart_2939906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939925 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2939925 : Nat := 118140960795 + 2939925 * 2 ^ 59
def prefixEnd_2939925 : Nat := 4983230072969 + 3 ^ 40 * 2939925 * 2
def baseEnd_2939925 : Nat := 503198204389838421205679

theorem tailTrace_2939925 : CollatzResearch.WordTrace tailWord_2939925 prefixEnd_2939925 503198204389838421205679 := by
  unfold tailWord_2939925
  simp only [CollatzResearch.WordTrace]
  refine ⟨107227873874161299060949229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71485249249440866040632819 107227873874161299060949229)
  ·
    refine ⟨40210452702810487147855961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107227873874161299060949229 40210452702810487147855961)
    ·
      refine ⟨30157839527107865360891971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40210452702810487147855961 30157839527107865360891971)
      ·
        refine ⟨45236759290661798041337957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30157839527107865360891971 45236759290661798041337957)
        ·
          refine ⟨8481892366999087132750867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45236759290661798041337957 8481892366999087132750867)
          ·
            refine ⟨12722838550498630699126301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8481892366999087132750867 12722838550498630699126301)
            ·
              refine ⟨4771064456436986512172363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12722838550498630699126301 4771064456436986512172363)
              ·
                refine ⟨7156596684655479768258545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771064456436986512172363 7156596684655479768258545)
                ·
                  refine ⟨5367447513491609826193909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7156596684655479768258545 5367447513491609826193909)
                  ·
                    refine ⟨503198204389838421205679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5367447513491609826193909 503198204389838421205679)
                    ·
                      rfl

theorem cell23_2939925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2939925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939925 prefixEnd_2939925 := by exact prefixLift 2939925
  have htrace : WordTrace (prefixWord ++ tailWord_2939925) baseStart_2939925 baseEnd_2939925 := by
    simpa [prefixWord, tailWord_2939925, baseEnd_2939925] using wordTrace_append hprefix tailTrace_2939925
  have hstable : (prefixWord ++ tailWord_2939925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939925).length < 2 ^ (prefixWord ++ tailWord_2939925).sum := by decide
  have hdescent : baseEnd_2939925 < baseStart_2939925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939965 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2939965 : Nat := 118140960795 + 2939965 * 2 ^ 59
def prefixEnd_2939965 : Nat := 4983230072969 + 3 ^ 40 * 2939965 * 2
def baseEnd_2939965 : Nat := 1509615152395695107116853

theorem tailTrace_2939965 : CollatzResearch.WordTrace tailWord_2939965 prefixEnd_2939965 1509615152395695107116853 := by
  unfold tailWord_2939965
  simp only [CollatzResearch.WordTrace]
  refine ⟨107229332794016385892405349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71486221862677590594936899 107229332794016385892405349)
  ·
    refine ⟨20105499898878072354826003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107229332794016385892405349 20105499898878072354826003)
    ·
      refine ⟨30158249848317108532239005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20105499898878072354826003 30158249848317108532239005)
      ·
        refine ⟨11309343693118915699589627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30158249848317108532239005 11309343693118915699589627)
        ·
          refine ⟨16964015539678373549384441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309343693118915699589627 16964015539678373549384441)
          ·
            refine ⟨12723011654758780162038331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16964015539678373549384441 12723011654758780162038331)
            ·
              refine ⟨19084517482138170243057497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723011654758780162038331 19084517482138170243057497)
              ·
                refine ⟨14313388111603627682293123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19084517482138170243057497 14313388111603627682293123)
                ·
                  refine ⟨21470082167405441523439685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14313388111603627682293123 21470082167405441523439685)
                  ·
                    refine ⟨4025640406388520285644941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21470082167405441523439685 4025640406388520285644941)
                    ·
                      refine ⟨1509615152395695107116853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025640406388520285644941 1509615152395695107116853)
                      ·
                        rfl

theorem cell23_2939965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2939965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939965 prefixEnd_2939965 := by exact prefixLift 2939965
  have htrace : WordTrace (prefixWord ++ tailWord_2939965) baseStart_2939965 baseEnd_2939965 := by
    simpa [prefixWord, tailWord_2939965, baseEnd_2939965] using wordTrace_append hprefix tailTrace_2939965
  have hstable : (prefixWord ++ tailWord_2939965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939965).length < 2 ^ (prefixWord ++ tailWord_2939965).sum := by decide
  have hdescent : baseEnd_2939965 < baseStart_2939965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940035 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4]
def baseStart_2940035 : Nat := 118140960795 + 2940035 * 2 ^ 59
def prefixEnd_2940035 : Nat := 4983230072969 + 3 ^ 40 * 2940035 * 2
def baseEnd_2940035 : Nat := 1509651096041509833241531

theorem tailTrace_2940035 : CollatzResearch.WordTrace tailWord_2940035 prefixEnd_2940035 1509651096041509833241531 := by
  unfold tailWord_2940035
  simp only [CollatzResearch.WordTrace]
  refine ⟨107231885903762787847453559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71487923935841858564969039 107231885903762787847453559)
  ·
    refine ⟨160847828855644181771180339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107231885903762787847453559 160847828855644181771180339)
    ·
      refine ⟨241271743283466272656770509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160847828855644181771180339 241271743283466272656770509)
      ·
        refine ⟨90476903731299852246288941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241271743283466272656770509 90476903731299852246288941)
        ·
          refine ⟨33928838899237444592358353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90476903731299852246288941 33928838899237444592358353)
          ·
            refine ⟨25446629174428083444268765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33928838899237444592358353 25446629174428083444268765)
            ·
              refine ⟨9542485940410531291600787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25446629174428083444268765 9542485940410531291600787)
              ·
                refine ⟨14313728910615796937401181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9542485940410531291600787 14313728910615796937401181)
                ·
                  refine ⟨5367648341480923851525443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14313728910615796937401181 5367648341480923851525443)
                  ·
                    refine ⟨8051472512221385777288165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5367648341480923851525443 8051472512221385777288165)
                    ·
                      refine ⟨1509651096041509833241531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8051472512221385777288165 1509651096041509833241531)
                      ·
                        rfl

theorem cell23_2940035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_2940035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940035 prefixEnd_2940035 := by exact prefixLift 2940035
  have htrace : WordTrace (prefixWord ++ tailWord_2940035) baseStart_2940035 baseEnd_2940035 := by
    simpa [prefixWord, tailWord_2940035, baseEnd_2940035] using wordTrace_append hprefix tailTrace_2940035
  have hstable : (prefixWord ++ tailWord_2940035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940035).length < 2 ^ (prefixWord ++ tailWord_2940035).sum := by decide
  have hdescent : baseEnd_2940035 < baseStart_2940035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940048 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_2940048 : Nat := 118140960795 + 2940048 * 2 ^ 59
def prefixEnd_2940048 : Nat := 4983230072969 + 3 ^ 40 * 2940048 * 2
def baseEnd_2940048 : Nat := 1509657771290018282378971

theorem tailTrace_2940048 : CollatzResearch.WordTrace tailWord_2940048 prefixEnd_2940048 1509657771290018282378971 := by
  unfold tailWord_2940048
  simp only [CollatzResearch.WordTrace]
  refine ⟨53616180026357845533838399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71488240035143794045117865 53616180026357845533838399)
  ·
    refine ⟨80424270039536768300757599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53616180026357845533838399 80424270039536768300757599)
    ·
      refine ⟨120636405059305152451136399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80424270039536768300757599 120636405059305152451136399)
      ·
        refine ⟨180954607588957728676704599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120636405059305152451136399 180954607588957728676704599)
        ·
          refine ⟨271431911383436593015056899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180954607588957728676704599 271431911383436593015056899)
          ·
            refine ⟨407147867075154889522585349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271431911383436593015056899 407147867075154889522585349)
            ·
              refine ⟨76340225076591541785484753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 407147867075154889522585349 76340225076591541785484753)
              ·
                refine ⟨57255168807443656339113565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76340225076591541785484753 57255168807443656339113565)
                ·
                  refine ⟨21470688302791371127167587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57255168807443656339113565 21470688302791371127167587)
                  ·
                    refine ⟨32206032454187056690751381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21470688302791371127167587 32206032454187056690751381)
                    ·
                      refine ⟨1509657771290018282378971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32206032454187056690751381 1509657771290018282378971)
                      ·
                        rfl

theorem cell23_2940048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_2940048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940048 prefixEnd_2940048 := by exact prefixLift 2940048
  have htrace : WordTrace (prefixWord ++ tailWord_2940048) baseStart_2940048 baseEnd_2940048 := by
    simpa [prefixWord, tailWord_2940048, baseEnd_2940048] using wordTrace_append hprefix tailTrace_2940048
  have hstable : (prefixWord ++ tailWord_2940048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940048).length < 2 ^ (prefixWord ++ tailWord_2940048).sum := by decide
  have hdescent : baseEnd_2940048 < baseStart_2940048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940065 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2940065 : Nat := 118140960795 + 2940065 * 2 ^ 59
def prefixEnd_2940065 : Nat := 4983230072969 + 3 ^ 40 * 2940065 * 2
def baseEnd_2940065 : Nat := 1509666500461144715866393

theorem tailTrace_2940065 : CollatzResearch.WordTrace tailWord_2940065 prefixEnd_2940065 1509666500461144715866393 := by
  unfold tailWord_2940065
  simp only [CollatzResearch.WordTrace]
  refine ⟨107232980093654102971045649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71488653395769401980697099 107232980093654102971045649)
  ·
    refine ⟨80424735070240577228284237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107232980093654102971045649 80424735070240577228284237)
    ·
      refine ⟨30159275651340216460606589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80424735070240577228284237 30159275651340216460606589)
      ·
        refine ⟨11309728369252581172727471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30159275651340216460606589 11309728369252581172727471)
        ·
          refine ⟨16964592553878871759091207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309728369252581172727471 16964592553878871759091207)
          ·
            refine ⟨25446888830818307638636811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16964592553878871759091207 25446888830818307638636811)
            ·
              refine ⟨38170333246227461457955217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25446888830818307638636811 38170333246227461457955217)
              ·
                refine ⟨28627749934670596093466413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38170333246227461457955217 28627749934670596093466413)
                ·
                  refine ⟨10735406225501473535049905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28627749934670596093466413 10735406225501473535049905)
                  ·
                    refine ⟨8051554669126105151287429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10735406225501473535049905 8051554669126105151287429)
                    ·
                      refine ⟨1509666500461144715866393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8051554669126105151287429 1509666500461144715866393)
                      ·
                        rfl

theorem cell23_2940065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2940065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940065 prefixEnd_2940065 := by exact prefixLift 2940065
  have htrace : WordTrace (prefixWord ++ tailWord_2940065) baseStart_2940065 baseEnd_2940065 := by
    simpa [prefixWord, tailWord_2940065, baseEnd_2940065] using wordTrace_append hprefix tailTrace_2940065
  have hstable : (prefixWord ++ tailWord_2940065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940065).length < 2 ^ (prefixWord ++ tailWord_2940065).sum := by decide
  have hdescent : baseEnd_2940065 < baseStart_2940065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940082 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_2940082 : Nat := 118140960795 + 2940082 * 2 ^ 59
def prefixEnd_2940082 : Nat := 4983230072969 + 3 ^ 40 * 2940082 * 2
def baseEnd_2940082 : Nat := 1509675229632271149353815

theorem tailTrace_2940082 : CollatzResearch.WordTrace tailWord_2940082 prefixEnd_2940082 1509675229632271149353815 := by
  unfold tailWord_2940082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808400033648128718603625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71489066756395009916276333 26808400033648128718603625)
  ·
    refine ⟨20106300025236096538952719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26808400033648128718603625 20106300025236096538952719)
    ·
      refine ⟨30159450037854144808429079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20106300025236096538952719 30159450037854144808429079)
      ·
        refine ⟨45239175056781217212643619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30159450037854144808429079 45239175056781217212643619)
        ·
          refine ⟨67858762585171825818965429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45239175056781217212643619 67858762585171825818965429)
          ·
            refine ⟨6361758992359858670528009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67858762585171825818965429 6361758992359858670528009)
            ·
              refine ⟨4771319244269894002896007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6361758992359858670528009 4771319244269894002896007)
              ·
                refine ⟨7156978866404841004344011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771319244269894002896007 7156978866404841004344011)
                ·
                  refine ⟨10735468299607261506516017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7156978866404841004344011 10735468299607261506516017)
                  ·
                    refine ⟨8051601224705446129887013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10735468299607261506516017 8051601224705446129887013)
                    ·
                      refine ⟨1509675229632271149353815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8051601224705446129887013 1509675229632271149353815)
                      ·
                        rfl

theorem cell23_2940082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_2940082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940082 prefixEnd_2940082 := by exact prefixLift 2940082
  have htrace : WordTrace (prefixWord ++ tailWord_2940082) baseStart_2940082 baseEnd_2940082 := by
    simpa [prefixWord, tailWord_2940082, baseEnd_2940082] using wordTrace_append hprefix tailTrace_2940082
  have hstable : (prefixWord ++ tailWord_2940082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940082).length < 2 ^ (prefixWord ++ tailWord_2940082).sum := by decide
  have hdescent : baseEnd_2940082 < baseStart_2940082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940092 : List Nat := [2, 2, 2, 3, 2, 2, 3, 7]
def baseStart_2940092 : Nat := 118140960795 + 2940092 * 2 ^ 59
def prefixEnd_2940092 : Nat := 4983230072969 + 3 ^ 40 * 2940092 * 2
def baseEnd_2940092 : Nat := 55914087571808004082547

theorem tailTrace_2940092 : CollatzResearch.WordTrace tailWord_2940092 prefixEnd_2940092 55914087571808004082547 := by
  unfold tailWord_2940092
  simp only [CollatzResearch.WordTrace]
  refine ⟨53616982432278143291139265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71489309909704191054852353 53616982432278143291139265)
  ·
    refine ⟨40212736824208607468354449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53616982432278143291139265 40212736824208607468354449)
    ·
      refine ⟨30159552618156455601265837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40212736824208607468354449 30159552618156455601265837)
      ·
        refine ⟨11309832231808670850474689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30159552618156455601265837 11309832231808670850474689)
        ·
          refine ⟨8482374173856503137856017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11309832231808670850474689 8482374173856503137856017)
          ·
            refine ⟨6361780630392377353392013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8482374173856503137856017 6361780630392377353392013)
            ·
              refine ⟨2385667736397141507522005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6361780630392377353392013 2385667736397141507522005)
              ·
                refine ⟨55914087571808004082547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2385667736397141507522005 55914087571808004082547)
                ·
                  rfl

theorem cell23_2940092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 7].length) (baseStart_2940092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940092 prefixEnd_2940092 := by exact prefixLift 2940092
  have htrace : WordTrace (prefixWord ++ tailWord_2940092) baseStart_2940092 baseEnd_2940092 := by
    simpa [prefixWord, tailWord_2940092, baseEnd_2940092] using wordTrace_append hprefix tailTrace_2940092
  have hstable : (prefixWord ++ tailWord_2940092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940092).length < 2 ^ (prefixWord ++ tailWord_2940092).sum := by decide
  have hdescent : baseEnd_2940092 < baseStart_2940092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940106 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_2940106 : Nat := 118140960795 + 2940106 * 2 ^ 59
def prefixEnd_2940106 : Nat := 4983230072969 + 3 ^ 40 * 2940106 * 2
def baseEnd_2940106 : Nat := 1509687553167979055453705

theorem tailTrace_2940106 : CollatzResearch.WordTrace tailWord_2940106 prefixEnd_2940106 1509687553167979055453705 := by
  unfold tailWord_2940106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808618871626391743322043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71489650324337044648858781 26808618871626391743322043)
  ·
    refine ⟨40212928307439587614983065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26808618871626391743322043 40212928307439587614983065)
    ·
      refine ⟨30159696230579690711237299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40212928307439587614983065 30159696230579690711237299)
      ·
        refine ⟨45239544345869536066855949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30159696230579690711237299 45239544345869536066855949)
        ·
          refine ⟨16964829129701076025070981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45239544345869536066855949 16964829129701076025070981)
          ·
            refine ⟨3180905461818951754700809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16964829129701076025070981 3180905461818951754700809)
            ·
              refine ⟨2385679096364213816025607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180905461818951754700809 2385679096364213816025607)
              ·
                refine ⟨3578518644546320724038411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385679096364213816025607 3578518644546320724038411)
                ·
                  refine ⟨5367777966819481086057617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578518644546320724038411 5367777966819481086057617)
                  ·
                    refine ⟨4025833475114610814543213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5367777966819481086057617 4025833475114610814543213)
                    ·
                      refine ⟨1509687553167979055453705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025833475114610814543213 1509687553167979055453705)
                      ·
                        rfl

theorem cell23_2940106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_2940106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940106 prefixEnd_2940106 := by exact prefixLift 2940106
  have htrace : WordTrace (prefixWord ++ tailWord_2940106) baseStart_2940106 baseEnd_2940106 := by
    simpa [prefixWord, tailWord_2940106, baseEnd_2940106] using wordTrace_append hprefix tailTrace_2940106
  have hstable : (prefixWord ++ tailWord_2940106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940106).length < 2 ^ (prefixWord ++ tailWord_2940106).sum := by decide
  have hdescent : baseEnd_2940106 < baseStart_2940106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940109 : List Nat := [1, 6, 2, 2, 1, 1, 10]
def baseStart_2940109 : Nat := 118140960795 + 2940109 * 2 ^ 59
def prefixEnd_2940109 : Nat := 4983230072969 + 3 ^ 40 * 2940109 * 2
def baseEnd_2940109 : Nat := 18638136958147438811311

theorem tailTrace_2940109 : CollatzResearch.WordTrace tailWord_2940109 prefixEnd_2940109 18638136958147438811311 := by
  unfold tailWord_2940109
  simp only [CollatzResearch.WordTrace]
  refine ⟨107234584905494698485647381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71489723270329798990431587 107234584905494698485647381)
  ·
    refine ⟨5026621167445063991514721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107234584905494698485647381 5026621167445063991514721)
    ·
      refine ⟨3769965875583797993636041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5026621167445063991514721 3769965875583797993636041)
      ·
        refine ⟨2827474406687848495227031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3769965875583797993636041 2827474406687848495227031)
        ·
          refine ⟨4241211610031772742840547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827474406687848495227031 4241211610031772742840547)
          ·
            refine ⟨6361817415047659114260821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241211610031772742840547 6361817415047659114260821)
            ·
              refine ⟨18638136958147438811311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6361817415047659114260821 18638136958147438811311)
              ·
                rfl

theorem cell23_2940109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 10].length) (baseStart_2940109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940109 prefixEnd_2940109 := by exact prefixLift 2940109
  have htrace : WordTrace (prefixWord ++ tailWord_2940109) baseStart_2940109 baseEnd_2940109 := by
    simpa [prefixWord, tailWord_2940109, baseEnd_2940109] using wordTrace_append hprefix tailTrace_2940109
  have hstable : (prefixWord ++ tailWord_2940109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940109).length < 2 ^ (prefixWord ++ tailWord_2940109).sum := by decide
  have hdescent : baseEnd_2940109 < baseStart_2940109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940119 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_2940119 : Nat := 118140960795 + 2940119 * 2 ^ 59
def prefixEnd_2940119 : Nat := 4983230072969 + 3 ^ 40 * 2940119 * 2
def baseEnd_2940119 : Nat := 1509694228416487504591145

theorem tailTrace_2940119 : CollatzResearch.WordTrace tailWord_2940119 prefixEnd_2940119 1509694228416487504591145 := by
  unfold tailWord_2940119
  simp only [CollatzResearch.WordTrace]
  refine ⟨107234949635458470193511411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71489966423638980129007607 107234949635458470193511411)
  ·
    refine ⟨160852424453187705290267117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107234949635458470193511411 160852424453187705290267117)
    ·
      refine ⟨60319659169945389483850169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160852424453187705290267117 60319659169945389483850169)
      ·
        refine ⟨45239744377459042112887627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60319659169945389483850169 45239744377459042112887627)
        ·
          refine ⟨67859616566188563169331441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45239744377459042112887627 67859616566188563169331441)
          ·
            refine ⟨50894712424641422376998581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67859616566188563169331441 50894712424641422376998581)
            ·
              refine ⟨4771379289810133347843617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50894712424641422376998581 4771379289810133347843617)
              ·
                refine ⟨3578534467357600010882713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771379289810133347843617 3578534467357600010882713)
                ·
                  refine ⟨2683900850518200008162035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578534467357600010882713 2683900850518200008162035)
                  ·
                    refine ⟨4025851275777300012243053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2683900850518200008162035 4025851275777300012243053)
                    ·
                      refine ⟨1509694228416487504591145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025851275777300012243053 1509694228416487504591145)
                      ·
                        rfl

theorem cell23_2940119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_2940119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940119 prefixEnd_2940119 := by exact prefixLift 2940119
  have htrace : WordTrace (prefixWord ++ tailWord_2940119) baseStart_2940119 baseEnd_2940119 := by
    simpa [prefixWord, tailWord_2940119, baseEnd_2940119] using wordTrace_append hprefix tailTrace_2940119
  have hstable : (prefixWord ++ tailWord_2940119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940119).length < 2 ^ (prefixWord ++ tailWord_2940119).sum := by decide
  have hdescent : baseEnd_2940119 < baseStart_2940119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940136 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2940136 : Nat := 118140960795 + 2940136 * 2 ^ 59
def prefixEnd_2940136 : Nat := 4983230072969 + 3 ^ 40 * 2940136 * 2
def baseEnd_2940136 : Nat := 1509702957587613938078567

theorem tailTrace_2940136 : CollatzResearch.WordTrace tailWord_2940136 prefixEnd_2940136 1509702957587613938078567 := by
  unfold tailWord_2940136
  simp only [CollatzResearch.WordTrace]
  refine ⟨53617784838198441048440131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71490379784264588064586841 53617784838198441048440131)
  ·
    refine ⟨80426677257297661572660197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53617784838198441048440131 80426677257297661572660197)
    ·
      refine ⟨15080001985743311544873787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80426677257297661572660197 15080001985743311544873787)
      ·
        refine ⟨22620002978614967317310681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080001985743311544873787 22620002978614967317310681)
        ·
          refine ⟨16965002233961225487983011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22620002978614967317310681 16965002233961225487983011)
          ·
            refine ⟨25447503350941838231974517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965002233961225487983011 25447503350941838231974517)
            ·
              refine ⟨2385703439150797334247611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25447503350941838231974517 2385703439150797334247611)
              ·
                refine ⟨3578555158726196001371417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385703439150797334247611 3578555158726196001371417)
                ·
                  refine ⟨2683916369044647001028563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578555158726196001371417 2683916369044647001028563)
                  ·
                    refine ⟨4025874553566970501542845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2683916369044647001028563 4025874553566970501542845)
                    ·
                      refine ⟨1509702957587613938078567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4025874553566970501542845 1509702957587613938078567)
                      ·
                        rfl

theorem cell23_2940136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2940136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940136 prefixEnd_2940136 := by exact prefixLift 2940136
  have htrace : WordTrace (prefixWord ++ tailWord_2940136) baseStart_2940136 baseEnd_2940136 := by
    simpa [prefixWord, tailWord_2940136, baseEnd_2940136] using wordTrace_append hprefix tailTrace_2940136
  have hstable : (prefixWord ++ tailWord_2940136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940136).length < 2 ^ (prefixWord ++ tailWord_2940136).sum := by decide
  have hdescent : baseEnd_2940136 < baseStart_2940136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940145 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2940145 : Nat := 118140960795 + 2940145 * 2 ^ 59
def prefixEnd_2940145 : Nat := 4983230072969 + 3 ^ 40 * 2940145 * 2
def baseEnd_2940145 : Nat := 1509707578913504402866025

theorem tailTrace_2940145 : CollatzResearch.WordTrace tailWord_2940145 prefixEnd_2940145 1509707578913504402866025 := by
  unfold tailWord_2940145
  simp only [CollatzResearch.WordTrace]
  refine ⟨107235897933364276633957889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71490598622242851089305259 107235897933364276633957889)
  ·
    refine ⟨80426923450023207475468417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107235897933364276633957889 80426923450023207475468417)
    ·
      refine ⟨60320192587517405606601313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80426923450023207475468417 60320192587517405606601313)
      ·
        refine ⟨45240144440638054204950985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60320192587517405606601313 45240144440638054204950985)
        ·
          refine ⟨33930108330478540653713239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45240144440638054204950985 33930108330478540653713239)
          ·
            refine ⟨50895162495717810980569859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33930108330478540653713239 50895162495717810980569859)
            ·
              refine ⟨76342743743576716470854789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50895162495717810980569859 76342743743576716470854789)
              ·
                refine ⟨14314264451920634338285273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76342743743576716470854789 14314264451920634338285273)
                ·
                  refine ⟨10735698338940475753713955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14314264451920634338285273 10735698338940475753713955)
                  ·
                    refine ⟨16103547508410713630570933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10735698338940475753713955 16103547508410713630570933)
                    ·
                      refine ⟨1509707578913504402866025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16103547508410713630570933 1509707578913504402866025)
                      ·
                        rfl

theorem cell23_2940145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2940145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940145 prefixEnd_2940145 := by exact prefixLift 2940145
  have htrace : WordTrace (prefixWord ++ tailWord_2940145) baseStart_2940145 baseEnd_2940145 := by
    simpa [prefixWord, tailWord_2940145, baseEnd_2940145] using wordTrace_append hprefix tailTrace_2940145
  have hstable : (prefixWord ++ tailWord_2940145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940145).length < 2 ^ (prefixWord ++ tailWord_2940145).sum := by decide
  have hdescent : baseEnd_2940145 < baseStart_2940145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940159 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 4, 2, 2]
def baseStart_2940159 : Nat := 118140960795 + 2940159 * 2 ^ 59
def prefixEnd_2940159 : Nat := 4983230072969 + 3 ^ 40 * 2940159 * 2
def baseEnd_2940159 : Nat := 1509714767642667348090961

theorem tailTrace_2940159 : CollatzResearch.WordTrace tailWord_2940159 prefixEnd_2940159 1509714767642667348090961 := by
  unfold tailWord_2940159
  simp only [CollatzResearch.WordTrace]
  refine ⟨107236408555313557024967531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71490939036875704683311687 107236408555313557024967531)
  ·
    refine ⟨160854612832970335537451297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107236408555313557024967531 160854612832970335537451297)
    ·
      refine ⟨120640959624727751653088473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160854612832970335537451297 120640959624727751653088473)
      ·
        refine ⟨90480719718545813739816355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120640959624727751653088473 90480719718545813739816355)
        ·
          refine ⟨135721079577818720609724533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90480719718545813739816355 135721079577818720609724533)
          ·
            refine ⟨12723851210420505057161675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135721079577818720609724533 12723851210420505057161675)
            ·
              refine ⟨19085776815630757585742513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723851210420505057161675 19085776815630757585742513)
              ·
                refine ⟨14314332611723068189306885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19085776815630757585742513 14314332611723068189306885)
                ·
                  refine ⟨2683937364698075285495041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14314332611723068189306885 2683937364698075285495041)
                  ·
                    refine ⟨2012953023523556464121281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2683937364698075285495041 2012953023523556464121281)
                    ·
                      refine ⟨1509714767642667348090961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012953023523556464121281 1509714767642667348090961)
                      ·
                        rfl

theorem cell23_2940159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_2940159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940159 prefixEnd_2940159 := by exact prefixLift 2940159
  have htrace : WordTrace (prefixWord ++ tailWord_2940159) baseStart_2940159 baseEnd_2940159 := by
    simpa [prefixWord, tailWord_2940159, baseEnd_2940159] using wordTrace_append hprefix tailTrace_2940159
  have hstable : (prefixWord ++ tailWord_2940159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940159).length < 2 ^ (prefixWord ++ tailWord_2940159).sum := by decide
  have hdescent : baseEnd_2940159 < baseStart_2940159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940222 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2940222 : Nat := 118140960795 + 2940222 * 2 ^ 59
def prefixEnd_2940222 : Nat := 4983230072969 + 3 ^ 40 * 2940222 * 2
def baseEnd_2940222 : Nat := 1509747116923900601603171

theorem tailTrace_2940222 : CollatzResearch.WordTrace tailWord_2940222 prefixEnd_2940222 1509747116923900601603171 := by
  unfold tailWord_2940222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13404838294260664848063865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71492470902723545856340613 13404838294260664848063865)
  ·
    refine ⟨10053628720695498636047899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13404838294260664848063865 10053628720695498636047899)
    ·
      refine ⟨15080443081043247954071849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053628720695498636047899 15080443081043247954071849)
      ·
        refine ⟨11310332310782435965553887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15080443081043247954071849 11310332310782435965553887)
        ·
          refine ⟨16965498466173653948330831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310332310782435965553887 16965498466173653948330831)
          ·
            refine ⟨25448247699260480922496247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965498466173653948330831 25448247699260480922496247)
            ·
              refine ⟨38172371548890721383744371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25448247699260480922496247 38172371548890721383744371)
              ·
                refine ⟨57258557323336082075616557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38172371548890721383744371 57258557323336082075616557)
                ·
                  refine ⟨21471958996251030778356209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57258557323336082075616557 21471958996251030778356209)
                  ·
                    refine ⟨16103969247188273083767157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21471958996251030778356209 16103969247188273083767157)
                    ·
                      refine ⟨1509747116923900601603171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16103969247188273083767157 1509747116923900601603171)
                      ·
                        rfl

theorem cell23_2940222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2940222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940222 prefixEnd_2940222 := by exact prefixLift 2940222
  have htrace : WordTrace (prefixWord ++ tailWord_2940222) baseStart_2940222 baseEnd_2940222 := by
    simpa [prefixWord, tailWord_2940222, baseEnd_2940222] using wordTrace_append hprefix tailTrace_2940222
  have hstable : (prefixWord ++ tailWord_2940222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940222).length < 2 ^ (prefixWord ++ tailWord_2940222).sum := by decide
  have hdescent : baseEnd_2940222 < baseStart_2940222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940255 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 10]
def baseStart_2940255 : Nat := 118140960795 + 2940255 * 2 ^ 59
def prefixEnd_2940255 : Nat := 4983230072969 + 3 ^ 40 * 2940255 * 2
def baseEnd_2940255 : Nat := 167751562420610996943391

theorem tailTrace_2940255 : CollatzResearch.WordTrace tailWord_2940255 prefixEnd_2940255 167751562420610996943391 := by
  unfold tailWord_2940255
  simp only [CollatzResearch.WordTrace]
  refine ⟨107239909962965765420462219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71493273308643843613641479 107239909962965765420462219)
  ·
    refine ⟨160859864944448648130693329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107239909962965765420462219 160859864944448648130693329)
    ·
      refine ⟨120644898708336486098019997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160859864944448648130693329 120644898708336486098019997)
      ·
        refine ⟨45241837015626182286757499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120644898708336486098019997 45241837015626182286757499)
        ·
          refine ⟨67862755523439273430136249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45241837015626182286757499 67862755523439273430136249)
          ·
            refine ⟨50897066642579455072602187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67862755523439273430136249 50897066642579455072602187)
            ·
              refine ⟨76345599963869182608903281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50897066642579455072602187 76345599963869182608903281)
              ·
                refine ⟨57259199972901886956677461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76345599963869182608903281 57259199972901886956677461)
                ·
                  refine ⟨167751562420610996943391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57259199972901886956677461 167751562420610996943391)
                  ·
                    rfl

theorem cell23_2940255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 10].length) (baseStart_2940255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940255 prefixEnd_2940255 := by exact prefixLift 2940255
  have htrace : WordTrace (prefixWord ++ tailWord_2940255) baseStart_2940255 baseEnd_2940255 := by
    simpa [prefixWord, tailWord_2940255, baseEnd_2940255] using wordTrace_append hprefix tailTrace_2940255
  have hstable : (prefixWord ++ tailWord_2940255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940255).length < 2 ^ (prefixWord ++ tailWord_2940255).sum := by decide
  have hdescent : baseEnd_2940255 < baseStart_2940255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940259 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 3, 4]
def baseStart_2940259 : Nat := 118140960795 + 2940259 * 2 ^ 59
def prefixEnd_2940259 : Nat := 4983230072969 + 3 ^ 40 * 2940259 * 2
def baseEnd_2940259 : Nat := 503255371902705652280167

theorem tailTrace_2940259 : CollatzResearch.WordTrace tailWord_2940259 prefixEnd_2940259 503255371902705652280167 := by
  unfold tailWord_2940259
  simp only [CollatzResearch.WordTrace]
  refine ⟨107240055854951274103607831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71493370569967516069071887 107240055854951274103607831)
  ·
    refine ⟨160860083782426911155411747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107240055854951274103607831 160860083782426911155411747)
    ·
      refine ⟨241290125673640366733117621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160860083782426911155411747 241290125673640366733117621)
      ·
        refine ⟨22620949281903784381229777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241290125673640366733117621 22620949281903784381229777)
        ·
          refine ⟨16965711961427838285922333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22620949281903784381229777 16965711961427838285922333)
          ·
            refine ⟨6362141985535439357220875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16965711961427838285922333 6362141985535439357220875)
            ·
              refine ⟨9543212978303159035831313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362141985535439357220875 9543212978303159035831313)
              ·
                refine ⟨7157409733727369276873485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9543212978303159035831313 7157409733727369276873485)
                ·
                  refine ⟨2684028650147763478827557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7157409733727369276873485 2684028650147763478827557)
                  ·
                    refine ⟨503255371902705652280167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684028650147763478827557 503255371902705652280167)
                    ·
                      rfl

theorem cell23_2940259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 4].length) (baseStart_2940259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940259 prefixEnd_2940259 := by exact prefixLift 2940259
  have htrace : WordTrace (prefixWord ++ tailWord_2940259) baseStart_2940259 baseEnd_2940259 := by
    simpa [prefixWord, tailWord_2940259, baseEnd_2940259] using wordTrace_append hprefix tailTrace_2940259
  have hstable : (prefixWord ++ tailWord_2940259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940259).length < 2 ^ (prefixWord ++ tailWord_2940259).sum := by decide
  have hdescent : baseEnd_2940259 < baseStart_2940259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940269 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2940269 : Nat := 118140960795 + 2940269 * 2 ^ 59
def prefixEnd_2940269 : Nat := 4983230072969 + 3 ^ 40 * 2940269 * 2
def baseEnd_2940269 : Nat := 1509771250514661917715455

theorem tailTrace_2940269 : CollatzResearch.WordTrace tailWord_2940269 prefixEnd_2940269 1509771250514661917715455 := by
  unfold tailWord_2940269
  simp only [CollatzResearch.WordTrace]
  refine ⟨107240420584915045811471861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71493613723276697207647907 107240420584915045811471861)
  ·
    refine ⟨10053789429835785544825487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107240420584915045811471861 10053789429835785544825487)
    ·
      refine ⟨15080684144753678317238231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053789429835785544825487 15080684144753678317238231)
      ·
        refine ⟨22621026217130517475857347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080684144753678317238231 22621026217130517475857347)
        ·
          refine ⟨33931539325695776213786021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22621026217130517475857347 33931539325695776213786021)
          ·
            refine ⟨6362163623567958040084879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33931539325695776213786021 6362163623567958040084879)
            ·
              refine ⟨9543245435351937060127319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362163623567958040084879 9543245435351937060127319)
              ·
                refine ⟨14314868153027905590190979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9543245435351937060127319 14314868153027905590190979)
                ·
                  refine ⟨21472302229541858385286469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14314868153027905590190979 21472302229541858385286469)
                  ·
                    refine ⟨4026056668039098447241213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21472302229541858385286469 4026056668039098447241213)
                    ·
                      refine ⟨1509771250514661917715455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026056668039098447241213 1509771250514661917715455)
                      ·
                        rfl

theorem cell23_2940269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2940269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940269 prefixEnd_2940269 := by exact prefixLift 2940269
  have htrace : WordTrace (prefixWord ++ tailWord_2940269) baseStart_2940269 baseEnd_2940269 := by
    simpa [prefixWord, tailWord_2940269, baseEnd_2940269] using wordTrace_append hprefix tailTrace_2940269
  have hstable : (prefixWord ++ tailWord_2940269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940269).length < 2 ^ (prefixWord ++ tailWord_2940269).sum := by decide
  have hdescent : baseEnd_2940269 < baseStart_2940269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940275 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_2940275 : Nat := 118140960795 + 2940275 * 2 ^ 59
def prefixEnd_2940275 : Nat := 4983230072969 + 3 ^ 40 * 2940275 * 2
def baseEnd_2940275 : Nat := 1509774331398588894240427

theorem tailTrace_2940275 : CollatzResearch.WordTrace tailWord_2940275 prefixEnd_2940275 1509774331398588894240427 := by
  unfold tailWord_2940275
  simp only [CollatzResearch.WordTrace]
  refine ⟨107240639422893308836190279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71493759615262205890793519 107240639422893308836190279)
  ·
    refine ⟨160860959134339963254285419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107240639422893308836190279 160860959134339963254285419)
    ·
      refine ⟨241291438701509944881428129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160860959134339963254285419 241291438701509944881428129)
      ·
        refine ⟨180968579026132458661071097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241291438701509944881428129 180968579026132458661071097)
        ·
          refine ⟨135726434269599343995803323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180968579026132458661071097 135726434269599343995803323)
          ·
            refine ⟨203589651404399015993704985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135726434269599343995803323 203589651404399015993704985)
            ·
              refine ⟨152692238553299261995278739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203589651404399015993704985 152692238553299261995278739)
              ·
                refine ⟨229038357829948892992918109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152692238553299261995278739 229038357829948892992918109)
                ·
                  refine ⟨85889384186230834872344291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229038357829948892992918109 85889384186230834872344291)
                  ·
                    refine ⟨128834076279346252308516437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85889384186230834872344291 128834076279346252308516437)
                    ·
                      refine ⟨1509774331398588894240427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128834076279346252308516437 1509774331398588894240427)
                      ·
                        rfl

theorem cell23_2940275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_2940275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940275 prefixEnd_2940275 := by exact prefixLift 2940275
  have htrace : WordTrace (prefixWord ++ tailWord_2940275) baseStart_2940275 baseEnd_2940275 := by
    simpa [prefixWord, tailWord_2940275, baseEnd_2940275] using wordTrace_append hprefix tailTrace_2940275
  have hstable : (prefixWord ++ tailWord_2940275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940275).length < 2 ^ (prefixWord ++ tailWord_2940275).sum := by decide
  have hdescent : baseEnd_2940275 < baseStart_2940275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940289 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 8]
def baseStart_2940289 : Nat := 118140960795 + 2940289 * 2 ^ 59
def prefixEnd_2940289 : Nat := 4983230072969 + 3 ^ 40 * 2940289 * 2
def baseEnd_2940289 : Nat := 167753502236416871051707

theorem tailTrace_2940289 : CollatzResearch.WordTrace tailWord_2940289 prefixEnd_2940289 167753502236416871051707 := by
  unfold tailWord_2940289
  simp only [CollatzResearch.WordTrace]
  refine ⟨107241150044842589227199921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71494100029895059484799947 107241150044842589227199921)
  ·
    refine ⟨80430862533631941920399941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107241150044842589227199921 80430862533631941920399941)
    ·
      refine ⟨15080786725055989110074989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80430862533631941920399941 15080786725055989110074989)
      ·
        refine ⟨5655295021895995916278121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15080786725055989110074989 5655295021895995916278121)
        ·
          refine ⟨4241471266421996937208591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5655295021895995916278121 4241471266421996937208591)
          ·
            refine ⟨6362206899632995405812887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241471266421996937208591 6362206899632995405812887)
            ·
              refine ⟨9543310349449493108719331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362206899632995405812887 9543310349449493108719331)
              ·
                refine ⟨14314965524174239663078997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9543310349449493108719331 14314965524174239663078997)
                ·
                  refine ⟨167753502236416871051707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14314965524174239663078997 167753502236416871051707)
                  ·
                    rfl

theorem cell23_2940289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_2940289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940289 prefixEnd_2940289 := by exact prefixLift 2940289
  have htrace : WordTrace (prefixWord ++ tailWord_2940289) baseStart_2940289 baseEnd_2940289 := by
    simpa [prefixWord, tailWord_2940289, baseEnd_2940289] using wordTrace_append hprefix tailTrace_2940289
  have hstable : (prefixWord ++ tailWord_2940289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940289).length < 2 ^ (prefixWord ++ tailWord_2940289).sum := by decide
  have hdescent : baseEnd_2940289 < baseStart_2940289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940292 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2940292 : Nat := 118140960795 + 2940292 * 2 ^ 59
def prefixEnd_2940292 : Nat := 4983230072969 + 3 ^ 40 * 2940292 * 2
def baseEnd_2940292 : Nat := 1509783060569715327727849

theorem tailTrace_2940292 : CollatzResearch.WordTrace tailWord_2940292 prefixEnd_2940292 1509783060569715327727849 := by
  unfold tailWord_2940292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53620629731915860369779565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71494172975887813826372753 53620629731915860369779565)
  ·
    refine ⟨20107736149468447638667337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53620629731915860369779565 20107736149468447638667337)
    ·
      refine ⟨15080802112101335729000503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20107736149468447638667337 15080802112101335729000503)
      ·
        refine ⟨22621203168152003593500755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080802112101335729000503 22621203168152003593500755)
        ·
          refine ⟨33931804752228005390251133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22621203168152003593500755 33931804752228005390251133)
          ·
            refine ⟨12724426782085502021344175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33931804752228005390251133 12724426782085502021344175)
            ·
              refine ⟨19086640173128253032016263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724426782085502021344175 19086640173128253032016263)
              ·
                refine ⟨28629960259692379548024395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19086640173128253032016263 28629960259692379548024395)
                ·
                  refine ⟨42944940389538569322036593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28629960259692379548024395 42944940389538569322036593)
                  ·
                    refine ⟨32208705292153926991527445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42944940389538569322036593 32208705292153926991527445)
                    ·
                      refine ⟨1509783060569715327727849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32208705292153926991527445 1509783060569715327727849)
                      ·
                        rfl

theorem cell23_2940292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2940292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940292 prefixEnd_2940292 := by exact prefixLift 2940292
  have htrace : WordTrace (prefixWord ++ tailWord_2940292) baseStart_2940292 baseEnd_2940292 := by
    simpa [prefixWord, tailWord_2940292, baseEnd_2940292] using wordTrace_append hprefix tailTrace_2940292
  have hstable : (prefixWord ++ tailWord_2940292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940292).length < 2 ^ (prefixWord ++ tailWord_2940292).sum := by decide
  have hdescent : baseEnd_2940292 < baseStart_2940292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940309 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_2940309 : Nat := 118140960795 + 2940309 * 2 ^ 59
def prefixEnd_2940309 : Nat := 4983230072969 + 3 ^ 40 * 2940309 * 2
def baseEnd_2940309 : Nat := 1509791789740841761215271

theorem tailTrace_2940309 : CollatzResearch.WordTrace tailWord_2940309 prefixEnd_2940309 1509791789740841761215271 := by
  unfold tailWord_2940309
  simp only [CollatzResearch.WordTrace]
  refine ⟨107241879504770132642927981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71494586336513421761951987 107241879504770132642927981)
  ·
    refine ⟨40215704814288799741097993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107241879504770132642927981 40215704814288799741097993)
    ·
      refine ⟨30161778610716599805823495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40215704814288799741097993 30161778610716599805823495)
      ·
        refine ⟨45242667916074899708735243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30161778610716599805823495 45242667916074899708735243)
        ·
          refine ⟨67864001874112349563102865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45242667916074899708735243 67864001874112349563102865)
          ·
            refine ⟨50898001405584262172327149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67864001874112349563102865 50898001405584262172327149)
            ·
              refine ⟨19086750527094098314622681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50898001405584262172327149 19086750527094098314622681)
              ·
                refine ⟨14315062895320573735967011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19086750527094098314622681 14315062895320573735967011)
                ·
                  refine ⟨21472594342980860603950517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14315062895320573735967011 21472594342980860603950517)
                  ·
                    refine ⟨2013055719654455681620361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21472594342980860603950517 2013055719654455681620361)
                    ·
                      refine ⟨1509791789740841761215271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013055719654455681620361 1509791789740841761215271)
                      ·
                        rfl

theorem cell23_2940309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_2940309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940309 prefixEnd_2940309 := by exact prefixLift 2940309
  have htrace : WordTrace (prefixWord ++ tailWord_2940309) baseStart_2940309 baseEnd_2940309 := by
    simpa [prefixWord, tailWord_2940309, baseEnd_2940309] using wordTrace_append hprefix tailTrace_2940309
  have hstable : (prefixWord ++ tailWord_2940309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940309).length < 2 ^ (prefixWord ++ tailWord_2940309).sum := by decide
  have hdescent : baseEnd_2940309 < baseStart_2940309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940319 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 1, 5]
def baseStart_2940319 : Nat := 118140960795 + 2940319 * 2 ^ 59
def prefixEnd_2940319 : Nat := 4983230072969 + 3 ^ 40 * 2940319 * 2
def baseEnd_2940319 : Nat := 503265641515795574030075

theorem tailTrace_2940319 : CollatzResearch.WordTrace tailWord_2940319 prefixEnd_2940319 503265641515795574030075 := by
  unfold tailWord_2940319
  simp only [CollatzResearch.WordTrace]
  refine ⟨107242244234733904350792011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71494829489822602900528007 107242244234733904350792011)
  ·
    refine ⟨160863366352100856526188017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107242244234733904350792011 160863366352100856526188017)
    ·
      refine ⟨120647524764075642394641013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160863366352100856526188017 120647524764075642394641013)
      ·
        refine ⟨11310705446632091474497595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120647524764075642394641013 11310705446632091474497595)
        ·
          refine ⟨16966058169948137211746393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310705446632091474497595 16966058169948137211746393)
          ·
            refine ⟨12724543627461102908809795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16966058169948137211746393 12724543627461102908809795)
            ·
              refine ⟨19086815441191654363214693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724543627461102908809795 19086815441191654363214693)
              ·
                refine ⟨3578777895223435193102755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19086815441191654363214693 3578777895223435193102755)
                ·
                  refine ⟨5368166842835152789654133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578777895223435193102755 5368166842835152789654133)
                  ·
                    refine ⟨503265641515795574030075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5368166842835152789654133 503265641515795574030075)
                    ·
                      rfl

theorem cell23_2940319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_2940319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940319 prefixEnd_2940319 := by exact prefixLift 2940319
  have htrace : WordTrace (prefixWord ++ tailWord_2940319) baseStart_2940319 baseEnd_2940319 := by
    simpa [prefixWord, tailWord_2940319, baseEnd_2940319] using wordTrace_append hprefix tailTrace_2940319
  have hstable : (prefixWord ++ tailWord_2940319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940319).length < 2 ^ (prefixWord ++ tailWord_2940319).sum := by decide
  have hdescent : baseEnd_2940319 < baseStart_2940319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940332 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_2940332 : Nat := 118140960795 + 2940332 * 2 ^ 59
def prefixEnd_2940332 : Nat := 4983230072969 + 3 ^ 40 * 2940332 * 2
def baseEnd_2940332 : Nat := 503267866598631723742555

theorem tailTrace_2940332 : CollatzResearch.WordTrace tailWord_2940332 prefixEnd_2940332 503267866598631723742555 := by
  unfold tailWord_2940332
  simp only [CollatzResearch.WordTrace]
  refine ⟨53621359191843403785507625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71495145589124538380676833 53621359191843403785507625)
  ·
    refine ⟨40216019393882552839130719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53621359191843403785507625 40216019393882552839130719)
    ·
      refine ⟨60324029090823829258696079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40216019393882552839130719 60324029090823829258696079)
      ·
        refine ⟨90486043636235743888044119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60324029090823829258696079 90486043636235743888044119)
        ·
          refine ⟨135729065454353615832066179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90486043636235743888044119 135729065454353615832066179)
          ·
            refine ⟨203593598181530423748099269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135729065454353615832066179 203593598181530423748099269)
            ·
              refine ⟨38173799659036954452768613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203593598181530423748099269 38173799659036954452768613)
              ·
                refine ⟨7157587436069428959894115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38173799659036954452768613 7157587436069428959894115)
                ·
                  refine ⟨10736381154104143439841173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157587436069428959894115 10736381154104143439841173)
                  ·
                    refine ⟨503267866598631723742555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10736381154104143439841173 503267866598631723742555)
                    ·
                      rfl

theorem cell23_2940332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_2940332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940332 prefixEnd_2940332 := by exact prefixLift 2940332
  have htrace : WordTrace (prefixWord ++ tailWord_2940332) baseStart_2940332 baseEnd_2940332 := by
    simpa [prefixWord, tailWord_2940332, baseEnd_2940332] using wordTrace_append hprefix tailTrace_2940332
  have hstable : (prefixWord ++ tailWord_2940332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940332).length < 2 ^ (prefixWord ++ tailWord_2940332).sum := by decide
  have hdescent : baseEnd_2940332 < baseStart_2940332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940349 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2940349 : Nat := 118140960795 + 2940349 * 2 ^ 59
def prefixEnd_2940349 : Nat := 4983230072969 + 3 ^ 40 * 2940349 * 2
def baseEnd_2940349 : Nat := 503270776322340534905029

theorem tailTrace_2940349 : CollatzResearch.WordTrace tailWord_2940349 prefixEnd_2940349 503270776322340534905029 := by
  unfold tailWord_2940349
  simp only [CollatzResearch.WordTrace]
  refine ⟨107243338424625219474384101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71495558949750146316256067 107243338424625219474384101)
  ·
    refine ⟨20108125954617228651447019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107243338424625219474384101 20108125954617228651447019)
    ·
      refine ⟨30162188931925842977170529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20108125954617228651447019 30162188931925842977170529)
      ·
        refine ⟨22621641698944382232877897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30162188931925842977170529 22621641698944382232877897)
        ·
          refine ⟨16966231274208286674658423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22621641698944382232877897 16966231274208286674658423)
          ·
            refine ⟨25449346911312430011987635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16966231274208286674658423 25449346911312430011987635)
            ·
              refine ⟨38174020366968645017981453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25449346911312430011987635 38174020366968645017981453)
              ·
                refine ⟨14315257637613241881743045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38174020366968645017981453 14315257637613241881743045)
                ·
                  refine ⟨2684110807052482852826821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14315257637613241881743045 2684110807052482852826821)
                  ·
                    refine ⟨503270776322340534905029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684110807052482852826821 503270776322340534905029)
                    ·
                      rfl

theorem cell23_2940349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2940349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940349 prefixEnd_2940349 := by exact prefixLift 2940349
  have htrace : WordTrace (prefixWord ++ tailWord_2940349) baseStart_2940349 baseEnd_2940349 := by
    simpa [prefixWord, tailWord_2940349, baseEnd_2940349] using wordTrace_append hprefix tailTrace_2940349
  have hstable : (prefixWord ++ tailWord_2940349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940349).length < 2 ^ (prefixWord ++ tailWord_2940349).sum := by decide
  have hdescent : baseEnd_2940349 < baseStart_2940349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940352 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_2940352 : Nat := 118140960795 + 2940352 * 2 ^ 59
def prefixEnd_2940352 : Nat := 4983230072969 + 3 ^ 40 * 2940352 * 2
def baseEnd_2940352 : Nat := 1509813869408985092977573

theorem tailTrace_2940352 : CollatzResearch.WordTrace tailWord_2940352 prefixEnd_2940352 1509813869408985092977573 := by
  unfold tailWord_2940352
  simp only [CollatzResearch.WordTrace]
  refine ⟨53621723921807175493371655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71495631895742900657828873 53621723921807175493371655)
  ·
    refine ⟨80432585882710763240057483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53621723921807175493371655 80432585882710763240057483)
    ·
      refine ⟨120648878824066144860086225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80432585882710763240057483 120648878824066144860086225)
      ·
        refine ⟨90486659118049608645064669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120648878824066144860086225 90486659118049608645064669)
        ·
          refine ⟨33932497169268603241899251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90486659118049608645064669 33932497169268603241899251)
          ·
            refine ⟨50898745753902904862848877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33932497169268603241899251 50898745753902904862848877)
            ·
              refine ⟨19087029657713589323568329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50898745753902904862848877 19087029657713589323568329)
              ·
                refine ⟨14315272243285191992676247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19087029657713589323568329 14315272243285191992676247)
                ·
                  refine ⟨21472908364927787989014371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14315272243285191992676247 21472908364927787989014371)
                  ·
                    refine ⟨32209362547391681983521557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21472908364927787989014371 32209362547391681983521557)
                    ·
                      refine ⟨1509813869408985092977573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32209362547391681983521557 1509813869408985092977573)
                      ·
                        rfl

theorem cell23_2940352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_2940352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940352 prefixEnd_2940352 := by exact prefixLift 2940352
  have htrace : WordTrace (prefixWord ++ tailWord_2940352) baseStart_2940352 baseEnd_2940352 := by
    simpa [prefixWord, tailWord_2940352, baseEnd_2940352] using wordTrace_append hprefix tailTrace_2940352
  have hstable : (prefixWord ++ tailWord_2940352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940352).length < 2 ^ (prefixWord ++ tailWord_2940352).sum := by decide
  have hdescent : baseEnd_2940352 < baseStart_2940352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940359 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_2940359 : Nat := 118140960795 + 2940359 * 2 ^ 59
def prefixEnd_2940359 : Nat := 4983230072969 + 3 ^ 40 * 2940359 * 2
def baseEnd_2940359 : Nat := 1509817463773566565590041

theorem tailTrace_2940359 : CollatzResearch.WordTrace tailWord_2940359 prefixEnd_2940359 1509817463773566565590041 := by
  unfold tailWord_2940359
  simp only [CollatzResearch.WordTrace]
  refine ⟨107243703154588991182248131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71495802103059327454832087 107243703154588991182248131)
  ·
    refine ⟨160865554731883486773372197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107243703154588991182248131 160865554731883486773372197)
    ·
      refine ⟨30162291512228153770007287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160865554731883486773372197 30162291512228153770007287)
      ·
        refine ⟨45243437268342230655010931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30162291512228153770007287 45243437268342230655010931)
        ·
          refine ⟨67865155902513345982516397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45243437268342230655010931 67865155902513345982516397)
          ·
            refine ⟨25449433463442504743443649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67865155902513345982516397 25449433463442504743443649)
            ·
              refine ⟨19087075097581878557582737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25449433463442504743443649 19087075097581878557582737)
              ·
                refine ⟨14315306323186408918187053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19087075097581878557582737 14315306323186408918187053)
                ·
                  refine ⟨5368239871194903344320145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14315306323186408918187053 5368239871194903344320145)
                  ·
                    refine ⟨4026179903396177508240109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5368239871194903344320145 4026179903396177508240109)
                    ·
                      refine ⟨1509817463773566565590041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026179903396177508240109 1509817463773566565590041)
                      ·
                        rfl

theorem cell23_2940359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_2940359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940359 prefixEnd_2940359 := by exact prefixLift 2940359
  have htrace : WordTrace (prefixWord ++ tailWord_2940359) baseStart_2940359 baseEnd_2940359 := by
    simpa [prefixWord, tailWord_2940359, baseEnd_2940359] using wordTrace_append hprefix tailTrace_2940359
  have hstable : (prefixWord ++ tailWord_2940359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940359).length < 2 ^ (prefixWord ++ tailWord_2940359).sum := by decide
  have hdescent : baseEnd_2940359 < baseStart_2940359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940362 : List Nat := [3, 1, 2, 1, 2, 3, 1, 10]
def baseStart_2940362 : Nat := 118140960795 + 2940362 * 2 ^ 59
def prefixEnd_2940362 : Nat := 4983230072969 + 3 ^ 40 * 2940362 * 2
def baseEnd_2940362 : Nat := 55919222378352964957501

theorem tailTrace_2940362 : CollatzResearch.WordTrace tailWord_2940362 prefixEnd_2940362 55919222378352964957501 := by
  unfold tailWord_2940362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810953143394530673651835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71495875049052081796404893 26810953143394530673651835)
  ·
    refine ⟨40216429715091796010477753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26810953143394530673651835 40216429715091796010477753)
    ·
      refine ⟨30162322286318847007858315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40216429715091796010477753 30162322286318847007858315)
      ·
        refine ⟨45243483429478270511787473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30162322286318847007858315 45243483429478270511787473)
        ·
          refine ⟨33932612572108702883840605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45243483429478270511787473 33932612572108702883840605)
          ·
            refine ⟨12724729714540763581440227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33932612572108702883840605 12724729714540763581440227)
            ·
              refine ⟨19087094571811145372160341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724729714540763581440227 19087094571811145372160341)
              ·
                refine ⟨55919222378352964957501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19087094571811145372160341 55919222378352964957501)
                ·
                  rfl

theorem cell23_2940362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_2940362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940362 prefixEnd_2940362 := by exact prefixLift 2940362
  have htrace : WordTrace (prefixWord ++ tailWord_2940362) baseStart_2940362 baseEnd_2940362 := by
    simpa [prefixWord, tailWord_2940362, baseEnd_2940362] using wordTrace_append hprefix tailTrace_2940362
  have hstable : (prefixWord ++ tailWord_2940362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940362).length < 2 ^ (prefixWord ++ tailWord_2940362).sum := by decide
  have hdescent : baseEnd_2940362 < baseStart_2940362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940376 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_2940376 : Nat := 118140960795 + 2940376 * 2 ^ 59
def prefixEnd_2940376 : Nat := 4983230072969 + 3 ^ 40 * 2940376 * 2
def baseEnd_2940376 : Nat := 1509826192944692999077463

theorem tailTrace_2940376 : CollatzResearch.WordTrace tailWord_2940376 prefixEnd_2940376 1509826192944692999077463 := by
  unfold tailWord_2940376
  simp only [CollatzResearch.WordTrace]
  refine ⟨53622161597763701542808491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71496215463684935390411321 53622161597763701542808491)
  ·
    refine ⟨80433242396645552314212737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53622161597763701542808491 80433242396645552314212737)
    ·
      refine ⟨60324931797484164235659553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80433242396645552314212737 60324931797484164235659553)
      ·
        refine ⟨45243698848113123176744665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60324931797484164235659553 45243698848113123176744665)
        ·
          refine ⟨33932774136084842382558499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45243698848113123176744665 33932774136084842382558499)
          ·
            refine ⟨50899161204127263573837749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33932774136084842382558499 50899161204127263573837749)
            ·
              refine ⟨4771796362886930960047289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50899161204127263573837749 4771796362886930960047289)
              ·
                refine ⟨3578847272165198220035467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771796362886930960047289 3578847272165198220035467)
                ·
                  refine ⟨5368270908247797330053201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578847272165198220035467 5368270908247797330053201)
                  ·
                    refine ⟨4026203181185847997539901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5368270908247797330053201 4026203181185847997539901)
                    ·
                      refine ⟨1509826192944692999077463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026203181185847997539901 1509826192944692999077463)
                      ·
                        rfl

theorem cell23_2940376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_2940376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940376 prefixEnd_2940376 := by exact prefixLift 2940376
  have htrace : WordTrace (prefixWord ++ tailWord_2940376) baseStart_2940376 baseEnd_2940376 := by
    simpa [prefixWord, tailWord_2940376, baseEnd_2940376] using wordTrace_append hprefix tailTrace_2940376
  have hstable : (prefixWord ++ tailWord_2940376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940376).length < 2 ^ (prefixWord ++ tailWord_2940376).sum := by decide
  have hdescent : baseEnd_2940376 < baseStart_2940376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940423 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2940423 : Nat := 118140960795 + 2940423 * 2 ^ 59
def prefixEnd_2940423 : Nat := 4983230072969 + 3 ^ 40 * 2940423 * 2
def baseEnd_2940423 : Nat := 1509850326535454315189747

theorem tailTrace_2940423 : CollatzResearch.WordTrace tailWord_2940423 prefixEnd_2940423 1509850326535454315189747 := by
  unfold tailWord_2940423
  simp only [CollatzResearch.WordTrace]
  refine ⟨107246037426357130112577923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71497358284238086741718615 107246037426357130112577923)
  ·
    refine ⟨160869056139535695168866885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107246037426357130112577923 160869056139535695168866885)
    ·
      refine ⟨30162948026162942844162541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160869056139535695168866885 30162948026162942844162541)
      ·
        refine ⟨11311105509811103566560953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30162948026162942844162541 11311105509811103566560953)
        ·
          refine ⟨8483329132358327674920715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11311105509811103566560953 8483329132358327674920715)
          ·
            refine ⟨12724993698537491512381073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483329132358327674920715 12724993698537491512381073)
            ·
              refine ⟨9543745273903118634285805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12724993698537491512381073 9543745273903118634285805)
              ·
                refine ⟨3578904477713669487857177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9543745273903118634285805 3578904477713669487857177)
                ·
                  refine ⟨2684178358285252115892883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578904477713669487857177 2684178358285252115892883)
                  ·
                    refine ⟨4026267537427878173839325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684178358285252115892883 4026267537427878173839325)
                    ·
                      refine ⟨1509850326535454315189747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026267537427878173839325 1509850326535454315189747)
                      ·
                        rfl

theorem cell23_2940423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2940423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940423 prefixEnd_2940423 := by exact prefixLift 2940423
  have htrace : WordTrace (prefixWord ++ tailWord_2940423) baseStart_2940423 baseEnd_2940423 := by
    simpa [prefixWord, tailWord_2940423, baseEnd_2940423] using wordTrace_append hprefix tailTrace_2940423
  have hstable : (prefixWord ++ tailWord_2940423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940423).length < 2 ^ (prefixWord ++ tailWord_2940423).sum := by decide
  have hdescent : baseEnd_2940423 < baseStart_2940423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940450 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_2940450 : Nat := 118140960795 + 2940450 * 2 ^ 59
def prefixEnd_2940450 : Nat := 4983230072969 + 3 ^ 40 * 2940450 * 2
def baseEnd_2940450 : Nat := 1509864190513125709552123

theorem tailTrace_2940450 : CollatzResearch.WordTrace tailWord_2940450 prefixEnd_2940450 1509864190513125709552123 := by
  unfold tailWord_2940450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26811755549314828430952701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71498014798172875815873869 26811755549314828430952701)
  ·
    refine ⟨10054408330993060661607263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26811755549314828430952701 10054408330993060661607263)
    ·
      refine ⟨15081612496489590992410895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054408330993060661607263 15081612496489590992410895)
      ·
        refine ⟨22622418744734386488616343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15081612496489590992410895 22622418744734386488616343)
        ·
          refine ⟨33933628117101579732924515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22622418744734386488616343 33933628117101579732924515)
          ·
            refine ⟨50900442175652369599386773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33933628117101579732924515 50900442175652369599386773)
            ·
              refine ⟨2385958226983704824971255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50900442175652369599386773 2385958226983704824971255)
              ·
                refine ⟨3578937340475557237456883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385958226983704824971255 3578937340475557237456883)
                ·
                  refine ⟨5368406010713335856185325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578937340475557237456883 5368406010713335856185325)
                  ·
                    refine ⟨2013152254017500946069497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5368406010713335856185325 2013152254017500946069497)
                    ·
                      refine ⟨1509864190513125709552123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013152254017500946069497 1509864190513125709552123)
                      ·
                        rfl

theorem cell23_2940450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_2940450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940450 prefixEnd_2940450 := by exact prefixLift 2940450
  have htrace : WordTrace (prefixWord ++ tailWord_2940450) baseStart_2940450 baseEnd_2940450 := by
    simpa [prefixWord, tailWord_2940450, baseEnd_2940450] using wordTrace_append hprefix tailTrace_2940450
  have hstable : (prefixWord ++ tailWord_2940450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940450).length < 2 ^ (prefixWord ++ tailWord_2940450).sum := by decide
  have hdescent : baseEnd_2940450 < baseStart_2940450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940469 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 7]
def baseStart_2940469 : Nat := 118140960795 + 2940469 * 2 ^ 59
def prefixEnd_2940469 : Nat := 4983230072969 + 3 ^ 40 * 2940469 * 2
def baseEnd_2940469 : Nat := 167763771849506792801615

theorem tailTrace_2940469 : CollatzResearch.WordTrace tailWord_2940469 prefixEnd_2940469 167763771849506792801615 := by
  unfold tailWord_2940469
  simp only [CollatzResearch.WordTrace]
  refine ⟨107247715184190479968752461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71498476789460319979168307 107247715184190479968752461)
  ·
    refine ⟨40217893194071429988282173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107247715184190479968752461 40217893194071429988282173)
    ·
      refine ⟨15081709947776786245605815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40217893194071429988282173 15081709947776786245605815)
      ·
        refine ⟨22622564921665179368408723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15081709947776786245605815 22622564921665179368408723)
        ·
          refine ⟨33933847382497769052613085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22622564921665179368408723 33933847382497769052613085)
          ·
            refine ⟨12725192768436663394729907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33933847382497769052613085 12725192768436663394729907)
            ·
              refine ⟨19087789152654995092094861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12725192768436663394729907 19087789152654995092094861)
              ·
                refine ⟨7157920932245623159535573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19087789152654995092094861 7157920932245623159535573)
                ·
                  refine ⟨167763771849506792801615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7157920932245623159535573 167763771849506792801615)
                  ·
                    rfl

theorem cell23_2940469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_2940469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940469 prefixEnd_2940469 := by exact prefixLift 2940469
  have htrace : WordTrace (prefixWord ++ tailWord_2940469) baseStart_2940469 baseEnd_2940469 := by
    simpa [prefixWord, tailWord_2940469, baseEnd_2940469] using wordTrace_append hprefix tailTrace_2940469
  have hstable : (prefixWord ++ tailWord_2940469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940469).length < 2 ^ (prefixWord ++ tailWord_2940469).sum := by decide
  have hdescent : baseEnd_2940469 < baseStart_2940469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940503 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 5]
def baseStart_2940503 : Nat := 118140960795 + 2940503 * 2 ^ 59
def prefixEnd_2940503 : Nat := 4983230072969 + 3 ^ 40 * 2940503 * 2
def baseEnd_2940503 : Nat := 167765711665312666909931

theorem tailTrace_2940503 : CollatzResearch.WordTrace tailWord_2940503 prefixEnd_2940503 167765711665312666909931 := by
  unfold tailWord_2940503
  simp only [CollatzResearch.WordTrace]
  refine ⟨107248955266067303775490163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71499303510711535850326775 107248955266067303775490163)
  ·
    refine ⟨160873432899100955663235245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107248955266067303775490163 160873432899100955663235245)
    ·
      refine ⟨60327537337162858373713217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160873432899100955663235245 60327537337162858373713217)
      ·
        refine ⟨45245653002872143780284913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60327537337162858373713217 45245653002872143780284913)
        ·
          refine ⟨33934239752154107835213685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45245653002872143780284913 33934239752154107835213685)
          ·
            refine ⟨3181334976764447609551283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33934239752154107835213685 3181334976764447609551283)
            ·
              refine ⟨4772002465146671414326925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181334976764447609551283 4772002465146671414326925)
              ·
                refine ⟨1789500924430001780372597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4772002465146671414326925 1789500924430001780372597)
                ·
                  refine ⟨167765711665312666909931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789500924430001780372597 167765711665312666909931)
                  ·
                    rfl

theorem cell23_2940503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 5].length) (baseStart_2940503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940503 prefixEnd_2940503 := by exact prefixLift 2940503
  have htrace : WordTrace (prefixWord ++ tailWord_2940503) baseStart_2940503 baseEnd_2940503 := by
    simpa [prefixWord, tailWord_2940503, baseEnd_2940503] using wordTrace_append hprefix tailTrace_2940503
  have hstable : (prefixWord ++ tailWord_2940503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940503).length < 2 ^ (prefixWord ++ tailWord_2940503).sum := by decide
  have hdescent : baseEnd_2940503 < baseStart_2940503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940516 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_2940516 : Nat := 118140960795 + 2940516 * 2 ^ 59
def prefixEnd_2940516 : Nat := 4983230072969 + 3 ^ 40 * 2940516 * 2
def baseEnd_2940516 : Nat := 503299360078774150442273

theorem tailTrace_2940516 : CollatzResearch.WordTrace tailWord_2940516 prefixEnd_2940516 503299360078774150442273 := by
  unfold tailWord_2940516
  simp only [CollatzResearch.WordTrace]
  refine ⟨53624714707510103497856701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71499619610013471330475601 53624714707510103497856701)
  ·
    refine ⟨20109268015316288811696263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53624714707510103497856701 20109268015316288811696263)
    ·
      refine ⟨30163902022974433217544395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20109268015316288811696263 30163902022974433217544395)
      ·
        refine ⟨45245853034461649826316593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30163902022974433217544395 45245853034461649826316593)
        ·
          refine ⟨33934389775846237369737445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45245853034461649826316593 33934389775846237369737445)
          ·
            refine ⟨6362698082971169506825771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33934389775846237369737445 6362698082971169506825771)
            ·
              refine ⟨9544047124456754260238657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362698082971169506825771 9544047124456754260238657)
              ·
                refine ⟨7158035343342565695178993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9544047124456754260238657 7158035343342565695178993)
                ·
                  refine ⟨5368526507506924271384245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7158035343342565695178993 5368526507506924271384245)
                  ·
                    refine ⟨503299360078774150442273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5368526507506924271384245 503299360078774150442273)
                    ·
                      rfl

theorem cell23_2940516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_2940516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940516 prefixEnd_2940516 := by exact prefixLift 2940516
  have htrace : WordTrace (prefixWord ++ tailWord_2940516) baseStart_2940516 baseEnd_2940516 := by
    simpa [prefixWord, tailWord_2940516, baseEnd_2940516] using wordTrace_append hprefix tailTrace_2940516
  have hstable : (prefixWord ++ tailWord_2940516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940516).length < 2 ^ (prefixWord ++ tailWord_2940516).sum := by decide
  have hdescent : baseEnd_2940516 < baseStart_2940516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940520 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 5]
def baseStart_2940520 : Nat := 118140960795 + 2940520 * 2 ^ 59
def prefixEnd_2940520 : Nat := 4983230072969 + 3 ^ 40 * 2940520 * 2
def baseEnd_2940520 : Nat := 167766681573215603964089

theorem tailTrace_2940520 : CollatzResearch.WordTrace tailWord_2940520 prefixEnd_2940520 167766681573215603964089 := by
  unfold tailWord_2940520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53624787653502857839429507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71499716871337143785906009 53624787653502857839429507)
  ·
    refine ⟨80437181480254286759144261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53624787653502857839429507 80437181480254286759144261)
    ·
      refine ⟨15081971527547678767339549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80437181480254286759144261 15081971527547678767339549)
      ·
        refine ⟨5655739322830379537752331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15081971527547678767339549 5655739322830379537752331)
        ·
          refine ⟨8483608984245569306628497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655739322830379537752331 8483608984245569306628497)
          ·
            refine ⟨6362706738184176979971373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8483608984245569306628497 6362706738184176979971373)
            ·
              refine ⟨2386015026819066367489265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6362706738184176979971373 2386015026819066367489265)
              ·
                refine ⟨1789511270114299775616949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386015026819066367489265 1789511270114299775616949)
                ·
                  refine ⟨167766681573215603964089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789511270114299775616949 167766681573215603964089)
                  ·
                    rfl

theorem cell23_2940520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 5].length) (baseStart_2940520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940520 prefixEnd_2940520 := by exact prefixLift 2940520
  have htrace : WordTrace (prefixWord ++ tailWord_2940520) baseStart_2940520 baseEnd_2940520 := by
    simpa [prefixWord, tailWord_2940520, baseEnd_2940520] using wordTrace_append hprefix tailTrace_2940520
  have hstable : (prefixWord ++ tailWord_2940520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940520).length < 2 ^ (prefixWord ++ tailWord_2940520).sum := by decide
  have hdescent : baseEnd_2940520 < baseStart_2940520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940576 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 6]
def baseStart_2940576 : Nat := 118140960795 + 2940576 * 2 ^ 59
def prefixEnd_2940576 : Nat := 4983230072969 + 3 ^ 40 * 2940576 * 2
def baseEnd_2940576 : Nat := 167769876563954690730727

theorem tailTrace_2940576 : CollatzResearch.WordTrace tailWord_2940576 prefixEnd_2940576 167769876563954690730727 := by
  unfold tailWord_2940576
  simp only [CollatzResearch.WordTrace]
  refine ⟨53625808897401418621448791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71501078529868558161931721 53625808897401418621448791)
  ·
    refine ⟨80438713346102127932173187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53625808897401418621448791 80438713346102127932173187)
    ·
      refine ⟨120658070019153191898259781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80438713346102127932173187 120658070019153191898259781)
      ·
        refine ⟨22623388128591223480923709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120658070019153191898259781 22623388128591223480923709)
        ·
          refine ⟨8483770548221708805346391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22623388128591223480923709 8483770548221708805346391)
          ·
            refine ⟨12725655822332563208019587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483770548221708805346391 12725655822332563208019587)
            ·
              refine ⟨19088483733498844812029381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12725655822332563208019587 19088483733498844812029381)
              ·
                refine ⟨3579090700031033402255509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19088483733498844812029381 3579090700031033402255509)
                ·
                  refine ⟨167769876563954690730727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3579090700031033402255509 167769876563954690730727)
                  ·
                    rfl

theorem cell23_2940576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_2940576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940576 prefixEnd_2940576 := by exact prefixLift 2940576
  have htrace : WordTrace (prefixWord ++ tailWord_2940576) baseStart_2940576 baseEnd_2940576 := by
    simpa [prefixWord, tailWord_2940576, baseEnd_2940576] using wordTrace_append hprefix tailTrace_2940576
  have hstable : (prefixWord ++ tailWord_2940576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940576).length < 2 ^ (prefixWord ++ tailWord_2940576).sum := by decide
  have hdescent : baseEnd_2940576 < baseStart_2940576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940579 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2940579 : Nat := 118140960795 + 2940579 * 2 ^ 59
def prefixEnd_2940579 : Nat := 4983230072969 + 3 ^ 40 * 2940579 * 2
def baseEnd_2940579 : Nat := 1509930429517555704839029

theorem tailTrace_2940579 : CollatzResearch.WordTrace tailWord_2940579 prefixEnd_2940579 1509930429517555704839029 := by
  unfold tailWord_2940579
  simp only [CollatzResearch.WordTrace]
  refine ⟨107251727213791968755256791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71501151475861312503504527 107251727213791968755256791)
  ·
    refine ⟨160877590820687953132885187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107251727213791968755256791 160877590820687953132885187)
    ·
      refine ⟨241316386231031929699327781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160877590820687953132885187 241316386231031929699327781)
      ·
        refine ⟨45246822418318486818623959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241316386231031929699327781 45246822418318486818623959)
        ·
          refine ⟨67870233627477730227935939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45246822418318486818623959 67870233627477730227935939)
          ·
            refine ⟨101805350441216595341903909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67870233627477730227935939 101805350441216595341903909)
            ·
              refine ⟨19088503207728111626606983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101805350441216595341903909 19088503207728111626606983)
              ·
                refine ⟨28632754811592167439910475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19088503207728111626606983 28632754811592167439910475)
                ·
                  refine ⟨42949132217388251159865713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28632754811592167439910475 42949132217388251159865713)
                  ·
                    refine ⟨32211849163041188369899285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42949132217388251159865713 32211849163041188369899285)
                    ·
                      refine ⟨1509930429517555704839029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32211849163041188369899285 1509930429517555704839029)
                      ·
                        rfl

theorem cell23_2940579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2940579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940579 prefixEnd_2940579 := by exact prefixLift 2940579
  have htrace : WordTrace (prefixWord ++ tailWord_2940579) baseStart_2940579 baseEnd_2940579 := by
    simpa [prefixWord, tailWord_2940579, baseEnd_2940579] using wordTrace_append hprefix tailTrace_2940579
  have hstable : (prefixWord ++ tailWord_2940579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940579).length < 2 ^ (prefixWord ++ tailWord_2940579).sum := by decide
  have hdescent : baseEnd_2940579 < baseStart_2940579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940580 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_2940580 : Nat := 118140960795 + 2940580 * 2 ^ 59
def prefixEnd_2940580 : Nat := 4983230072969 + 3 ^ 40 * 2940580 * 2
def baseEnd_2940580 : Nat := 503310314332736733642175

theorem tailTrace_2940580 : CollatzResearch.WordTrace tailWord_2940580 prefixEnd_2940580 503310314332736733642175 := by
  unfold tailWord_2940580
  simp only [CollatzResearch.WordTrace]
  refine ⟨53625881843394172963021597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71501175791192230617362129 53625881843394172963021597)
  ·
    refine ⟨20109705691272814861133099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53625881843394172963021597 20109705691272814861133099)
    ·
      refine ⟨30164558536909222291699649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20109705691272814861133099 30164558536909222291699649)
      ·
        refine ⟨22623418902681916718774737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30164558536909222291699649 22623418902681916718774737)
        ·
          refine ⟨16967564177011437539081053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22623418902681916718774737 16967564177011437539081053)
          ·
            refine ⟨6362836566379289077155395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16967564177011437539081053 6362836566379289077155395)
            ·
              refine ⟨9544254849568933615733093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362836566379289077155395 9544254849568933615733093)
              ·
                refine ⟨1789547784294175052949955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9544254849568933615733093 1789547784294175052949955)
                ·
                  refine ⟨2684321676441262579424933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789547784294175052949955 2684321676441262579424933)
                  ·
                    refine ⟨503310314332736733642175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684321676441262579424933 503310314332736733642175)
                    ·
                      rfl

theorem cell23_2940580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_2940580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940580 prefixEnd_2940580 := by exact prefixLift 2940580
  have htrace : WordTrace (prefixWord ++ tailWord_2940580) baseStart_2940580 baseEnd_2940580 := by
    simpa [prefixWord, tailWord_2940580, baseEnd_2940580] using wordTrace_append hprefix tailTrace_2940580
  have hstable : (prefixWord ++ tailWord_2940580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940580).length < 2 ^ (prefixWord ++ tailWord_2940580).sum := by decide
  have hdescent : baseEnd_2940580 < baseStart_2940580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940614 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2940614 : Nat := 118140960795 + 2940614 * 2 ^ 59
def prefixEnd_2940614 : Nat := 4983230072969 + 3 ^ 40 * 2940614 * 2
def baseEnd_2940614 : Nat := 503316133780154355967123

theorem tailTrace_2940614 : CollatzResearch.WordTrace tailWord_2940614 prefixEnd_2940614 503316133780154355967123 := by
  unfold tailWord_2940614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351656367770786554149403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71502002512443446488520597 3351656367770786554149403)
  ·
    refine ⟨5027484551656179831224105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351656367770786554149403 5027484551656179831224105)
    ·
      refine ⟨3770613413742134873418079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027484551656179831224105 3770613413742134873418079)
      ·
        refine ⟨5655920120613202310127119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770613413742134873418079 5655920120613202310127119)
        ·
          refine ⟨8483880180919803465190679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655920120613202310127119 8483880180919803465190679)
          ·
            refine ⟨12725820271379705197786019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483880180919803465190679 12725820271379705197786019)
            ·
              refine ⟨19088730407069557796679029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12725820271379705197786019 19088730407069557796679029)
              ·
                refine ⟨1789568475662771043438659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19088730407069557796679029 1789568475662771043438659)
                ·
                  refine ⟨2684352713494156565157989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789568475662771043438659 2684352713494156565157989)
                  ·
                    refine ⟨503316133780154355967123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684352713494156565157989 503316133780154355967123)
                    ·
                      rfl

theorem cell23_2940614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2940614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940614 prefixEnd_2940614 := by exact prefixLift 2940614
  have htrace : WordTrace (prefixWord ++ tailWord_2940614) baseStart_2940614 baseEnd_2940614 := by
    simpa [prefixWord, tailWord_2940614, baseEnd_2940614] using wordTrace_append hprefix tailTrace_2940614
  have hstable : (prefixWord ++ tailWord_2940614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940614).length < 2 ^ (prefixWord ++ tailWord_2940614).sum := by decide
  have hdescent : baseEnd_2940614 < baseStart_2940614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940649 : List Nat := [1, 2, 1, 1, 1, 2, 3, 12]
def baseStart_2940649 : Nat := 118140960795 + 2940649 * 2 ^ 59
def prefixEnd_2940649 : Nat := 4983230072969 + 3 ^ 40 * 2940649 * 2
def baseEnd_2940649 : Nat := 55924680487532238183841

theorem tailTrace_2940649 : CollatzResearch.WordTrace tailWord_2940649 prefixEnd_2940649 55924680487532238183841 := by
  unfold tailWord_2940649
  simp only [CollatzResearch.WordTrace]
  refine ⟨107254280323538370710305001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71502853549025580473536667 107254280323538370710305001)
  ·
    refine ⟨80440710242653778032728751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107254280323538370710305001 80440710242653778032728751)
    ·
      refine ⟨120661065363980667049093127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80440710242653778032728751 120661065363980667049093127)
      ·
        refine ⟨180991598045971000573639691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120661065363980667049093127 180991598045971000573639691)
        ·
          refine ⟨271487397068956500860459537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180991598045971000573639691 271487397068956500860459537)
          ·
            refine ⟨203615547801717375645344653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271487397068956500860459537 203615547801717375645344653)
            ·
              refine ⟨76355830425644015867004245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203615547801717375645344653 76355830425644015867004245)
              ·
                refine ⟨55924680487532238183841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 76355830425644015867004245 55924680487532238183841)
                ·
                  rfl

theorem cell23_2940649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 12].length) (baseStart_2940649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940649 prefixEnd_2940649 := by exact prefixLift 2940649
  have htrace : WordTrace (prefixWord ++ tailWord_2940649) baseStart_2940649 baseEnd_2940649 := by
    simpa [prefixWord, tailWord_2940649, baseEnd_2940649] using wordTrace_append hprefix tailTrace_2940649
  have hstable : (prefixWord ++ tailWord_2940649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940649).length < 2 ^ (prefixWord ++ tailWord_2940649).sum := by decide
  have hdescent : baseEnd_2940649 < baseStart_2940649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940653 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2940653 : Nat := 118140960795 + 2940653 * 2 ^ 59
def prefixEnd_2940653 : Nat := 4983230072969 + 3 ^ 40 * 2940653 * 2
def baseEnd_2940653 : Nat := 503322809028662805104563

theorem tailTrace_2940653 : CollatzResearch.WordTrace tailWord_2940653 prefixEnd_2940653 503322809028662805104563 := by
  unfold tailWord_2940653
  simp only [CollatzResearch.WordTrace]
  refine ⟨107254426215523879393450613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71502950810349252928967075 107254426215523879393450613)
  ·
    refine ⟨10055102457705363693135995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107254426215523879393450613 10055102457705363693135995)
    ·
      refine ⟨15082653686558045539703993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10055102457705363693135995 15082653686558045539703993)
      ·
        refine ⟨11311990264918534154777995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15082653686558045539703993 11311990264918534154777995)
        ·
          refine ⟨16967985397377801232166993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11311990264918534154777995 16967985397377801232166993)
          ·
            refine ⟨12725989048033350924125245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16967985397377801232166993 12725989048033350924125245)
            ·
              refine ⟨4772245893012506596546967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12725989048033350924125245 4772245893012506596546967)
              ·
                refine ⟨7158368839518759894820451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772245893012506596546967 7158368839518759894820451)
                ·
                  refine ⟨10737553259278139842230677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7158368839518759894820451 10737553259278139842230677)
                  ·
                    refine ⟨503322809028662805104563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10737553259278139842230677 503322809028662805104563)
                    ·
                      rfl

theorem cell23_2940653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2940653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940653 prefixEnd_2940653 := by exact prefixLift 2940653
  have htrace : WordTrace (prefixWord ++ tailWord_2940653) baseStart_2940653 baseEnd_2940653 := by
    simpa [prefixWord, tailWord_2940653, baseEnd_2940653] using wordTrace_append hprefix tailTrace_2940653
  have hstable : (prefixWord ++ tailWord_2940653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940653).length < 2 ^ (prefixWord ++ tailWord_2940653).sum := by decide
  have hdescent : baseEnd_2940653 < baseStart_2940653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940656 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_2940656 : Nat := 118140960795 + 2940656 * 2 ^ 59
def prefixEnd_2940656 : Nat := 4983230072969 + 3 ^ 40 * 2940656 * 2
def baseEnd_2940656 : Nat := 1509969967527951903576175

theorem tailTrace_2940656 : CollatzResearch.WordTrace tailWord_2940656 prefixEnd_2940656 1509969967527951903576175 := by
  unfold tailWord_2940656
  simp only [CollatzResearch.WordTrace]
  refine ⟨53627267817256505452904911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71503023756342007270539881 53627267817256505452904911)
  ·
    refine ⟨80440901725884758179357367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53627267817256505452904911 80440901725884758179357367)
    ·
      refine ⟨120661352588827137269036051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80440901725884758179357367 120661352588827137269036051)
      ·
        refine ⟨180992028883240705903554077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120661352588827137269036051 180992028883240705903554077)
        ·
          refine ⟨67872010831215264713832779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180992028883240705903554077 67872010831215264713832779)
          ·
            refine ⟨101808016246822897070749169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67872010831215264713832779 101808016246822897070749169)
            ·
              refine ⟨76356012185117172803061877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101808016246822897070749169 76356012185117172803061877)
              ·
                refine ⟨7158376142354734950287051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76356012185117172803061877 7158376142354734950287051)
                ·
                  refine ⟨10737564213532102425430577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7158376142354734950287051 10737564213532102425430577)
                  ·
                    refine ⟨8053173160149076819072933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10737564213532102425430577 8053173160149076819072933)
                    ·
                      refine ⟨1509969967527951903576175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8053173160149076819072933 1509969967527951903576175)
                      ·
                        rfl

theorem cell23_2940656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_2940656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940656 prefixEnd_2940656 := by exact prefixLift 2940656
  have htrace : WordTrace (prefixWord ++ tailWord_2940656) baseStart_2940656 baseEnd_2940656 := by
    simpa [prefixWord, tailWord_2940656, baseEnd_2940656] using wordTrace_append hprefix tailTrace_2940656
  have hstable : (prefixWord ++ tailWord_2940656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940656).length < 2 ^ (prefixWord ++ tailWord_2940656).sum := by decide
  have hdescent : baseEnd_2940656 < baseStart_2940656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940663 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_2940663 : Nat := 118140960795 + 2940663 * 2 ^ 59
def prefixEnd_2940663 : Nat := 4983230072969 + 3 ^ 40 * 2940663 * 2
def baseEnd_2940663 : Nat := 1509973561892533376188643

theorem tailTrace_2940663 : CollatzResearch.WordTrace tailWord_2940663 prefixEnd_2940663 1509973561892533376188643 := by
  unfold tailWord_2940663
  simp only [CollatzResearch.WordTrace]
  refine ⟨107254790945487651101314643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71503193963658434067543095 107254790945487651101314643)
  ·
    refine ⟨160882186418231476651971965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107254790945487651101314643 160882186418231476651971965)
    ·
      refine ⟨60330819906836803744489487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160882186418231476651971965 60330819906836803744489487)
      ·
        refine ⟨90496229860255205616734231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60330819906836803744489487 90496229860255205616734231)
        ·
          refine ⟨135744344790382808425101347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90496229860255205616734231 135744344790382808425101347)
          ·
            refine ⟨203616517185574212637652021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135744344790382808425101347 203616517185574212637652021)
            ·
              refine ⟨19089048486147582434779877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203616517185574212637652021 19089048486147582434779877)
              ·
                refine ⟨3579196591152671706521227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19089048486147582434779877 3579196591152671706521227)
                ·
                  refine ⟨5368794886729007559781841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579196591152671706521227 5368794886729007559781841)
                  ·
                    refine ⟨4026596165046755669836381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5368794886729007559781841 4026596165046755669836381)
                    ·
                      refine ⟨1509973561892533376188643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026596165046755669836381 1509973561892533376188643)
                      ·
                        rfl

theorem cell23_2940663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_2940663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940663 prefixEnd_2940663 := by exact prefixLift 2940663
  have htrace : WordTrace (prefixWord ++ tailWord_2940663) baseStart_2940663 baseEnd_2940663 := by
    simpa [prefixWord, tailWord_2940663, baseEnd_2940663] using wordTrace_append hprefix tailTrace_2940663
  have hstable : (prefixWord ++ tailWord_2940663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940663).length < 2 ^ (prefixWord ++ tailWord_2940663).sum := by decide
  have hdescent : baseEnd_2940663 < baseStart_2940663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940753 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_2940753 : Nat := 118140960795 + 2940753 * 2 ^ 59
def prefixEnd_2940753 : Nat := 4983230072969 + 3 ^ 40 * 2940753 * 2
def baseEnd_2940753 : Nat := 1510019775151438024063229

theorem tailTrace_2940753 : CollatzResearch.WordTrace tailWord_2940753 prefixEnd_2940753 1510019775151438024063229 := by
  unfold tailWord_2940753
  simp only [CollatzResearch.WordTrace]
  refine ⟨107258073515161596472090913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71505382343441064314727275 107258073515161596472090913)
  ·
    refine ⟨80443555136371197354068185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107258073515161596472090913 80443555136371197354068185)
    ·
      refine ⟨60332666352278398015551139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80443555136371197354068185 60332666352278398015551139)
      ·
        refine ⟨90498999528417597023326709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60332666352278398015551139 90498999528417597023326709)
        ·
          refine ⟨8484281205789149720936879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90498999528417597023326709 8484281205789149720936879)
          ·
            refine ⟨12726421808683724581405319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8484281205789149720936879 12726421808683724581405319)
            ·
              refine ⟨19089632713025586872107979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12726421808683724581405319 19089632713025586872107979)
              ·
                refine ⟨28634449069538380308161969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19089632713025586872107979 28634449069538380308161969)
                ·
                  refine ⟨21475836802153785231121477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28634449069538380308161969 21475836802153785231121477)
                  ·
                    refine ⟨4026719400403834730835277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21475836802153785231121477 4026719400403834730835277)
                    ·
                      refine ⟨1510019775151438024063229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026719400403834730835277 1510019775151438024063229)
                      ·
                        rfl

theorem cell23_2940753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_2940753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940753 prefixEnd_2940753 := by exact prefixLift 2940753
  have htrace : WordTrace (prefixWord ++ tailWord_2940753) baseStart_2940753 baseEnd_2940753 := by
    simpa [prefixWord, tailWord_2940753, baseEnd_2940753] using wordTrace_append hprefix tailTrace_2940753
  have hstable : (prefixWord ++ tailWord_2940753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940753).length < 2 ^ (prefixWord ++ tailWord_2940753).sum := by decide
  have hdescent : baseEnd_2940753 < baseStart_2940753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940767 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 2, 2, 2]
def baseStart_2940767 : Nat := 118140960795 + 2940767 * 2 ^ 59
def prefixEnd_2940767 : Nat := 4983230072969 + 3 ^ 40 * 2940767 * 2
def baseEnd_2940767 : Nat := 1510026963880600969288165

theorem tailTrace_2940767 : CollatzResearch.WordTrace tailWord_2940767 prefixEnd_2940767 1510026963880600969288165 := by
  unfold tailWord_2940767
  simp only [CollatzResearch.WordTrace]
  refine ⟨107258584137110876863100555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71505722758073917908733703 107258584137110876863100555)
  ·
    refine ⟨160887876205666315294650833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107258584137110876863100555 160887876205666315294650833)
    ·
      refine ⟨120665907154249736470988125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160887876205666315294650833 120665907154249736470988125)
      ·
        refine ⟨45249715182843651176620547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120665907154249736470988125 45249715182843651176620547)
        ·
          refine ⟨67874572774265476764930821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45249715182843651176620547 67874572774265476764930821)
          ·
            refine ⟨12726482395174776893424529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67874572774265476764930821 12726482395174776893424529)
            ·
              refine ⟨9544861796381082670068397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12726482395174776893424529 9544861796381082670068397)
              ·
                refine ⟨3579323173642906001275649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9544861796381082670068397 3579323173642906001275649)
                ·
                  refine ⟨2684492380232179500956737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3579323173642906001275649 2684492380232179500956737)
                  ·
                    refine ⟨2013369285174134625717553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2684492380232179500956737 2013369285174134625717553)
                    ·
                      refine ⟨1510026963880600969288165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013369285174134625717553 1510026963880600969288165)
                      ·
                        rfl

theorem cell23_2940767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_2940767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940767 prefixEnd_2940767 := by exact prefixLift 2940767
  have htrace : WordTrace (prefixWord ++ tailWord_2940767) baseStart_2940767 baseEnd_2940767 := by
    simpa [prefixWord, tailWord_2940767, baseEnd_2940767] using wordTrace_append hprefix tailTrace_2940767
  have hstable : (prefixWord ++ tailWord_2940767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940767).length < 2 ^ (prefixWord ++ tailWord_2940767).sum := by decide
  have hdescent : baseEnd_2940767 < baseStart_2940767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940816 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_2940816 : Nat := 118140960795 + 2940816 * 2 ^ 59
def prefixEnd_2940816 : Nat := 4983230072969 + 3 ^ 40 * 2940816 * 2
def baseEnd_2940816 : Nat := 503350708144223759191813

theorem tailTrace_2940816 : CollatzResearch.WordTrace tailWord_2940816 prefixEnd_2940816 503350708144223759191813 := by
  unfold tailWord_2940816
  simp only [CollatzResearch.WordTrace]
  refine ⟨53630185656966679115817151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71506914209288905487756201 53630185656966679115817151)
  ·
    refine ⟨80445278485450018673725727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53630185656966679115817151 80445278485450018673725727)
    ·
      refine ⟨120667917728175028010588591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80445278485450018673725727 120667917728175028010588591)
      ·
        refine ⟨181001876592262542015882887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120667917728175028010588591 181001876592262542015882887)
        ·
          refine ⟨271502814888393813023824331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181001876592262542015882887 271502814888393813023824331)
          ·
            refine ⟨407254222332590719535736497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271502814888393813023824331 407254222332590719535736497)
            ·
              refine ⟨305440666749443039651802373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407254222332590719535736497 305440666749443039651802373)
              ·
                refine ⟨57270125015520569934712945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305440666749443039651802373 57270125015520569934712945)
                ·
                  refine ⟨42952593761640427451034709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57270125015520569934712945 42952593761640427451034709)
                  ·
                    refine ⟨503350708144223759191813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42952593761640427451034709 503350708144223759191813)
                    ·
                      rfl

theorem cell23_2940816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_2940816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940816 prefixEnd_2940816 := by exact prefixLift 2940816
  have htrace : WordTrace (prefixWord ++ tailWord_2940816) baseStart_2940816 baseEnd_2940816 := by
    simpa [prefixWord, tailWord_2940816, baseEnd_2940816] using wordTrace_append hprefix tailTrace_2940816
  have hstable : (prefixWord ++ tailWord_2940816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940816).length < 2 ^ (prefixWord ++ tailWord_2940816).sum := by decide
  have hdescent : baseEnd_2940816 < baseStart_2940816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940823 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2940823 : Nat := 118140960795 + 2940823 * 2 ^ 59
def prefixEnd_2940823 : Nat := 4983230072969 + 3 ^ 40 * 2940823 * 2
def baseEnd_2940823 : Nat := 1510055718797252750187907

theorem tailTrace_2940823 : CollatzResearch.WordTrace tailWord_2940823 prefixEnd_2940823 1510055718797252750187907 := by
  unfold tailWord_2940823
  simp only [CollatzResearch.WordTrace]
  refine ⟨107260626624907998427139123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71507084416605332284759415 107260626624907998427139123)
  ·
    refine ⟨160890939937361997640708685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107260626624907998427139123 160890939937361997640708685)
    ·
      refine ⟨60334102476510749115265757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160890939937361997640708685 60334102476510749115265757)
      ·
        refine ⟨22625288428691530918224659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60334102476510749115265757 22625288428691530918224659)
        ·
          refine ⟨33937932643037296377336989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22625288428691530918224659 33937932643037296377336989)
          ·
            refine ⟨12726724741138986141501371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33937932643037296377336989 12726724741138986141501371)
            ·
              refine ⟨19090087111708479212252057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12726724741138986141501371 19090087111708479212252057)
              ·
                refine ⟨14317565333781359409189043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19090087111708479212252057 14317565333781359409189043)
                ·
                  refine ⟨21476348000672039113783565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14317565333781359409189043 21476348000672039113783565)
                  ·
                    refine ⟨8053630500252014667668837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21476348000672039113783565 8053630500252014667668837)
                    ·
                      refine ⟨1510055718797252750187907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8053630500252014667668837 1510055718797252750187907)
                      ·
                        rfl

theorem cell23_2940823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2940823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940823 prefixEnd_2940823 := by exact prefixLift 2940823
  have htrace : WordTrace (prefixWord ++ tailWord_2940823) baseStart_2940823 baseEnd_2940823 := by
    simpa [prefixWord, tailWord_2940823, baseEnd_2940823] using wordTrace_append hprefix tailTrace_2940823
  have hstable : (prefixWord ++ tailWord_2940823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940823).length < 2 ^ (prefixWord ++ tailWord_2940823).sum := by decide
  have hdescent : baseEnd_2940823 < baseStart_2940823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940863 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 6]
def baseStart_2940863 : Nat := 118140960795 + 2940863 * 2 ^ 59
def prefixEnd_2940863 : Nat := 4983230072969 + 3 ^ 40 * 2940863 * 2
def baseEnd_2940863 : Nat := 167786250891492510409747

theorem tailTrace_2940863 : CollatzResearch.WordTrace tailWord_2940863 prefixEnd_2940863 167786250891492510409747 := by
  unfold tailWord_2940863
  simp only [CollatzResearch.WordTrace]
  refine ⟨107262085544763085258595243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71508057029842056839063495 107262085544763085258595243)
  ·
    refine ⟨160893128317144627887892865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107262085544763085258595243 160893128317144627887892865)
    ·
      refine ⟨120669846237858470915919649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160893128317144627887892865 120669846237858470915919649)
      ·
        refine ⟨90502384678393853186939737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120669846237858470915919649 90502384678393853186939737)
        ·
          refine ⟨67876788508795389890204803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90502384678393853186939737 67876788508795389890204803)
          ·
            refine ⟨101815182763193084835307205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67876788508795389890204803 101815182763193084835307205)
            ·
              refine ⟨19090346768098703406620101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101815182763193084835307205 19090346768098703406620101)
              ·
                refine ⟨3579440019018506888741269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19090346768098703406620101 3579440019018506888741269)
                ·
                  refine ⟨167786250891492510409747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3579440019018506888741269 167786250891492510409747)
                  ·
                    rfl

theorem cell23_2940863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 6].length) (baseStart_2940863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940863 prefixEnd_2940863 := by exact prefixLift 2940863
  have htrace : WordTrace (prefixWord ++ tailWord_2940863) baseStart_2940863 baseEnd_2940863 := by
    simpa [prefixWord, tailWord_2940863, baseEnd_2940863] using wordTrace_append hprefix tailTrace_2940863
  have hstable : (prefixWord ++ tailWord_2940863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940863).length < 2 ^ (prefixWord ++ tailWord_2940863).sum := by decide
  have hdescent : baseEnd_2940863 < baseStart_2940863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940880 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 6]
def baseStart_2940880 : Nat := 118140960795 + 2940880 * 2 ^ 59
def prefixEnd_2940880 : Nat := 4983230072969 + 3 ^ 40 * 2940880 * 2
def baseEnd_2940880 : Nat := 167787220799395447463905

theorem tailTrace_2940880 : CollatzResearch.WordTrace tailWord_2940880 prefixEnd_2940880 167787220799395447463905 := by
  unfold tailWord_2940880
  simp only [CollatzResearch.WordTrace]
  refine ⟨53631352792850748580982047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71508470390467664774642729 53631352792850748580982047)
  ·
    refine ⟨80447029189276122871473071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53631352792850748580982047 80447029189276122871473071)
    ·
      refine ⟨120670543783914184307209607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80447029189276122871473071 120670543783914184307209607)
      ·
        refine ⟨181005815675871276460814411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120670543783914184307209607 181005815675871276460814411)
        ·
          refine ⟨271508723513806914691221617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181005815675871276460814411 271508723513806914691221617)
          ·
            refine ⟨203631542635355186018416213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271508723513806914691221617 203631542635355186018416213)
            ·
              refine ⟨2386307140258068586153315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 203631542635355186018416213 2386307140258068586153315)
              ·
                refine ⟨3579460710387102879229973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386307140258068586153315 3579460710387102879229973)
                ·
                  refine ⟨167787220799395447463905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3579460710387102879229973 167787220799395447463905)
                  ·
                    rfl

theorem cell23_2940880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 6].length) (baseStart_2940880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940880 prefixEnd_2940880 := by exact prefixLift 2940880
  have htrace : WordTrace (prefixWord ++ tailWord_2940880) baseStart_2940880 baseEnd_2940880 := by
    simpa [prefixWord, tailWord_2940880, baseEnd_2940880] using wordTrace_append hprefix tailTrace_2940880
  have hstable : (prefixWord ++ tailWord_2940880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940880).length < 2 ^ (prefixWord ++ tailWord_2940880).sum := by decide
  have hdescent : baseEnd_2940880 < baseStart_2940880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940918 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2940918 : Nat := 118140960795 + 2940918 * 2 ^ 59
def prefixEnd_2940918 : Nat := 4983230072969 + 3 ^ 40 * 2940918 * 2
def baseEnd_2940918 : Nat := 503368166486476626166657

theorem tailTrace_2940918 : CollatzResearch.WordTrace tailWord_2940918 prefixEnd_2940918 503368166486476626166657 := by
  unfold tailWord_2940918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704005722472739353240463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71509394373042553101231605 6704005722472739353240463)
  ·
    refine ⟨10056008583709109029860695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704005722472739353240463 10056008583709109029860695)
    ·
      refine ⟨15084012875563663544791043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10056008583709109029860695 15084012875563663544791043)
      ·
        refine ⟨22626019313345495317186565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15084012875563663544791043 22626019313345495317186565)
        ·
          refine ⟨4242378621252280371972481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22626019313345495317186565 4242378621252280371972481)
          ·
            refine ⟨3181783965939210278979361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242378621252280371972481 3181783965939210278979361)
            ·
              refine ⟨2386337974454407709234521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181783965939210278979361 2386337974454407709234521)
              ·
                refine ⟨1789753480840805781925891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386337974454407709234521 1789753480840805781925891)
                ·
                  refine ⟨2684630221261208672888837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789753480840805781925891 2684630221261208672888837)
                  ·
                    refine ⟨503368166486476626166657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684630221261208672888837 503368166486476626166657)
                    ·
                      rfl

theorem cell23_2940918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2940918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940918 prefixEnd_2940918 := by exact prefixLift 2940918
  have htrace : WordTrace (prefixWord ++ tailWord_2940918) baseStart_2940918 baseEnd_2940918 := by
    simpa [prefixWord, tailWord_2940918, baseEnd_2940918] using wordTrace_append hprefix tailTrace_2940918
  have hstable : (prefixWord ++ tailWord_2940918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940918).length < 2 ^ (prefixWord ++ tailWord_2940918).sum := by decide
  have hdescent : baseEnd_2940918 < baseStart_2940918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940924 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_2940924 : Nat := 118140960795 + 2940924 * 2 ^ 59
def prefixEnd_2940924 : Nat := 4983230072969 + 3 ^ 40 * 2940924 * 2
def baseEnd_2940924 : Nat := 1510107580343356855024943

theorem tailTrace_2940924 : CollatzResearch.WordTrace tailWord_2940924 prefixEnd_2940924 1510107580343356855024943 := by
  unfold tailWord_2940924
  simp only [CollatzResearch.WordTrace]
  refine ⟨53632155198771046338282913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71509540265028061784377217 53632155198771046338282913)
  ·
    refine ⟨40224116399078284753712185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53632155198771046338282913 40224116399078284753712185)
    ·
      refine ⟨30168087299308713565284139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40224116399078284753712185 30168087299308713565284139)
      ·
        refine ⟨45252130948963070347926209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30168087299308713565284139 45252130948963070347926209)
        ·
          refine ⟨33939098211722302760944657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45252130948963070347926209 33939098211722302760944657)
          ·
            refine ⟨25454323658791727070708493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33939098211722302760944657 25454323658791727070708493)
            ·
              refine ⟨9545371372046897651515685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25454323658791727070708493 9545371372046897651515685)
              ·
                refine ⟨1789757132258793309659191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9545371372046897651515685 1789757132258793309659191)
                ·
                  refine ⟨2684635698388189964488787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789757132258793309659191 2684635698388189964488787)
                  ·
                    refine ⟨4026953547582284946733181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684635698388189964488787 4026953547582284946733181)
                    ·
                      refine ⟨1510107580343356855024943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4026953547582284946733181 1510107580343356855024943)
                      ·
                        rfl

theorem cell23_2940924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_2940924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940924 prefixEnd_2940924 := by exact prefixLift 2940924
  have htrace : WordTrace (prefixWord ++ tailWord_2940924) baseStart_2940924 baseEnd_2940924 := by
    simpa [prefixWord, tailWord_2940924, baseEnd_2940924] using wordTrace_append hprefix tailTrace_2940924
  have hstable : (prefixWord ++ tailWord_2940924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940924).length < 2 ^ (prefixWord ++ tailWord_2940924).sum := by decide
  have hdescent : baseEnd_2940924 < baseStart_2940924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940940 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_2940940 : Nat := 118140960795 + 2940940 * 2 ^ 59
def prefixEnd_2940940 : Nat := 4983230072969 + 3 ^ 40 * 2940940 * 2
def baseEnd_2940940 : Nat := 503371932011276264141623

theorem tailTrace_2940940 : CollatzResearch.WordTrace tailWord_2940940 prefixEnd_2940940 503371932011276264141623 := by
  unfold tailWord_2940940
  simp only [CollatzResearch.WordTrace]
  refine ⟨53632446982742063704574137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71509929310322751606098849 53632446982742063704574137)
  ·
    refine ⟨40224335237056547778430603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53632446982742063704574137 40224335237056547778430603)
    ·
      refine ⟨60336502855584821667645905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40224335237056547778430603 60336502855584821667645905)
      ·
        refine ⟨45252377141688616250734429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60336502855584821667645905 45252377141688616250734429)
        ·
          refine ⟨16969641428133231094025411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45252377141688616250734429 16969641428133231094025411)
          ·
            refine ⟨25454462142199846641038117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16969641428133231094025411 25454462142199846641038117)
            ·
              refine ⟨4772711651662471245194647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25454462142199846641038117 4772711651662471245194647)
              ·
                refine ⟨7159067477493706867791971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772711651662471245194647 7159067477493706867791971)
                ·
                  refine ⟨10738601216240560301687957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159067477493706867791971 10738601216240560301687957)
                  ·
                    refine ⟨503371932011276264141623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10738601216240560301687957 503371932011276264141623)
                    ·
                      rfl

theorem cell23_2940940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_2940940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940940 prefixEnd_2940940 := by exact prefixLift 2940940
  have htrace : WordTrace (prefixWord ++ tailWord_2940940) baseStart_2940940 baseEnd_2940940 := by
    simpa [prefixWord, tailWord_2940940, baseEnd_2940940] using wordTrace_append hprefix tailTrace_2940940
  have hstable : (prefixWord ++ tailWord_2940940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940940).length < 2 ^ (prefixWord ++ tailWord_2940940).sum := by decide
  have hdescent : baseEnd_2940940 < baseStart_2940940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940947 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 5, 2, 2]
def baseStart_2940947 : Nat := 118140960795 + 2940947 * 2 ^ 59
def prefixEnd_2940947 : Nat := 4983230072969 + 3 ^ 40 * 2940947 * 2
def baseEnd_2940947 : Nat := 1510119390398410265037337

theorem tailTrace_2940947 : CollatzResearch.WordTrace tailWord_2940947 prefixEnd_2940947 1510119390398410265037337 := by
  unfold tailWord_2940947
  simp only [CollatzResearch.WordTrace]
  refine ⟨107265149276458767604653095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71510099517639178403102063 107265149276458767604653095)
  ·
    refine ⟨160897723914688151406979643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107265149276458767604653095 160897723914688151406979643)
    ·
      refine ⟨241346585872032227110469465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160897723914688151406979643 241346585872032227110469465)
      ·
        refine ⟨181009939404024170332852099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241346585872032227110469465 181009939404024170332852099)
        ·
          refine ⟨271514909106036255499278149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181009939404024170332852099 271514909106036255499278149)
          ·
            refine ⟨50909045457381797906114653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271514909106036255499278149 50909045457381797906114653)
            ·
              refine ⟨19090892046518174214792995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50909045457381797906114653 19090892046518174214792995)
              ·
                refine ⟨28636338069777261322189493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19090892046518174214792995 28636338069777261322189493)
                ·
                  refine ⟨2684656694041618248955265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28636338069777261322189493 2684656694041618248955265)
                  ·
                    refine ⟨2013492520531213686716449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2684656694041618248955265 2013492520531213686716449)
                    ·
                      refine ⟨1510119390398410265037337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013492520531213686716449 1510119390398410265037337)
                      ·
                        rfl

theorem cell23_2940947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2, 2].length) (baseStart_2940947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940947 prefixEnd_2940947 := by exact prefixLift 2940947
  have htrace : WordTrace (prefixWord ++ tailWord_2940947) baseStart_2940947 baseEnd_2940947 := by
    simpa [prefixWord, tailWord_2940947, baseEnd_2940947] using wordTrace_append hprefix tailTrace_2940947
  have hstable : (prefixWord ++ tailWord_2940947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940947).length < 2 ^ (prefixWord ++ tailWord_2940947).sum := by decide
  have hdescent : baseEnd_2940947 < baseStart_2940947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940951 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2940951 : Nat := 118140960795 + 2940951 * 2 ^ 59
def prefixEnd_2940951 : Nat := 4983230072969 + 3 ^ 40 * 2940951 * 2
def baseEnd_2940951 : Nat := 1510121444321028249387319

theorem tailTrace_2940951 : CollatzResearch.WordTrace tailWord_2940951 prefixEnd_2940951 1510121444321028249387319 := by
  unfold tailWord_2940951
  simp only [CollatzResearch.WordTrace]
  refine ⟨107265295168444276287798707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71510196778962850858532471 107265295168444276287798707)
  ·
    refine ⟨160897942752666414431698061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107265295168444276287798707 160897942752666414431698061)
    ·
      refine ⟨60336728532249905411886773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160897942752666414431698061 60336728532249905411886773)
      ·
        refine ⟨5656568299898428632364385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60336728532249905411886773 5656568299898428632364385)
        ·
          refine ⟨4242426224923821474273289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656568299898428632364385 4242426224923821474273289)
          ·
            refine ⟨3181819668692866105704967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242426224923821474273289 3181819668692866105704967)
            ·
              refine ⟨4772729503039299158557451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181819668692866105704967 4772729503039299158557451)
              ·
                refine ⟨7159094254558948737836177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772729503039299158557451 7159094254558948737836177)
                ·
                  refine ⟨5369320690919211553377133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7159094254558948737836177 5369320690919211553377133)
                  ·
                    refine ⟨2013495259094704332516425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5369320690919211553377133 2013495259094704332516425)
                    ·
                      refine ⟨1510121444321028249387319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013495259094704332516425 1510121444321028249387319)
                      ·
                        rfl

theorem cell23_2940951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2940951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940951 prefixEnd_2940951 := by exact prefixLift 2940951
  have htrace : WordTrace (prefixWord ++ tailWord_2940951) baseStart_2940951 baseEnd_2940951 := by
    simpa [prefixWord, tailWord_2940951, baseEnd_2940951] using wordTrace_append hprefix tailTrace_2940951
  have hstable : (prefixWord ++ tailWord_2940951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940951).length < 2 ^ (prefixWord ++ tailWord_2940951).sum := by decide
  have hdescent : baseEnd_2940951 < baseStart_2940951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940961 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 1, 5]
def baseStart_2940961 : Nat := 118140960795 + 2940961 * 2 ^ 59
def prefixEnd_2940961 : Nat := 4983230072969 + 3 ^ 40 * 2940961 * 2
def baseEnd_2940961 : Nat := 503375526375857736754091

theorem tailTrace_2940961 : CollatzResearch.WordTrace tailWord_2940961 prefixEnd_2940961 503375526375857736754091 := by
  unfold tailWord_2940961
  simp only [CollatzResearch.WordTrace]
  refine ⟨107265659898408047995662737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71510439932272031997108491 107265659898408047995662737)
  ·
    refine ⟨80449244923806035996747053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107265659898408047995662737 80449244923806035996747053)
    ·
      refine ⟨30168466846427263498780145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80449244923806035996747053 30168466846427263498780145)
      ·
        refine ⟨22626350134820447624085109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30168466846427263498780145 22626350134820447624085109)
        ·
          refine ⟨2121220325139416964757979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22626350134820447624085109 2121220325139416964757979)
          ·
            refine ⟨3181830487709125447136969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121220325139416964757979 3181830487709125447136969)
            ·
              refine ⟨2386372865781844085352727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181830487709125447136969 2386372865781844085352727)
              ·
                refine ⟨3579559298672766128029091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386372865781844085352727 3579559298672766128029091)
                ·
                  refine ⟨5369338948009149192043637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579559298672766128029091 5369338948009149192043637)
                  ·
                    refine ⟨503375526375857736754091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5369338948009149192043637 503375526375857736754091)
                    ·
                      rfl

theorem cell23_2940961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_2940961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940961 prefixEnd_2940961 := by exact prefixLift 2940961
  have htrace : WordTrace (prefixWord ++ tailWord_2940961) baseStart_2940961 baseEnd_2940961 := by
    simpa [prefixWord, tailWord_2940961, baseEnd_2940961] using wordTrace_append hprefix tailTrace_2940961
  have hstable : (prefixWord ++ tailWord_2940961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940961).length < 2 ^ (prefixWord ++ tailWord_2940961).sum := by decide
  have hdescent : baseEnd_2940961 < baseStart_2940961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940964 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2940964 : Nat := 118140960795 + 2940964 * 2 ^ 59
def prefixEnd_2940964 : Nat := 4983230072969 + 3 ^ 40 * 2940964 * 2
def baseEnd_2940964 : Nat := 1510128119569536698524759

theorem tailTrace_2940964 : CollatzResearch.WordTrace tailWord_2940964 prefixEnd_2940964 1510128119569536698524759 := by
  unfold tailWord_2940964
  simp only [CollatzResearch.WordTrace]
  refine ⟨53632884658698589754010973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71510512878264786338681297 53632884658698589754010973)
  ·
    refine ⟨20112331747011971157754115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53632884658698589754010973 20112331747011971157754115)
    ·
      refine ⟨30168497620517956736631173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20112331747011971157754115 30168497620517956736631173)
      ·
        refine ⟨5656593303847116888118345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30168497620517956736631173 5656593303847116888118345)
        ·
          refine ⟨4242444977885337666088759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656593303847116888118345 4242444977885337666088759)
          ·
            refine ⟨6363667466828006499133139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242444977885337666088759 6363667466828006499133139)
            ·
              refine ⟨9545501200242009748699709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363667466828006499133139 9545501200242009748699709)
              ·
                refine ⟨3579562950090753655762391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9545501200242009748699709 3579562950090753655762391)
                ·
                  refine ⟨5369344425136130483643587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579562950090753655762391 5369344425136130483643587)
                  ·
                    refine ⟨8054016637704195725465381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369344425136130483643587 8054016637704195725465381)
                    ·
                      refine ⟨1510128119569536698524759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8054016637704195725465381 1510128119569536698524759)
                      ·
                        rfl

theorem cell23_2940964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2940964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940964 prefixEnd_2940964 := by exact prefixLift 2940964
  have htrace : WordTrace (prefixWord ++ tailWord_2940964) baseStart_2940964 baseEnd_2940964 := by
    simpa [prefixWord, tailWord_2940964, baseEnd_2940964] using wordTrace_append hprefix tailTrace_2940964
  have hstable : (prefixWord ++ tailWord_2940964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940964).length < 2 ^ (prefixWord ++ tailWord_2940964).sum := by decide
  have hdescent : baseEnd_2940964 < baseStart_2940964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940970 : List Nat := [3, 1, 4, 1, 2, 2, 10]
def baseStart_2940970 : Nat := 118140960795 + 2940970 * 2 ^ 59
def prefixEnd_2940970 : Nat := 4983230072969 + 3 ^ 40 * 2940970 * 2
def baseEnd_2940970 : Nat := 18643595067326712037651

theorem tailTrace_2940970 : CollatzResearch.WordTrace tailWord_2940970 prefixEnd_2940970 18643595067326712037651 := by
  unfold tailWord_2940970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816497038843860633185091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71510658770250295021826909 26816497038843860633185091)
  ·
    refine ⟨40224745558265790949777637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26816497038843860633185091 40224745558265790949777637)
    ·
      refine ⟨7542139792174835803083307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40224745558265790949777637 7542139792174835803083307)
      ·
        refine ⟨11313209688262253704624961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542139792174835803083307 11313209688262253704624961)
        ·
          refine ⟨8484907266196690278468721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11313209688262253704624961 8484907266196690278468721)
          ·
            refine ⟨6363680449647517708851541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8484907266196690278468721 6363680449647517708851541)
            ·
              refine ⟨18643595067326712037651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6363680449647517708851541 18643595067326712037651)
              ·
                rfl

theorem cell23_2940970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 10].length) (baseStart_2940970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940970 prefixEnd_2940970 := by exact prefixLift 2940970
  have htrace : WordTrace (prefixWord ++ tailWord_2940970) baseStart_2940970 baseEnd_2940970 := by
    simpa [prefixWord, tailWord_2940970, baseEnd_2940970] using wordTrace_append hprefix tailTrace_2940970
  have hstable : (prefixWord ++ tailWord_2940970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940970).length < 2 ^ (prefixWord ++ tailWord_2940970).sum := by decide
  have hdescent : baseEnd_2940970 < baseStart_2940970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940974 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2940974 : Nat := 118140960795 + 2940974 * 2 ^ 59
def prefixEnd_2940974 : Nat := 4983230072969 + 3 ^ 40 * 2940974 * 2
def baseEnd_2940974 : Nat := 503377751458693886466571

theorem tailTrace_2940974 : CollatzResearch.WordTrace tailWord_2940974 prefixEnd_2940974 503377751458693886466571 := by
  unfold tailWord_2940974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408266755920118901985747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71510756031573967477257317 13408266755920118901985747)
  ·
    refine ⟨20112400133880178352978621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13408266755920118901985747 20112400133880178352978621)
    ·
      refine ⟨7542150050205066882366983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20112400133880178352978621 7542150050205066882366983)
      ·
        refine ⟨11313225075307600323550475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542150050205066882366983 11313225075307600323550475)
        ·
          refine ⟨16969837612961400485325713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11313225075307600323550475 16969837612961400485325713)
          ·
            refine ⟨12727378209721050363994285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16969837612961400485325713 12727378209721050363994285)
            ·
              refine ⟨4772766828645393886497857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12727378209721050363994285 4772766828645393886497857)
              ·
                refine ⟨3579575121484045414873393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772766828645393886497857 3579575121484045414873393)
                ·
                  refine ⟨2684681341113034061155045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3579575121484045414873393 2684681341113034061155045)
                  ·
                    refine ⟨503377751458693886466571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684681341113034061155045 503377751458693886466571)
                    ·
                      rfl

theorem cell23_2940974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2940974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940974 prefixEnd_2940974 := by exact prefixLift 2940974
  have htrace : WordTrace (prefixWord ++ tailWord_2940974) baseStart_2940974 baseEnd_2940974 := by
    simpa [prefixWord, tailWord_2940974, baseEnd_2940974] using wordTrace_append hprefix tailTrace_2940974
  have hstable : (prefixWord ++ tailWord_2940974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940974).length < 2 ^ (prefixWord ++ tailWord_2940974).sum := by decide
  have hdescent : baseEnd_2940974 < baseStart_2940974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940981 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_2940981 : Nat := 118140960795 + 2940981 * 2 ^ 59
def prefixEnd_2940981 : Nat := 4983230072969 + 3 ^ 40 * 2940981 * 2
def baseEnd_2940981 : Nat := 1510136848740663132012181

theorem tailTrace_2940981 : CollatzResearch.WordTrace tailWord_2940981 prefixEnd_2940981 1510136848740663132012181 := by
  unfold tailWord_2940981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107266389358335591411390797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71510926238890394274260531 107266389358335591411390797)
  ·
    refine ⟨40224896009375846779271549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107266389358335591411390797 40224896009375846779271549)
    ·
      refine ⟨15084336003515942542226831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40224896009375846779271549 15084336003515942542226831)
      ·
        refine ⟨22626504005273913813340247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15084336003515942542226831 22626504005273913813340247)
        ·
          refine ⟨33939756007910870720010371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22626504005273913813340247 33939756007910870720010371)
          ·
            refine ⟨50909634011866306080015557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33939756007910870720010371 50909634011866306080015557)
            ·
              refine ⟨9545556377224932390002917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50909634011866306080015557 9545556377224932390002917)
              ·
                refine ⟨1789791820729674823125547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9545556377224932390002917 1789791820729674823125547)
                ·
                  refine ⟨2684687731094512234688321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789791820729674823125547 2684687731094512234688321)
                  ·
                    refine ⟨2013515798320884176016241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2684687731094512234688321 2013515798320884176016241)
                    ·
                      refine ⟨1510136848740663132012181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013515798320884176016241 1510136848740663132012181)
                      ·
                        rfl

theorem cell23_2940981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_2940981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940981 prefixEnd_2940981 := by exact prefixLift 2940981
  have htrace : WordTrace (prefixWord ++ tailWord_2940981) baseStart_2940981 baseEnd_2940981 := by
    simpa [prefixWord, tailWord_2940981, baseEnd_2940981] using wordTrace_append hprefix tailTrace_2940981
  have hstable : (prefixWord ++ tailWord_2940981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940981).length < 2 ^ (prefixWord ++ tailWord_2940981).sum := by decide
  have hdescent : baseEnd_2940981 < baseStart_2940981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940983 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 9]
def baseStart_2940983 : Nat := 118140960795 + 2940983 * 2 ^ 59
def prefixEnd_2940983 : Nat := 4983230072969 + 3 ^ 40 * 2940983 * 2
def baseEnd_2940983 : Nat := 503379291900657374729057

theorem tailTrace_2940983 : CollatzResearch.WordTrace tailWord_2940983 prefixEnd_2940983 503379291900657374729057 := by
  unfold tailWord_2940983
  simp only [CollatzResearch.WordTrace]
  refine ⟨107266462304328345752963603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71510974869552230501975735 107266462304328345752963603)
  ·
    refine ⟨160899693456492518629445405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107266462304328345752963603 160899693456492518629445405)
    ·
      refine ⟨60337385046184694486042027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160899693456492518629445405 60337385046184694486042027)
      ·
        refine ⟨90506077569277041729063041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60337385046184694486042027 90506077569277041729063041)
        ·
          refine ⟨67879558176957781296797281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90506077569277041729063041 67879558176957781296797281)
          ·
            refine ⟨50909668632718335972597961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67879558176957781296797281 50909668632718335972597961)
            ·
              refine ⟨38182251474538751979448471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50909668632718335972597961 38182251474538751979448471)
              ·
                refine ⟨57273377211808127969172707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38182251474538751979448471 57273377211808127969172707)
                ·
                  refine ⟨85910065817712191953759061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57273377211808127969172707 85910065817712191953759061)
                  ·
                    refine ⟨503379291900657374729057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85910065817712191953759061 503379291900657374729057)
                    ·
                      rfl

theorem cell23_2940983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_2940983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2940983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2940983 prefixEnd_2940983 := by exact prefixLift 2940983
  have htrace : WordTrace (prefixWord ++ tailWord_2940983) baseStart_2940983 baseEnd_2940983 := by
    simpa [prefixWord, tailWord_2940983, baseEnd_2940983] using wordTrace_append hprefix tailTrace_2940983
  have hstable : (prefixWord ++ tailWord_2940983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940983).length < 2 ^ (prefixWord ++ tailWord_2940983).sum := by decide
  have hdescent : baseEnd_2940983 < baseStart_2940983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941024 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2]
def baseStart_2941024 : Nat := 118140960795 + 2941024 * 2 ^ 59
def prefixEnd_2941024 : Nat := 4983230072969 + 3 ^ 40 * 2941024 * 2
def baseEnd_2941024 : Nat := 1510158928408806463774483

theorem tailTrace_2941024 : CollatzResearch.WordTrace tailWord_2941024 prefixEnd_2941024 1510158928408806463774483 := by
  unfold tailWord_2941024
  simp only [CollatzResearch.WordTrace]
  refine ⟨53633978848589904877603063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71511971798119873170137417 53633978848589904877603063)
  ·
    refine ⟨80450968272884857316404595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53633978848589904877603063 80450968272884857316404595)
    ·
      refine ⟨120676452409327285974606893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80450968272884857316404595 120676452409327285974606893)
      ·
        refine ⟨45253669653497732240477585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120676452409327285974606893 45253669653497732240477585)
        ·
          refine ⟨33940252240123299180358189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45253669653497732240477585 33940252240123299180358189)
          ·
            refine ⟨12727594590046237192634321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33940252240123299180358189 12727594590046237192634321)
            ·
              refine ⟨9545695942534677894475741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12727594590046237192634321 9545695942534677894475741)
              ·
                refine ⟨3579635978450504210428403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9545695942534677894475741 3579635978450504210428403)
                ·
                  refine ⟨5369453967675756315642605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579635978450504210428403 5369453967675756315642605)
                  ·
                    refine ⟨2013545237878408618365977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5369453967675756315642605 2013545237878408618365977)
                    ·
                      refine ⟨1510158928408806463774483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013545237878408618365977 1510158928408806463774483)
                      ·
                        rfl

theorem cell23_2941024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_2941024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941024 prefixEnd_2941024 := by exact prefixLift 2941024
  have htrace : WordTrace (prefixWord ++ tailWord_2941024) baseStart_2941024 baseEnd_2941024 := by
    simpa [prefixWord, tailWord_2941024, baseEnd_2941024] using wordTrace_append hprefix tailTrace_2941024
  have hstable : (prefixWord ++ tailWord_2941024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941024).length < 2 ^ (prefixWord ++ tailWord_2941024).sum := by decide
  have hdescent : baseEnd_2941024 < baseStart_2941024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941060 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 9]
def baseStart_2941060 : Nat := 118140960795 + 2941060 * 2 ^ 59
def prefixEnd_2941060 : Nat := 4983230072969 + 3 ^ 40 * 2941060 * 2
def baseEnd_2941060 : Nat := 167797490412485369213813

theorem tailTrace_2941060 : CollatzResearch.WordTrace tailWord_2941060 prefixEnd_2941060 167797490412485369213813 := by
  unfold tailWord_2941060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53634635362524693951758317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71512847150032925269011089 53634635362524693951758317)
  ·
    refine ⟨20112988260946760231909369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53634635362524693951758317 20112988260946760231909369)
    ·
      refine ⟨15084741195710070173932027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20112988260946760231909369 15084741195710070173932027)
      ·
        refine ⟨22627111793565105260898041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15084741195710070173932027 22627111793565105260898041)
        ·
          refine ⟨16970333845173828945673531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22627111793565105260898041 16970333845173828945673531)
          ·
            refine ⟨25455500767760743418510297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16970333845173828945673531 25455500767760743418510297)
            ·
              refine ⟨19091625575820557563882723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25455500767760743418510297 19091625575820557563882723)
              ·
                refine ⟨28637438363730836345824085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19091625575820557563882723 28637438363730836345824085)
                ·
                  refine ⟨167797490412485369213813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28637438363730836345824085 167797490412485369213813)
                  ·
                    rfl

theorem cell23_2941060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_2941060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941060 prefixEnd_2941060 := by exact prefixLift 2941060
  have htrace : WordTrace (prefixWord ++ tailWord_2941060) baseStart_2941060 baseEnd_2941060 := by
    simpa [prefixWord, tailWord_2941060, baseEnd_2941060] using wordTrace_append hprefix tailTrace_2941060
  have hstable : (prefixWord ++ tailWord_2941060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941060).length < 2 ^ (prefixWord ++ tailWord_2941060).sum := by decide
  have hdescent : baseEnd_2941060 < baseStart_2941060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941077 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 5]
def baseStart_2941077 : Nat := 118140960795 + 2941077 * 2 ^ 59
def prefixEnd_2941077 : Nat := 4983230072969 + 3 ^ 40 * 2941077 * 2
def baseEnd_2941077 : Nat := 167798460320388306267971

theorem tailTrace_2941077 : CollatzResearch.WordTrace tailWord_2941077 prefixEnd_2941077 167798460320388306267971 := by
  unfold tailWord_2941077
  simp only [CollatzResearch.WordTrace]
  refine ⟨107269890765987799806885485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71513260510658533204590323 107269890765987799806885485)
  ·
    refine ⟨40226209037245424927582057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107269890765987799806885485 40226209037245424927582057)
    ·
      refine ⟨30169656777934068695686543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40226209037245424927582057 30169656777934068695686543)
      ·
        refine ⟨45254485166901103043529815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30169656777934068695686543 45254485166901103043529815)
        ·
          refine ⟨67881727750351654565294723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45254485166901103043529815 67881727750351654565294723)
          ·
            refine ⟨101822591625527481847942085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67881727750351654565294723 101822591625527481847942085)
            ·
              refine ⟨19091735929786402846489141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101822591625527481847942085 19091735929786402846489141)
              ·
                refine ⟨1789850243417475266858357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19091735929786402846489141 1789850243417475266858357)
                ·
                  refine ⟨167798460320388306267971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789850243417475266858357 167798460320388306267971)
                  ·
                    rfl

theorem cell23_2941077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_2941077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941077 prefixEnd_2941077 := by exact prefixLift 2941077
  have htrace : WordTrace (prefixWord ++ tailWord_2941077) baseStart_2941077 baseEnd_2941077 := by
    simpa [prefixWord, tailWord_2941077, baseEnd_2941077] using wordTrace_append hprefix tailTrace_2941077
  have hstable : (prefixWord ++ tailWord_2941077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941077).length < 2 ^ (prefixWord ++ tailWord_2941077).sum := by decide
  have hdescent : baseEnd_2941077 < baseStart_2941077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941124 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2941124 : Nat := 118140960795 + 2941124 * 2 ^ 59
def prefixEnd_2941124 : Nat := 4983230072969 + 3 ^ 40 * 2941124 * 2
def baseEnd_2941124 : Nat := 503403425491418690841341

theorem tailTrace_2941124 : CollatzResearch.WordTrace tailWord_2941124 prefixEnd_2941124 503403425491418690841341 := by
  unfold tailWord_2941124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53635802498408763416923213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71514403331211684555897617 53635802498408763416923213)
  ·
    refine ⟨20113425936903286281346205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53635802498408763416923213 20113425936903286281346205)
    ·
      refine ⟨7542534726338732355504827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20113425936903286281346205 7542534726338732355504827)
      ·
        refine ⟨11313802089508098533257241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542534726338732355504827 11313802089508098533257241)
        ·
          refine ⟨8485351567131073899942931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11313802089508098533257241 8485351567131073899942931)
          ·
            refine ⟨12728027350696610849914397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8485351567131073899942931 12728027350696610849914397)
            ·
              refine ⟨4773010256511229068717899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12728027350696610849914397 4773010256511229068717899)
              ·
                refine ⟨7159515384766843603076849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773010256511229068717899 7159515384766843603076849)
                ·
                  refine ⟨5369636538575132702307637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7159515384766843603076849 5369636538575132702307637)
                  ·
                    refine ⟨503403425491418690841341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5369636538575132702307637 503403425491418690841341)
                    ·
                      rfl

theorem cell23_2941124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2941124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941124 prefixEnd_2941124 := by exact prefixLift 2941124
  have htrace : WordTrace (prefixWord ++ tailWord_2941124) baseStart_2941124 baseEnd_2941124 := by
    simpa [prefixWord, tailWord_2941124, baseEnd_2941124] using wordTrace_append hprefix tailTrace_2941124
  have hstable : (prefixWord ++ tailWord_2941124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941124).length < 2 ^ (prefixWord ++ tailWord_2941124).sum := by decide
  have hdescent : baseEnd_2941124 < baseStart_2941124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941144 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_2941144 : Nat := 118140960795 + 2941144 * 2 ^ 59
def prefixEnd_2941144 : Nat := 4983230072969 + 3 ^ 40 * 2941144 * 2
def baseEnd_2941144 : Nat := 1510220546087345994273931

theorem tailTrace_2941144 : CollatzResearch.WordTrace tailWord_2941144 prefixEnd_2941144 1510220546087345994273931 := by
  unfold tailWord_2941144
  simp only [CollatzResearch.WordTrace]
  refine ⟨53636167228372535124787243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71514889637830046833049657 53636167228372535124787243)
  ·
    refine ⟨80454250842558802687180865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53636167228372535124787243 80454250842558802687180865)
    ·
      refine ⟨60340688131919102015385649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80454250842558802687180865 60340688131919102015385649)
      ·
        refine ⟨45255516098939326511539237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60340688131919102015385649 45255516098939326511539237)
        ·
          refine ⟨8485409268551123720913607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45255516098939326511539237 8485409268551123720913607)
          ·
            refine ⟨12728113902826685581370411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8485409268551123720913607 12728113902826685581370411)
            ·
              refine ⟨19092170854240028372055617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12728113902826685581370411 19092170854240028372055617)
              ·
                refine ⟨14319128140680021279041713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19092170854240028372055617 14319128140680021279041713)
                ·
                  refine ⟨10739346105510015959281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14319128140680021279041713 10739346105510015959281285)
                  ·
                    refine ⟨2013627394783127992365241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10739346105510015959281285 2013627394783127992365241)
                    ·
                      refine ⟨1510220546087345994273931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013627394783127992365241 1510220546087345994273931)
                      ·
                        rfl

theorem cell23_2941144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_2941144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941144 prefixEnd_2941144 := by exact prefixLift 2941144
  have htrace : WordTrace (prefixWord ++ tailWord_2941144) baseStart_2941144 baseEnd_2941144 := by
    simpa [prefixWord, tailWord_2941144, baseEnd_2941144] using wordTrace_append hprefix tailTrace_2941144
  have hstable : (prefixWord ++ tailWord_2941144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941144).length < 2 ^ (prefixWord ++ tailWord_2941144).sum := by decide
  have hdescent : baseEnd_2941144 < baseStart_2941144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941194 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2941194 : Nat := 118140960795 + 2941194 * 2 ^ 59
def prefixEnd_2941194 : Nat := 4983230072969 + 3 ^ 40 * 2941194 * 2
def baseEnd_2941194 : Nat := 1510246220120070798648701

theorem tailTrace_2941194 : CollatzResearch.WordTrace tailWord_2941194 prefixEnd_2941194 1510246220120070798648701 := by
  unfold tailWord_2941194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818539526640982197223659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71516105404375952525929757 26818539526640982197223659)
  ·
    refine ⟨40227809289961473295835489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26818539526640982197223659 40227809289961473295835489)
    ·
      refine ⟨30170856967471104971876617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40227809289961473295835489 30170856967471104971876617)
      ·
        refine ⟨22628142725603328728907463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30170856967471104971876617 22628142725603328728907463)
        ·
          refine ⟨33942214088404993093361195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22628142725603328728907463 33942214088404993093361195)
          ·
            refine ⟨50913321132607489640041793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33942214088404993093361195 50913321132607489640041793)
            ·
              refine ⟨38184990849455617230031345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50913321132607489640041793 38184990849455617230031345)
              ·
                refine ⟨28638743137091712922523509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38184990849455617230031345 28638743137091712922523509)
                ·
                  refine ⟨2684882169102348086486579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28638743137091712922523509 2684882169102348086486579)
                  ·
                    refine ⟨4027323253653522129729869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684882169102348086486579 4027323253653522129729869)
                    ·
                      refine ⟨1510246220120070798648701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4027323253653522129729869 1510246220120070798648701)
                      ·
                        rfl

theorem cell23_2941194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2941194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941194 prefixEnd_2941194 := by exact prefixLift 2941194
  have htrace : WordTrace (prefixWord ++ tailWord_2941194) baseStart_2941194 baseEnd_2941194 := by
    simpa [prefixWord, tailWord_2941194, baseEnd_2941194] using wordTrace_append hprefix tailTrace_2941194
  have hstable : (prefixWord ++ tailWord_2941194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941194).length < 2 ^ (prefixWord ++ tailWord_2941194).sum := by decide
  have hdescent : baseEnd_2941194 < baseStart_2941194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941200 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_2941200 : Nat := 118140960795 + 2941200 * 2 ^ 59
def prefixEnd_2941200 : Nat := 4983230072969 + 3 ^ 40 * 2941200 * 2
def baseEnd_2941200 : Nat := 1510249301003997775173673

theorem tailTrace_2941200 : CollatzResearch.WordTrace tailWord_2941200 prefixEnd_2941200 1510249301003997775173673 := by
  unfold tailWord_2941200
  simp only [CollatzResearch.WordTrace]
  refine ⟨53637188472271095906806527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71516251296361461209075369 53637188472271095906806527)
  ·
    refine ⟨80455782708406643860209791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53637188472271095906806527 80455782708406643860209791)
    ·
      refine ⟨120683674062609965790314687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80455782708406643860209791 120683674062609965790314687)
      ·
        refine ⟨181025511093914948685472031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120683674062609965790314687 181025511093914948685472031)
        ·
          refine ⟨271538266640872423028208047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181025511093914948685472031 271538266640872423028208047)
          ·
            refine ⟨407307399961308634542312071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271538266640872423028208047 407307399961308634542312071)
            ·
              refine ⟨610961099941962951813468107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407307399961308634542312071 610961099941962951813468107)
              ·
                refine ⟨916441649912944427720202161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610961099941962951813468107 916441649912944427720202161)
                ·
                  refine ⟨687331237434708320790151621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916441649912944427720202161 687331237434708320790151621)
                  ·
                    refine ⟨128874607019007810148153429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687331237434708320790151621 128874607019007810148153429)
                    ·
                      refine ⟨1510249301003997775173673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128874607019007810148153429 1510249301003997775173673)
                      ·
                        rfl

theorem cell23_2941200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_2941200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941200 prefixEnd_2941200 := by exact prefixLift 2941200
  have htrace : WordTrace (prefixWord ++ tailWord_2941200) baseStart_2941200 baseEnd_2941200 := by
    simpa [prefixWord, tailWord_2941200, baseEnd_2941200] using wordTrace_append hprefix tailTrace_2941200
  have hstable : (prefixWord ++ tailWord_2941200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941200).length < 2 ^ (prefixWord ++ tailWord_2941200).sum := by decide
  have hdescent : baseEnd_2941200 < baseStart_2941200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941211 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 1, 1, 3]
def baseStart_2941211 : Nat := 118140960795 + 2941211 * 2 ^ 59
def prefixEnd_2941211 : Nat := 4983230072969 + 3 ^ 40 * 2941211 * 2
def baseEnd_2941211 : Nat := 1510254949291197232136123

theorem tailTrace_2941211 : CollatzResearch.WordTrace tailWord_2941211 prefixEnd_2941211 1510254949291197232136123 := by
  unfold tailWord_2941211
  simp only [CollatzResearch.WordTrace]
  refine ⟨107274778147502340692263487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71516518765001560461508991 107274778147502340692263487)
  ·
    refine ⟨160912167221253511038395231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107274778147502340692263487 160912167221253511038395231)
    ·
      refine ⟨241368250831880266557592847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160912167221253511038395231 241368250831880266557592847)
      ·
        refine ⟨362052376247820399836389271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241368250831880266557592847 362052376247820399836389271)
        ·
          refine ⟨543078564371730599754583907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362052376247820399836389271 543078564371730599754583907)
          ·
            refine ⟨814617846557595899631875861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543078564371730599754583907 814617846557595899631875861)
            ·
              refine ⟨38185211557387307795244181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 814617846557595899631875861 38185211557387307795244181)
              ·
                refine ⟨1789931791752530052902071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38185211557387307795244181 1789931791752530052902071)
                ·
                  refine ⟨2684897687628795079353107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789931791752530052902071 2684897687628795079353107)
                  ·
                    refine ⟨4027346531443192619029661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684897687628795079353107 4027346531443192619029661)
                    ·
                      refine ⟨1510254949291197232136123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4027346531443192619029661 1510254949291197232136123)
                      ·
                        rfl

theorem cell23_2941211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 1, 3].length) (baseStart_2941211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941211 prefixEnd_2941211 := by exact prefixLift 2941211
  have htrace : WordTrace (prefixWord ++ tailWord_2941211) baseStart_2941211 baseEnd_2941211 := by
    simpa [prefixWord, tailWord_2941211, baseEnd_2941211] using wordTrace_append hprefix tailTrace_2941211
  have hstable : (prefixWord ++ tailWord_2941211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941211).length < 2 ^ (prefixWord ++ tailWord_2941211).sum := by decide
  have hdescent : baseEnd_2941211 < baseStart_2941211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941297 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2941297 : Nat := 118140960795 + 2941297 * 2 ^ 59
def prefixEnd_2941297 : Nat := 4983230072969 + 3 ^ 40 * 2941297 * 2
def baseEnd_2941297 : Nat := 1510299108627483895660727

theorem tailTrace_2941297 : CollatzResearch.WordTrace tailWord_2941297 prefixEnd_2941297 1510299108627483895660727 := by
  unfold tailWord_2941297
  simp only [CollatzResearch.WordTrace]
  refine ⟨107277914825190777379894145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71518609883460518253262763 107277914825190777379894145)
  ·
    refine ⟨80458436118893083034920609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107277914825190777379894145 80458436118893083034920609)
    ·
      refine ⟨60343827089169812276190457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80458436118893083034920609 60343827089169812276190457)
      ·
        refine ⟨45257870316877359207142843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60343827089169812276190457 45257870316877359207142843)
        ·
          refine ⟨67886805475316038810714265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45257870316877359207142843 67886805475316038810714265)
          ·
            refine ⟨50915104106487029108035699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67886805475316038810714265 50915104106487029108035699)
            ·
              refine ⟨76372656159730543662053549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50915104106487029108035699 76372656159730543662053549)
              ·
                refine ⟨28639746059898953873270081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76372656159730543662053549 28639746059898953873270081)
                ·
                  refine ⟨21479809544924215404952561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28639746059898953873270081 21479809544924215404952561)
                  ·
                    refine ⟨16109857158693161553714421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21479809544924215404952561 16109857158693161553714421)
                    ·
                      refine ⟨1510299108627483895660727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16109857158693161553714421 1510299108627483895660727)
                      ·
                        rfl

theorem cell23_2941297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2941297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941297 prefixEnd_2941297 := by exact prefixLift 2941297
  have htrace : WordTrace (prefixWord ++ tailWord_2941297) baseStart_2941297 baseEnd_2941297 := by
    simpa [prefixWord, tailWord_2941297, baseEnd_2941297] using wordTrace_append hprefix tailTrace_2941297
  have hstable : (prefixWord ++ tailWord_2941297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941297).length < 2 ^ (prefixWord ++ tailWord_2941297).sum := by decide
  have hdescent : baseEnd_2941297 < baseStart_2941297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941301 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2941301 : Nat := 118140960795 + 2941301 * 2 ^ 59
def prefixEnd_2941301 : Nat := 4983230072969 + 3 ^ 40 * 2941301 * 2
def baseEnd_2941301 : Nat := 1510301162550101880010709

theorem tailTrace_2941301 : CollatzResearch.WordTrace tailWord_2941301 prefixEnd_2941301 1510301162550101880010709 := by
  unfold tailWord_2941301
  simp only [CollatzResearch.WordTrace]
  refine ⟨107278060717176286063039757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71518707144784190708693171 107278060717176286063039757)
  ·
    refine ⟨40229272768941107273639909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107278060717176286063039757 40229272768941107273639909)
    ·
      refine ⟨7542988644176457613807483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40229272768941107273639909 7542988644176457613807483)
      ·
        refine ⟨11314482966264686420711225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542988644176457613807483 11314482966264686420711225)
        ·
          refine ⟨8485862224698514815533419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11314482966264686420711225 8485862224698514815533419)
          ·
            refine ⟨12728793337047772223300129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8485862224698514815533419 12728793337047772223300129)
            ·
              refine ⟨9546595002785829167475097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12728793337047772223300129 9546595002785829167475097)
              ·
                refine ⟨7159946252089371875606323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9546595002785829167475097 7159946252089371875606323)
                ·
                  refine ⟨10739919378134057813409485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7159946252089371875606323 10739919378134057813409485)
                  ·
                    refine ⟨4027469766800271680028557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10739919378134057813409485 4027469766800271680028557)
                    ·
                      refine ⟨1510301162550101880010709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4027469766800271680028557 1510301162550101880010709)
                      ·
                        rfl

theorem cell23_2941301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2941301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941301 prefixEnd_2941301 := by exact prefixLift 2941301
  have htrace : WordTrace (prefixWord ++ tailWord_2941301) baseStart_2941301 baseEnd_2941301 := by
    simpa [prefixWord, tailWord_2941301, baseEnd_2941301] using wordTrace_append hprefix tailTrace_2941301
  have hstable : (prefixWord ++ tailWord_2941301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941301).length < 2 ^ (prefixWord ++ tailWord_2941301).sum := by decide
  have hdescent : baseEnd_2941301 < baseStart_2941301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941302 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2941302 : Nat := 118140960795 + 2941302 * 2 ^ 59
def prefixEnd_2941302 : Nat := 4983230072969 + 3 ^ 40 * 2941302 * 2
def baseEnd_2941302 : Nat := 1510301676030756376098205

theorem tailTrace_2941302 : CollatzResearch.WordTrace tailWord_2941302 prefixEnd_2941302 1510301676030756376098205 := by
  unfold tailWord_2941302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704881074385791452114135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71518731460115108822550773 6704881074385791452114135)
  ·
    refine ⟨10057321611578687178171203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704881074385791452114135 10057321611578687178171203)
    ·
      refine ⟨15085982417368030767256805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10057321611578687178171203 15085982417368030767256805)
      ·
        refine ⟨2828621703256505768860651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15085982417368030767256805 2828621703256505768860651)
        ·
          refine ⟨4242932554884758653290977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828621703256505768860651 4242932554884758653290977)
          ·
            refine ⟨3182199416163568989968233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242932554884758653290977 3182199416163568989968233)
            ·
              refine ⟨2386649562122676742476175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182199416163568989968233 2386649562122676742476175)
              ·
                refine ⟨3579974343184015113714263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386649562122676742476175 3579974343184015113714263)
                ·
                  refine ⟨5369961514776022670571395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579974343184015113714263 5369961514776022670571395)
                  ·
                    refine ⟨8054942272164034005857093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369961514776022670571395 8054942272164034005857093)
                    ·
                      refine ⟨1510301676030756376098205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8054942272164034005857093 1510301676030756376098205)
                      ·
                        rfl

theorem cell23_2941302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2941302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941302 prefixEnd_2941302 := by exact prefixLift 2941302
  have htrace : WordTrace (prefixWord ++ tailWord_2941302) baseStart_2941302 baseEnd_2941302 := by
    simpa [prefixWord, tailWord_2941302, baseEnd_2941302] using wordTrace_append hprefix tailTrace_2941302
  have hstable : (prefixWord ++ tailWord_2941302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941302).length < 2 ^ (prefixWord ++ tailWord_2941302).sum := by decide
  have hdescent : baseEnd_2941302 < baseStart_2941302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941311 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 1, 3, 2]
def baseStart_2941311 : Nat := 118140960795 + 2941311 * 2 ^ 59
def prefixEnd_2941311 : Nat := 4983230072969 + 3 ^ 40 * 2941311 * 2
def baseEnd_2941311 : Nat := 1510306297356646840885663

theorem tailTrace_2941311 : CollatzResearch.WordTrace tailWord_2941311 prefixEnd_2941311 1510306297356646840885663 := by
  unfold tailWord_2941311
  simp only [CollatzResearch.WordTrace]
  refine ⟨107278425447140057770903787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71518950298093371847269191 107278425447140057770903787)
  ·
    refine ⟨160917638170710086656355681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107278425447140057770903787 160917638170710086656355681)
    ·
      refine ⟨120688228628032564992266761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160917638170710086656355681 120688228628032564992266761)
      ·
        refine ⟨90516171471024423744200071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120688228628032564992266761 90516171471024423744200071)
        ·
          refine ⟨135774257206536635616300107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90516171471024423744200071 135774257206536635616300107)
          ·
            refine ⟨203661385809804953424450161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135774257206536635616300107 203661385809804953424450161)
            ·
              refine ⟨152746039357353715068337621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203661385809804953424450161 152746039357353715068337621)
              ·
                refine ⟨3579985297437977696914163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152746039357353715068337621 3579985297437977696914163)
                ·
                  refine ⟨5369977946156966545371245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579985297437977696914163 5369977946156966545371245)
                  ·
                    refine ⟨2013741729808862454514217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5369977946156966545371245 2013741729808862454514217)
                    ·
                      refine ⟨1510306297356646840885663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013741729808862454514217 1510306297356646840885663)
                      ·
                        rfl

theorem cell23_2941311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_2941311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941311 prefixEnd_2941311 := by exact prefixLift 2941311
  have htrace : WordTrace (prefixWord ++ tailWord_2941311) baseStart_2941311 baseEnd_2941311 := by
    simpa [prefixWord, tailWord_2941311, baseEnd_2941311] using wordTrace_append hprefix tailTrace_2941311
  have hstable : (prefixWord ++ tailWord_2941311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941311).length < 2 ^ (prefixWord ++ tailWord_2941311).sum := by decide
  have hdescent : baseEnd_2941311 < baseStart_2941311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941421 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2941421 : Nat := 118140960795 + 2941421 * 2 ^ 59
def prefixEnd_2941421 : Nat := 4983230072969 + 3 ^ 40 * 2941421 * 2
def baseEnd_2941421 : Nat := 1510362780228641410510157

theorem tailTrace_2941421 : CollatzResearch.WordTrace tailWord_2941421 prefixEnd_2941421 1510362780228641410510157 := by
  unfold tailWord_2941421
  simp only [CollatzResearch.WordTrace]
  refine ⟨107282437476741546557408117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71521624984494364371605411 107282437476741546557408117)
  ·
    refine ⟨10057728513444519989757011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107282437476741546557408117 10057728513444519989757011)
    ·
      refine ⟨15086592770166779984635517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10057728513444519989757011 15086592770166779984635517)
      ·
        refine ⟨5657472288812542494238319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15086592770166779984635517 5657472288812542494238319)
        ·
          refine ⟨8486208433218813741357479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657472288812542494238319 8486208433218813741357479)
          ·
            refine ⟨12729312649828220612036219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8486208433218813741357479 12729312649828220612036219)
            ·
              refine ⟨19093968974742330918054329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12729312649828220612036219 19093968974742330918054329)
              ·
                refine ⟨14320476731056748188540747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19093968974742330918054329 14320476731056748188540747)
                ·
                  refine ⟨21480715096585122282811121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14320476731056748188540747 21480715096585122282811121)
                  ·
                    refine ⟨16110536322438841712108341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21480715096585122282811121 16110536322438841712108341)
                    ·
                      refine ⟨1510362780228641410510157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16110536322438841712108341 1510362780228641410510157)
                      ·
                        rfl

theorem cell23_2941421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2941421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941421 prefixEnd_2941421 := by exact prefixLift 2941421
  have htrace : WordTrace (prefixWord ++ tailWord_2941421) baseStart_2941421 baseEnd_2941421 := by
    simpa [prefixWord, tailWord_2941421, baseEnd_2941421] using wordTrace_append hprefix tailTrace_2941421
  have hstable : (prefixWord ++ tailWord_2941421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941421).length < 2 ^ (prefixWord ++ tailWord_2941421).sum := by decide
  have hdescent : baseEnd_2941421 < baseStart_2941421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941468 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2941468 : Nat := 118140960795 + 2941468 * 2 ^ 59
def prefixEnd_2941468 : Nat := 4983230072969 + 3 ^ 40 * 2941468 * 2
def baseEnd_2941468 : Nat := 1510386913819402726622441

theorem tailTrace_2941468 : CollatzResearch.WordTrace tailWord_2941468 prefixEnd_2941468 1510386913819402726622441 := by
  unfold tailWord_2941468
  simp only [CollatzResearch.WordTrace]
  refine ⟨53642075853785636792184529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71522767805047515722912705 53642075853785636792184529)
  ·
    refine ⟨40231556890339227594138397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53642075853785636792184529 40231556890339227594138397)
    ·
      refine ⟨15086833833877210347801899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40231556890339227594138397 15086833833877210347801899)
      ·
        refine ⟨22630250750815815521702849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15086833833877210347801899 22630250750815815521702849)
        ·
          refine ⟨16972688063111861641277137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22630250750815815521702849 16972688063111861641277137)
          ·
            refine ⟨12729516047333896230957853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16972688063111861641277137 12729516047333896230957853)
            ·
              refine ⟨4773568517750211086609195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12729516047333896230957853 4773568517750211086609195)
              ·
                refine ⟨7160352776625316629913793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773568517750211086609195 7160352776625316629913793)
                ·
                  refine ⟨5370264582468987472435345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7160352776625316629913793 5370264582468987472435345)
                  ·
                    refine ⟨4027698436851740604326509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370264582468987472435345 4027698436851740604326509)
                    ·
                      refine ⟨1510386913819402726622441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4027698436851740604326509 1510386913819402726622441)
                      ·
                        rfl

theorem cell23_2941468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2941468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941468 prefixEnd_2941468 := by exact prefixLift 2941468
  have htrace : WordTrace (prefixWord ++ tailWord_2941468) baseStart_2941468 baseEnd_2941468 := by
    simpa [prefixWord, tailWord_2941468, baseEnd_2941468] using wordTrace_append hprefix tailTrace_2941468
  have hstable : (prefixWord ++ tailWord_2941468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941468).length < 2 ^ (prefixWord ++ tailWord_2941468).sum := by decide
  have hdescent : baseEnd_2941468 < baseStart_2941468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941475 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 1, 4]
def baseStart_2941475 : Nat := 118140960795 + 2941475 * 2 ^ 59
def prefixEnd_2941475 : Nat := 4983230072969 + 3 ^ 40 * 2941475 * 2
def baseEnd_2941475 : Nat := 503463502727994733078303

theorem tailTrace_2941475 : CollatzResearch.WordTrace tailWord_2941475 prefixEnd_2941475 503463502727994733078303 := by
  unfold tailWord_2941475
  simp only [CollatzResearch.WordTrace]
  refine ⟨107284407018545913779873879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71522938012363942519915919 107284407018545913779873879)
  ·
    refine ⟨160926610527818870669810819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107284407018545913779873879 160926610527818870669810819)
    ·
      refine ⟨241389915791728306004716229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160926610527818870669810819 241389915791728306004716229)
      ·
        refine ⟨45260609210949057375884293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241389915791728306004716229 45260609210949057375884293)
        ·
          refine ⟨8486364227052948257978305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45260609210949057375884293 8486364227052948257978305)
          ·
            refine ⟨6364773170289711193483729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8486364227052948257978305 6364773170289711193483729)
            ·
              refine ⟨4773579877717283395112797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364773170289711193483729 4773579877717283395112797)
              ·
                refine ⟨1790092454143981273167299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4773579877717283395112797 1790092454143981273167299)
                ·
                  refine ⟨2685138681215971909750949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790092454143981273167299 2685138681215971909750949)
                  ·
                    refine ⟨503463502727994733078303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2685138681215971909750949 503463502727994733078303)
                    ·
                      rfl

theorem cell23_2941475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 4].length) (baseStart_2941475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941475 prefixEnd_2941475 := by exact prefixLift 2941475
  have htrace : WordTrace (prefixWord ++ tailWord_2941475) baseStart_2941475 baseEnd_2941475 := by
    simpa [prefixWord, tailWord_2941475, baseEnd_2941475] using wordTrace_append hprefix tailTrace_2941475
  have hstable : (prefixWord ++ tailWord_2941475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941475).length < 2 ^ (prefixWord ++ tailWord_2941475).sum := by decide
  have hdescent : baseEnd_2941475 < baseStart_2941475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941492 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2941492 : Nat := 118140960795 + 2941492 * 2 ^ 59
def prefixEnd_2941492 : Nat := 4983230072969 + 3 ^ 40 * 2941492 * 2
def baseEnd_2941492 : Nat := 503466412451703544240777

theorem tailTrace_2941492 : CollatzResearch.WordTrace tailWord_2941492 prefixEnd_2941492 503466412451703544240777 := by
  unfold tailWord_2941492
  simp only [CollatzResearch.WordTrace]
  refine ⟨53642513529742162841621365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71523351372989550455495153 53642513529742162841621365)
  ·
    refine ⟨5028985643413327766402003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53642513529742162841621365 5028985643413327766402003)
    ·
      refine ⟨7543478465119991649603005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028985643413327766402003 7543478465119991649603005)
      ·
        refine ⟨2828804424419996868601127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7543478465119991649603005 2828804424419996868601127)
        ·
          refine ⟨4243206636629995302901691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828804424419996868601127 4243206636629995302901691)
          ·
            refine ⟨6364809954944992954352537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243206636629995302901691 6364809954944992954352537)
            ·
              refine ⟨4773607466208744715764403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364809954944992954352537 4773607466208744715764403)
              ·
                refine ⟨7160411199313117073646605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773607466208744715764403 7160411199313117073646605)
                ·
                  refine ⟨2685154199742418902617477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7160411199313117073646605 2685154199742418902617477)
                  ·
                    refine ⟨503466412451703544240777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2685154199742418902617477 503466412451703544240777)
                    ·
                      rfl

theorem cell23_2941492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2941492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941492 prefixEnd_2941492 := by exact prefixLift 2941492
  have htrace : WordTrace (prefixWord ++ tailWord_2941492) baseStart_2941492 baseEnd_2941492 := by
    simpa [prefixWord, tailWord_2941492, baseEnd_2941492] using wordTrace_append hprefix tailTrace_2941492
  have hstable : (prefixWord ++ tailWord_2941492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941492).length < 2 ^ (prefixWord ++ tailWord_2941492).sum := by decide
  have hdescent : baseEnd_2941492 < baseStart_2941492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941498 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_2941498 : Nat := 118140960795 + 2941498 * 2 ^ 59
def prefixEnd_2941498 : Nat := 4983230072969 + 3 ^ 40 * 2941498 * 2
def baseEnd_2941498 : Nat := 1510402318239037609247303

theorem tailTrace_2941498 : CollatzResearch.WordTrace tailWord_2941498 prefixEnd_2941498 1510402318239037609247303 := by
  unfold tailWord_2941498
  simp only [CollatzResearch.WordTrace]
  refine ⟨26821311474365647176990287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71523497264975059138640765 26821311474365647176990287)
  ·
    refine ⟨40231967211548470765485431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26821311474365647176990287 40231967211548470765485431)
    ·
      refine ⟨60347950817322706148228147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40231967211548470765485431 60347950817322706148228147)
      ·
        refine ⟨90521926225984059222342221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60347950817322706148228147 90521926225984059222342221)
        ·
          refine ⟨33945722334744022208378333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90521926225984059222342221 33945722334744022208378333)
          ·
            refine ⟨12729645875529008328141875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33945722334744022208378333 12729645875529008328141875)
            ·
              refine ⟨19094468813293512492212813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12729645875529008328141875 19094468813293512492212813)
              ·
                refine ⟨7160425804985067184579805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19094468813293512492212813 7160425804985067184579805)
                ·
                  refine ⟨2685159676869400194217427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7160425804985067184579805 2685159676869400194217427)
                  ·
                    refine ⟨4027739515304100291326141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2685159676869400194217427 4027739515304100291326141)
                    ·
                      refine ⟨1510402318239037609247303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4027739515304100291326141 1510402318239037609247303)
                      ·
                        rfl

theorem cell23_2941498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_2941498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941498 prefixEnd_2941498 := by exact prefixLift 2941498
  have htrace : WordTrace (prefixWord ++ tailWord_2941498) baseStart_2941498 baseEnd_2941498 := by
    simpa [prefixWord, tailWord_2941498, baseEnd_2941498] using wordTrace_append hprefix tailTrace_2941498
  have hstable : (prefixWord ++ tailWord_2941498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941498).length < 2 ^ (prefixWord ++ tailWord_2941498).sum := by decide
  have hdescent : baseEnd_2941498 < baseStart_2941498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941549 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_2941549 : Nat := 118140960795 + 2941549 * 2 ^ 59
def prefixEnd_2941549 : Nat := 4983230072969 + 3 ^ 40 * 2941549 * 2
def baseEnd_2941549 : Nat := 1510428505752416909709569

theorem tailTrace_2941549 : CollatzResearch.WordTrace tailWord_2941549 prefixEnd_2941549 1510428505752416909709569 := by
  unfold tailWord_2941549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107287106020277824418067701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71524737346851882945378467 107287106020277824418067701)
  ·
    refine ⟨10058166189401046039193847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107287106020277824418067701 10058166189401046039193847)
    ·
      refine ⟨15087249284101569058790771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10058166189401046039193847 15087249284101569058790771)
      ·
        refine ⟨22630873926152353588186157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15087249284101569058790771 22630873926152353588186157)
        ·
          refine ⟨8486577722307132595569809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22630873926152353588186157 8486577722307132595569809)
          ·
            refine ⟨6364933291730349446677357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8486577722307132595569809 6364933291730349446677357)
            ·
              refine ⟨2386849984398881042504009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6364933291730349446677357 2386849984398881042504009)
              ·
                refine ⟨1790137488299160781878007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386849984398881042504009 1790137488299160781878007)
                ·
                  refine ⟨2685206232448741172817011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790137488299160781878007 2685206232448741172817011)
                  ·
                    refine ⟨4027809348673111759225517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2685206232448741172817011 4027809348673111759225517)
                    ·
                      refine ⟨1510428505752416909709569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4027809348673111759225517 1510428505752416909709569)
                      ·
                        rfl

theorem cell23_2941549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_2941549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941549 prefixEnd_2941549 := by exact prefixLift 2941549
  have htrace : WordTrace (prefixWord ++ tailWord_2941549) baseStart_2941549 baseEnd_2941549 := by
    simpa [prefixWord, tailWord_2941549, baseEnd_2941549] using wordTrace_append hprefix tailTrace_2941549
  have hstable : (prefixWord ++ tailWord_2941549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941549).length < 2 ^ (prefixWord ++ tailWord_2941549).sum := by decide
  have hdescent : baseEnd_2941549 < baseStart_2941549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941561 : List Nat := [1, 2, 1, 3, 3, 3, 2, 8]
def baseStart_2941561 : Nat := 118140960795 + 2941561 * 2 ^ 59
def prefixEnd_2941561 : Nat := 4983230072969 + 3 ^ 40 * 2941561 * 2
def baseEnd_2941561 : Nat := 55942024722972994917019

theorem tailTrace_2941561 : CollatzResearch.WordTrace tailWord_2941561 prefixEnd_2941561 55942024722972994917019 := by
  unfold tailWord_2941561
  simp only [CollatzResearch.WordTrace]
  refine ⟨107287543696234350467504537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71525029130822900311669691 107287543696234350467504537)
  ·
    refine ⟨80465657772175762850628403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107287543696234350467504537 80465657772175762850628403)
    ·
      refine ⟨120698486658263644275942605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80465657772175762850628403 120698486658263644275942605)
      ·
        refine ⟨45261932496848866603478477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120698486658263644275942605 45261932496848866603478477)
        ·
          refine ⟨16973224686318324976304429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45261932496848866603478477 16973224686318324976304429)
          ·
            refine ⟨6364959257369371866114161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16973224686318324976304429 6364959257369371866114161)
            ·
              refine ⟨4773719443027028899585621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364959257369371866114161 4773719443027028899585621)
              ·
                refine ⟨55942024722972994917019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4773719443027028899585621 55942024722972994917019)
                ·
                  rfl

theorem cell23_2941561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 8].length) (baseStart_2941561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941561 prefixEnd_2941561 := by exact prefixLift 2941561
  have htrace : WordTrace (prefixWord ++ tailWord_2941561) baseStart_2941561 baseEnd_2941561 := by
    simpa [prefixWord, tailWord_2941561, baseEnd_2941561] using wordTrace_append hprefix tailTrace_2941561
  have hstable : (prefixWord ++ tailWord_2941561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941561).length < 2 ^ (prefixWord ++ tailWord_2941561).sum := by decide
  have hdescent : baseEnd_2941561 < baseStart_2941561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941565 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2941565 : Nat := 118140960795 + 2941565 * 2 ^ 59
def prefixEnd_2941565 : Nat := 4983230072969 + 3 ^ 40 * 2941565 * 2
def baseEnd_2941565 : Nat := 503478907147629615703165

theorem tailTrace_2941565 : CollatzResearch.WordTrace tailWord_2941565 prefixEnd_2941565 503478907147629615703165 := by
  unfold tailWord_2941565
  simp only [CollatzResearch.WordTrace]
  refine ⟨107287689588219859150650149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71525126392146572767100099 107287689588219859150650149)
  ·
    refine ⟨20116441797791223590746903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107287689588219859150650149 20116441797791223590746903)
    ·
      refine ⟨30174662696686835386120355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20116441797791223590746903 30174662696686835386120355)
      ·
        refine ⟨45261994045030253079180533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30174662696686835386120355 45261994045030253079180533)
        ·
          refine ⟨4243311941721586226173175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45261994045030253079180533 4243311941721586226173175)
          ·
            refine ⟨6364967912582379339259763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243311941721586226173175 6364967912582379339259763)
            ·
              refine ⟨9547451868873569008889645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364967912582379339259763 9547451868873569008889645)
              ·
                refine ⟨3580294450827588378333617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9547451868873569008889645 3580294450827588378333617)
                ·
                  refine ⟨2685220838120691283750213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580294450827588378333617 2685220838120691283750213)
                  ·
                    refine ⟨503478907147629615703165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2685220838120691283750213 503478907147629615703165)
                    ·
                      rfl

theorem cell23_2941565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2941565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941565 prefixEnd_2941565 := by exact prefixLift 2941565
  have htrace : WordTrace (prefixWord ++ tailWord_2941565) baseStart_2941565 baseEnd_2941565 := by
    simpa [prefixWord, tailWord_2941565, baseEnd_2941565] using wordTrace_append hprefix tailTrace_2941565
  have hstable : (prefixWord ++ tailWord_2941565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941565).length < 2 ^ (prefixWord ++ tailWord_2941565).sum := by decide
  have hdescent : baseEnd_2941565 < baseStart_2941565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941668 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 7]
def baseStart_2941668 : Nat := 118140960795 + 2941668 * 2 ^ 59
def prefixEnd_2941668 : Nat := 4983230072969 + 3 ^ 40 * 2941668 * 2
def baseEnd_2941668 : Nat := 167832178883366882680169

theorem tailTrace_2941668 : CollatzResearch.WordTrace tailWord_2941668 prefixEnd_2941668 167832178883366882680169 := by
  unfold tailWord_2941668
  simp only [CollatzResearch.WordTrace]
  refine ⟨53645723153423353870824829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71527630871231138494433105 53645723153423353870824829)
  ·
    refine ⟨20117146182533757701559311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53645723153423353870824829 20117146182533757701559311)
    ·
      refine ⟨30175719273800636552338967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20117146182533757701559311 30175719273800636552338967)
      ·
        refine ⟨45263578910700954828508451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30175719273800636552338967 45263578910700954828508451)
        ·
          refine ⟨67895368366051432242762677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45263578910700954828508451 67895368366051432242762677)
          ·
            refine ⟨6365190784317321772759001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67895368366051432242762677 6365190784317321772759001)
            ·
              refine ⟨4773893088237991329569251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6365190784317321772759001 4773893088237991329569251)
              ·
                refine ⟨7160839632356986994353877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773893088237991329569251 7160839632356986994353877)
                ·
                  refine ⟨167832178883366882680169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7160839632356986994353877 167832178883366882680169)
                  ·
                    rfl

theorem cell23_2941668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_2941668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941668 prefixEnd_2941668 := by exact prefixLift 2941668
  have htrace : WordTrace (prefixWord ++ tailWord_2941668) baseStart_2941668 baseEnd_2941668 := by
    simpa [prefixWord, tailWord_2941668, baseEnd_2941668] using wordTrace_append hprefix tailTrace_2941668
  have hstable : (prefixWord ++ tailWord_2941668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941668).length < 2 ^ (prefixWord ++ tailWord_2941668).sum := by decide
  have hdescent : baseEnd_2941668 < baseStart_2941668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941679 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 2, 2, 2]
def baseStart_2941679 : Nat := 118140960795 + 2941679 * 2 ^ 59
def prefixEnd_2941679 : Nat := 4983230072969 + 3 ^ 40 * 2941679 * 2
def baseEnd_2941679 : Nat := 1510495258237501401083971

theorem tailTrace_2941679 : CollatzResearch.WordTrace tailWord_2941679 prefixEnd_2941679 1510495258237501401083971 := by
  unfold tailWord_2941679
  simp only [CollatzResearch.WordTrace]
  refine ⟨107291847509806856620300091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71527898339871237746866727 107291847509806856620300091)
  ·
    refine ⟨160937771264710284930450137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107291847509806856620300091 160937771264710284930450137)
    ·
      refine ⟨120703328448532713697837603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160937771264710284930450137 120703328448532713697837603)
      ·
        refine ⟨181054992672799070546756405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120703328448532713697837603 181054992672799070546756405)
        ·
          refine ⟨16973905563074912863758413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181054992672799070546756405 16973905563074912863758413)
          ·
            refine ⟨6365214586153092323909405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16973905563074912863758413 6365214586153092323909405)
            ·
              refine ⟨2386955469807409621466027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6365214586153092323909405 2386955469807409621466027)
              ·
                refine ⟨3580433204711114432199041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386955469807409621466027 3580433204711114432199041)
                ·
                  refine ⟨2685324903533335824149281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580433204711114432199041 2685324903533335824149281)
                  ·
                    refine ⟨2013993677650001868111961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2685324903533335824149281 2013993677650001868111961)
                    ·
                      refine ⟨1510495258237501401083971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2013993677650001868111961 1510495258237501401083971)
                      ·
                        rfl

theorem cell23_2941679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 2, 2].length) (baseStart_2941679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941679 prefixEnd_2941679 := by exact prefixLift 2941679
  have htrace : WordTrace (prefixWord ++ tailWord_2941679) baseStart_2941679 baseEnd_2941679 := by
    simpa [prefixWord, tailWord_2941679, baseEnd_2941679] using wordTrace_append hprefix tailTrace_2941679
  have hstable : (prefixWord ++ tailWord_2941679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941679).length < 2 ^ (prefixWord ++ tailWord_2941679).sum := by decide
  have hdescent : baseEnd_2941679 < baseStart_2941679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941681 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_2941681 : Nat := 118140960795 + 2941681 * 2 ^ 59
def prefixEnd_2941681 : Nat := 4983230072969 + 3 ^ 40 * 2941681 * 2
def baseEnd_2941681 : Nat := 503498761732936797752987

theorem tailTrace_2941681 : CollatzResearch.WordTrace tailWord_2941681 prefixEnd_2941681 503498761732936797752987 := by
  unfold tailWord_2941681
  simp only [CollatzResearch.WordTrace]
  refine ⟨107291920455799610961872897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71527946970533073974581931 107291920455799610961872897)
  ·
    refine ⟨80468940341849708221404673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107291920455799610961872897 80468940341849708221404673)
    ·
      refine ⟨60351705256387281166053505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80468940341849708221404673 60351705256387281166053505)
      ·
        refine ⟨45263778942290460874540129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60351705256387281166053505 45263778942290460874540129)
        ·
          refine ⟨33947834206717845655905097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45263778942290460874540129 33947834206717845655905097)
          ·
            refine ⟨25460875655038384241928823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33947834206717845655905097 25460875655038384241928823)
            ·
              refine ⟨38191313482557576362893235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25460875655038384241928823 38191313482557576362893235)
              ·
                refine ⟨57286970223836364544339853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38191313482557576362893235 57286970223836364544339853)
                ·
                  refine ⟨21482613833938636704127445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57286970223836364544339853 21482613833938636704127445)
                  ·
                    refine ⟨503498761732936797752987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21482613833938636704127445 503498761732936797752987)
                    ·
                      rfl

theorem cell23_2941681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_2941681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941681 prefixEnd_2941681 := by exact prefixLift 2941681
  have htrace : WordTrace (prefixWord ++ tailWord_2941681) baseStart_2941681 baseEnd_2941681 := by
    simpa [prefixWord, tailWord_2941681, baseEnd_2941681] using wordTrace_append hprefix tailTrace_2941681
  have hstable : (prefixWord ++ tailWord_2941681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941681).length < 2 ^ (prefixWord ++ tailWord_2941681).sum := by decide
  have hdescent : baseEnd_2941681 < baseStart_2941681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941721 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2941721 : Nat := 118140960795 + 2941721 * 2 ^ 59
def prefixEnd_2941721 : Nat := 4983230072969 + 3 ^ 40 * 2941721 * 2
def baseEnd_2941721 : Nat := 1510516824424990236758777

theorem tailTrace_2941721 : CollatzResearch.WordTrace tailWord_2941721 prefixEnd_2941721 1510516824424990236758777 := by
  unfold tailWord_2941721
  simp only [CollatzResearch.WordTrace]
  refine ⟨107293379375654697793329017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71528919583769798528886011 107293379375654697793329017)
  ·
    refine ⟨80470034531741023344996763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107293379375654697793329017 80470034531741023344996763)
    ·
      refine ⟨120705051797611535017495145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80470034531741023344996763 120705051797611535017495145)
      ·
        refine ⟨90528788848208651263121359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120705051797611535017495145 90528788848208651263121359)
        ·
          refine ⟨135793183272312976894682039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90528788848208651263121359 135793183272312976894682039)
          ·
            refine ⟨203689774908469465342023059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135793183272312976894682039 203689774908469465342023059)
            ·
              refine ⟨305534662362704198013034589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203689774908469465342023059 305534662362704198013034589)
              ·
                refine ⟨114575498386014074254887971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305534662362704198013034589 114575498386014074254887971)
                ·
                  refine ⟨171863247579021111382331957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114575498386014074254887971 171863247579021111382331957)
                  ·
                    refine ⟨16112179460533229192093621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171863247579021111382331957 16112179460533229192093621)
                    ·
                      refine ⟨1510516824424990236758777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16112179460533229192093621 1510516824424990236758777)
                      ·
                        rfl

theorem cell23_2941721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2941721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941721 prefixEnd_2941721 := by exact prefixLift 2941721
  have htrace : WordTrace (prefixWord ++ tailWord_2941721) baseStart_2941721 baseEnd_2941721 := by
    simpa [prefixWord, tailWord_2941721, baseEnd_2941721] using wordTrace_append hprefix tailTrace_2941721
  have hstable : (prefixWord ++ tailWord_2941721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941721).length < 2 ^ (prefixWord ++ tailWord_2941721).sum := by decide
  have hdescent : baseEnd_2941721 < baseStart_2941721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941778 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2941778 : Nat := 118140960795 + 2941778 * 2 ^ 59
def prefixEnd_2941778 : Nat := 4983230072969 + 3 ^ 40 * 2941778 * 2
def baseEnd_2941778 : Nat := 1510546092822296513746015

theorem tailTrace_2941778 : CollatzResearch.WordTrace tailWord_2941778 prefixEnd_2941778 1510546092822296513746015 := by
  unfold tailWord_2941778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26823864584112049132038497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71530305557632131018769325 26823864584112049132038497)
  ·
    refine ⟨20117898438084036849028873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26823864584112049132038497 20117898438084036849028873)
    ·
      refine ⟨15088423828563027636771655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20117898438084036849028873 15088423828563027636771655)
      ·
        refine ⟨22632635742844541455157483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15088423828563027636771655 22632635742844541455157483)
        ·
          refine ⟨33948953614266812182736225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22632635742844541455157483 33948953614266812182736225)
          ·
            refine ⟨25461715210700109137052169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33948953614266812182736225 25461715210700109137052169)
            ·
              refine ⟨19096286408025081852789127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25461715210700109137052169 19096286408025081852789127)
              ·
                refine ⟨28644429612037622779183691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19096286408025081852789127 28644429612037622779183691)
                ·
                  refine ⟨42966644418056434168775537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28644429612037622779183691 42966644418056434168775537)
                  ·
                    refine ⟨32224983313542325626581653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42966644418056434168775537 32224983313542325626581653)
                    ·
                      refine ⟨1510546092822296513746015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32224983313542325626581653 1510546092822296513746015)
                      ·
                        rfl

theorem cell23_2941778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2941778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941778 prefixEnd_2941778 := by exact prefixLift 2941778
  have htrace : WordTrace (prefixWord ++ tailWord_2941778) baseStart_2941778 baseEnd_2941778 := by
    simpa [prefixWord, tailWord_2941778, baseEnd_2941778] using wordTrace_append hprefix tailTrace_2941778
  have hstable : (prefixWord ++ tailWord_2941778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941778).length < 2 ^ (prefixWord ++ tailWord_2941778).sum := by decide
  have hdescent : baseEnd_2941778 < baseStart_2941778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941805 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2941805 : Nat := 118140960795 + 2941805 * 2 ^ 59
def prefixEnd_2941805 : Nat := 4983230072969 + 3 ^ 40 * 2941805 * 2
def baseEnd_2941805 : Nat := 503519985599989302702797

theorem tailTrace_2941805 : CollatzResearch.WordTrace tailWord_2941805 prefixEnd_2941805 503519985599989302702797 := by
  unfold tailWord_2941805
  simp only [CollatzResearch.WordTrace]
  refine ⟨107296443107350380139386869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71530962071566920092924579 107296443107350380139386869)
  ·
    refine ⟨10059041541314098138067519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107296443107350380139386869 10059041541314098138067519)
    ·
      refine ⟨15088562311971147207101279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10059041541314098138067519 15088562311971147207101279)
      ·
        refine ⟨22632843467956720810651919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15088562311971147207101279 22632843467956720810651919)
        ·
          refine ⟨33949265201935081215977879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22632843467956720810651919 33949265201935081215977879)
          ·
            refine ⟨50923897802902621823966819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33949265201935081215977879 50923897802902621823966819)
            ·
              refine ⟨76385846704353932735950229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50923897802902621823966819 76385846704353932735950229)
              ·
                refine ⟨3580586564266590596997667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76385846704353932735950229 3580586564266590596997667)
                ·
                  refine ⟨5370879846399885895496501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580586564266590596997667 5370879846399885895496501)
                  ·
                    refine ⟨503519985599989302702797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5370879846399885895496501 503519985599989302702797)
                    ·
                      rfl

theorem cell23_2941805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2941805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941805 prefixEnd_2941805 := by exact prefixLift 2941805
  have htrace : WordTrace (prefixWord ++ tailWord_2941805) baseStart_2941805 baseEnd_2941805 := by
    simpa [prefixWord, tailWord_2941805, baseEnd_2941805] using wordTrace_append hprefix tailTrace_2941805
  have hstable : (prefixWord ++ tailWord_2941805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941805).length < 2 ^ (prefixWord ++ tailWord_2941805).sum := by decide
  have hdescent : baseEnd_2941805 < baseStart_2941805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941806 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2941806 : Nat := 118140960795 + 2941806 * 2 ^ 59
def prefixEnd_2941806 : Nat := 4983230072969 + 3 ^ 40 * 2941806 * 2
def baseEnd_2941806 : Nat := 1510560470280622404195887

theorem tailTrace_2941806 : CollatzResearch.WordTrace tailWord_2941806 prefixEnd_2941806 1510560470280622404195887 := by
  unfold tailWord_2941806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412059947543344663771659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71530986386897838206782181 13412059947543344663771659)
  ·
    refine ⟨20118089921315016995657489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13412059947543344663771659 20118089921315016995657489)
    ·
      refine ⟨15088567440986262746743117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20118089921315016995657489 15088567440986262746743117)
      ·
        refine ⟨5658212790369848530028669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15088567440986262746743117 5658212790369848530028669)
        ·
          refine ⟨2121829796388693198760751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5658212790369848530028669 2121829796388693198760751)
          ·
            refine ⟨3182744694583039798141127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121829796388693198760751 3182744694583039798141127)
            ·
              refine ⟨4774117041874559697211691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182744694583039798141127 4774117041874559697211691)
              ·
                refine ⟨7161175562811839545817537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4774117041874559697211691 7161175562811839545817537)
                ·
                  refine ⟨5370881672108879659363153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161175562811839545817537 5370881672108879659363153)
                  ·
                    refine ⟨4028161254081659744522365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5370881672108879659363153 4028161254081659744522365)
                    ·
                      refine ⟨1510560470280622404195887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4028161254081659744522365 1510560470280622404195887)
                      ·
                        rfl

theorem cell23_2941806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2941806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941806 prefixEnd_2941806 := by exact prefixLift 2941806
  have htrace : WordTrace (prefixWord ++ tailWord_2941806) baseStart_2941806 baseEnd_2941806 := by
    simpa [prefixWord, tailWord_2941806, baseEnd_2941806] using wordTrace_append hprefix tailTrace_2941806
  have hstable : (prefixWord ++ tailWord_2941806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941806).length < 2 ^ (prefixWord ++ tailWord_2941806).sum := by decide
  have hdescent : baseEnd_2941806 < baseStart_2941806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941826 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_2941826 : Nat := 118140960795 + 2941826 * 2 ^ 59
def prefixEnd_2941826 : Nat := 4983230072969 + 3 ^ 40 * 2941826 * 2
def baseEnd_2941826 : Nat := 167841193321523591771755

theorem tailTrace_2941826 : CollatzResearch.WordTrace tailWord_2941826 prefixEnd_2941826 167841193321523591771755 := by
  unfold tailWord_2941826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26824302260068575181475333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71531472693516200483934221 26824302260068575181475333)
  ·
    refine ⟨5029556673762857846526625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26824302260068575181475333 5029556673762857846526625)
    ·
      refine ⟨3772167505322143384894969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029556673762857846526625 3772167505322143384894969)
      ·
        refine ⟨2829125628991607538671227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772167505322143384894969 2829125628991607538671227)
        ·
          refine ⟨4243688443487411308006841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829125628991607538671227 4243688443487411308006841)
          ·
            refine ⟨3182766332615558481005131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243688443487411308006841 3182766332615558481005131)
            ·
              refine ⟨4774149498923337721507697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182766332615558481005131 4774149498923337721507697)
              ·
                refine ⟨3580612124192503291130773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4774149498923337721507697 3580612124192503291130773)
                ·
                  refine ⟨167841193321523591771755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3580612124192503291130773 167841193321523591771755)
                  ·
                    rfl

theorem cell23_2941826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_2941826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941826 prefixEnd_2941826 := by exact prefixLift 2941826
  have htrace : WordTrace (prefixWord ++ tailWord_2941826) baseStart_2941826 baseEnd_2941826 := by
    simpa [prefixWord, tailWord_2941826, baseEnd_2941826] using wordTrace_append hprefix tailTrace_2941826
  have hstable : (prefixWord ++ tailWord_2941826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941826).length < 2 ^ (prefixWord ++ tailWord_2941826).sum := by decide
  have hdescent : baseEnd_2941826 < baseStart_2941826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941845 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2941845 : Nat := 118140960795 + 2941845 * 2 ^ 59
def prefixEnd_2941845 : Nat := 4983230072969 + 3 ^ 40 * 2941845 * 2
def baseEnd_2941845 : Nat := 1510580496026147751608207

theorem tailTrace_2941845 : CollatzResearch.WordTrace tailWord_2941845 prefixEnd_2941845 1510580496026147751608207 := by
  unfold tailWord_2941845
  simp only [CollatzResearch.WordTrace]
  refine ⟨107297902027205466970842989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71531934684803644647228659 107297902027205466970842989)
  ·
    refine ⟨40236713260202050114066121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107297902027205466970842989 40236713260202050114066121)
    ·
      refine ⟨30177534945151537585549591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40236713260202050114066121 30177534945151537585549591)
      ·
        refine ⟨45266302417727306378324387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30177534945151537585549591 45266302417727306378324387)
        ·
          refine ⟨67899453626590959567486581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45266302417727306378324387 67899453626590959567486581)
          ·
            refine ⟨6365573777492902459451867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67899453626590959567486581 6365573777492902459451867)
            ·
              refine ⟨9548360666239353689177801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365573777492902459451867 9548360666239353689177801)
              ·
                refine ⟨7161270499679515266883351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9548360666239353689177801 7161270499679515266883351)
                ·
                  refine ⟨10741905749519272900325027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7161270499679515266883351 10741905749519272900325027)
                  ·
                    refine ⟨16112858624278909350487541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10741905749519272900325027 16112858624278909350487541)
                    ·
                      refine ⟨1510580496026147751608207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16112858624278909350487541 1510580496026147751608207)
                      ·
                        rfl

theorem cell23_2941845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2941845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941845 prefixEnd_2941845 := by exact prefixLift 2941845
  have htrace : WordTrace (prefixWord ++ tailWord_2941845) baseStart_2941845 baseEnd_2941845 := by
    simpa [prefixWord, tailWord_2941845, baseEnd_2941845] using wordTrace_append hprefix tailTrace_2941845
  have hstable : (prefixWord ++ tailWord_2941845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941845).length < 2 ^ (prefixWord ++ tailWord_2941845).sum := by decide
  have hdescent : baseEnd_2941845 < baseStart_2941845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941846 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2941846 : Nat := 118140960795 + 2941846 * 2 ^ 59
def prefixEnd_2941846 : Nat := 4983230072969 + 3 ^ 40 * 2941846 * 2
def baseEnd_2941846 : Nat := 1510581009506802247695703

theorem tailTrace_2941846 : CollatzResearch.WordTrace tailWord_2941846 prefixEnd_2941846 1510581009506802247695703 := by
  unfold tailWord_2941846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706121156262615258851837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71531959000134562761086261 6706121156262615258851837)
  ·
    refine ⟨2514795433598480722069439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6706121156262615258851837 2514795433598480722069439)
    ·
      refine ⟨3772193150397721083104159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514795433598480722069439 3772193150397721083104159)
      ·
        refine ⟨5658289725596581624656239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772193150397721083104159 5658289725596581624656239)
        ·
          refine ⟨8487434588394872436984359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658289725596581624656239 8487434588394872436984359)
          ·
            refine ⟨12731151882592308655476539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487434588394872436984359 12731151882592308655476539)
            ·
              refine ⟨19096727823888462983214809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12731151882592308655476539 19096727823888462983214809)
              ·
                refine ⟨14322545867916347237411107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19096727823888462983214809 14322545867916347237411107)
                ·
                  refine ⟨21483818801874520856116661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14322545867916347237411107 21483818801874520856116661)
                  ·
                    refine ⟨2014108012675736330260937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21483818801874520856116661 2014108012675736330260937)
                    ·
                      refine ⟨1510581009506802247695703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014108012675736330260937 1510581009506802247695703)
                      ·
                        rfl

theorem cell23_2941846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2941846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941846 prefixEnd_2941846 := by exact prefixLift 2941846
  have htrace : WordTrace (prefixWord ++ tailWord_2941846) baseStart_2941846 baseEnd_2941846 := by
    simpa [prefixWord, tailWord_2941846, baseEnd_2941846] using wordTrace_append hprefix tailTrace_2941846
  have hstable : (prefixWord ++ tailWord_2941846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941846).length < 2 ^ (prefixWord ++ tailWord_2941846).sum := by decide
  have hdescent : baseEnd_2941846 < baseStart_2941846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941855 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2941855 : Nat := 118140960795 + 2941855 * 2 ^ 59
def prefixEnd_2941855 : Nat := 4983230072969 + 3 ^ 40 * 2941855 * 2
def baseEnd_2941855 : Nat := 1510585630832692712483161

theorem tailTrace_2941855 : CollatzResearch.WordTrace tailWord_2941855 prefixEnd_2941855 1510585630832692712483161 := by
  unfold tailWord_2941855
  simp only [CollatzResearch.WordTrace]
  refine ⟨107298266757169238678707019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71532177838112825785804679 107298266757169238678707019)
  ·
    refine ⟨160947400135753858018060529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107298266757169238678707019 160947400135753858018060529)
    ·
      refine ⟨120710550101815393513545397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160947400135753858018060529 120710550101815393513545397)
      ·
        refine ⟨11316614072045193141894881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120710550101815393513545397 11316614072045193141894881)
        ·
          refine ⟨8487460554033894856421161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11316614072045193141894881 8487460554033894856421161)
          ·
            refine ⟨6365595415525421142315871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487460554033894856421161 6365595415525421142315871)
            ·
              refine ⟨9548393123288131713473807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365595415525421142315871 9548393123288131713473807)
              ·
                refine ⟨14322589684932197570210711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548393123288131713473807 14322589684932197570210711)
                ·
                  refine ⟨21483884527398296355316067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14322589684932197570210711 21483884527398296355316067)
                  ·
                    refine ⟨32225826791097444532974101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21483884527398296355316067 32225826791097444532974101)
                    ·
                      refine ⟨1510585630832692712483161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32225826791097444532974101 1510585630832692712483161)
                      ·
                        rfl

theorem cell23_2941855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2941855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941855 prefixEnd_2941855 := by exact prefixLift 2941855
  have htrace : WordTrace (prefixWord ++ tailWord_2941855) baseStart_2941855 baseEnd_2941855 := by
    simpa [prefixWord, tailWord_2941855, baseEnd_2941855] using wordTrace_append hprefix tailTrace_2941855
  have hstable : (prefixWord ++ tailWord_2941855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941855).length < 2 ^ (prefixWord ++ tailWord_2941855).sum := by decide
  have hdescent : baseEnd_2941855 < baseStart_2941855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941919 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 3, 3, 2]
def baseStart_2941919 : Nat := 118140960795 + 2941919 * 2 ^ 59
def prefixEnd_2941919 : Nat := 4983230072969 + 3 ^ 40 * 2941919 * 2
def baseEnd_2941919 : Nat := 1510618493594580462082867

theorem tailTrace_2941919 : CollatzResearch.WordTrace tailWord_2941919 prefixEnd_2941919 1510618493594580462082867 := by
  unfold tailWord_2941919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107300601028937377609036811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71533734019291585072691207 107300601028937377609036811)
  ·
    refine ⟨160950901543406066413555217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107300601028937377609036811 160950901543406066413555217)
    ·
      refine ⟨120713176157554549810166413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160950901543406066413555217 120713176157554549810166413)
      ·
        refine ⟨45267441059082956178812405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120713176157554549810166413 45267441059082956178812405)
        ·
          refine ⟨4243822599289027141763663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45267441059082956178812405 4243822599289027141763663)
          ·
            refine ⟨6365733898933540712645495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243822599289027141763663 6365733898933540712645495)
            ·
              refine ⟨9548600848400311068968243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365733898933540712645495 9548600848400311068968243)
              ·
                refine ⟨14322901272600466603452365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548600848400311068968243 14322901272600466603452365)
                ·
                  refine ⟨5371087977225174976294637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14322901272600466603452365 5371087977225174976294637)
                  ·
                    refine ⟨2014157991459440616110489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5371087977225174976294637 2014157991459440616110489)
                    ·
                      refine ⟨1510618493594580462082867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014157991459440616110489 1510618493594580462082867)
                      ·
                        rfl

theorem cell23_2941919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_2941919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941919 prefixEnd_2941919 := by exact prefixLift 2941919
  have htrace : WordTrace (prefixWord ++ tailWord_2941919) baseStart_2941919 baseEnd_2941919 := by
    simpa [prefixWord, tailWord_2941919, baseEnd_2941919] using wordTrace_append hprefix tailTrace_2941919
  have hstable : (prefixWord ++ tailWord_2941919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941919).length < 2 ^ (prefixWord ++ tailWord_2941919).sum := by decide
  have hdescent : baseEnd_2941919 < baseStart_2941919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941935 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_2941935 : Nat := 118140960795 + 2941935 * 2 ^ 59
def prefixEnd_2941935 : Nat := 4983230072969 + 3 ^ 40 * 2941935 * 2
def baseEnd_2941935 : Nat := 1510626709285052399482793

theorem tailTrace_2941935 : CollatzResearch.WordTrace tailWord_2941935 prefixEnd_2941935 1510626709285052399482793 := by
  unfold tailWord_2941935
  simp only [CollatzResearch.WordTrace]
  refine ⟨107301184596879412341619259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71534123064586274894412839 107301184596879412341619259)
  ·
    refine ⟨160951776895319118512428889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107301184596879412341619259 160951776895319118512428889)
    ·
      refine ⟨120713832671489338884321667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160951776895319118512428889 120713832671489338884321667)
      ·
        refine ⟨181070749007234008326482501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120713832671489338884321667 181070749007234008326482501)
        ·
          refine ⟨33950765438856376561215469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181070749007234008326482501 33950765438856376561215469)
          ·
            refine ⟨12731537039571141210455801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33950765438856376561215469 12731537039571141210455801)
            ·
              refine ⟨9548652779678355907841851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12731537039571141210455801 9548652779678355907841851)
              ·
                refine ⟨14322979169517533861762777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548652779678355907841851 14322979169517533861762777)
                ·
                  refine ⟨10742234377138150396322083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14322979169517533861762777 10742234377138150396322083)
                  ·
                    refine ⟨16113351565707225594483125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10742234377138150396322083 16113351565707225594483125)
                    ·
                      refine ⟨1510626709285052399482793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16113351565707225594483125 1510626709285052399482793)
                      ·
                        rfl

theorem cell23_2941935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_2941935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941935 prefixEnd_2941935 := by exact prefixLift 2941935
  have htrace : WordTrace (prefixWord ++ tailWord_2941935) baseStart_2941935 baseEnd_2941935 := by
    simpa [prefixWord, tailWord_2941935, baseEnd_2941935] using wordTrace_append hprefix tailTrace_2941935
  have hstable : (prefixWord ++ tailWord_2941935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941935).length < 2 ^ (prefixWord ++ tailWord_2941935).sum := by decide
  have hdescent : baseEnd_2941935 < baseStart_2941935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941945 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2941945 : Nat := 118140960795 + 2941945 * 2 ^ 59
def prefixEnd_2941945 : Nat := 4983230072969 + 3 ^ 40 * 2941945 * 2
def baseEnd_2941945 : Nat := 1510631844091597360357747

theorem tailTrace_2941945 : CollatzResearch.WordTrace tailWord_2941945 prefixEnd_2941945 1510631844091597360357747 := by
  unfold tailWord_2941945
  simp only [CollatzResearch.WordTrace]
  refine ⟨107301549326843184049483289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71534366217895456032988859 107301549326843184049483289)
  ·
    refine ⟨80476161995132388037112467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107301549326843184049483289 80476161995132388037112467)
    ·
      refine ⟨120714242992698582055668701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80476161995132388037112467 120714242992698582055668701)
      ·
        refine ⟨45267841122261968270875763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120714242992698582055668701 45267841122261968270875763)
        ·
          refine ⟨67901761683392952406313645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45267841122261968270875763 67901761683392952406313645)
          ·
            refine ⟨25463160631272357152367617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67901761683392952406313645 25463160631272357152367617)
            ·
              refine ⟨19097370473454267864275713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25463160631272357152367617 19097370473454267864275713)
              ·
                refine ⟨14323027855090700898206785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19097370473454267864275713 14323027855090700898206785)
                ·
                  refine ⟨10742270891318025673655089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14323027855090700898206785 10742270891318025673655089)
                  ·
                    refine ⟨8056703168488519255241317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10742270891318025673655089 8056703168488519255241317)
                    ·
                      refine ⟨1510631844091597360357747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8056703168488519255241317 1510631844091597360357747)
                      ·
                        rfl

theorem cell23_2941945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2941945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941945 prefixEnd_2941945 := by exact prefixLift 2941945
  have htrace : WordTrace (prefixWord ++ tailWord_2941945) baseStart_2941945 baseEnd_2941945 := by
    simpa [prefixWord, tailWord_2941945, baseEnd_2941945] using wordTrace_append hprefix tailTrace_2941945
  have hstable : (prefixWord ++ tailWord_2941945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941945).length < 2 ^ (prefixWord ++ tailWord_2941945).sum := by decide
  have hdescent : baseEnd_2941945 < baseStart_2941945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941962 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2941962 : Nat := 118140960795 + 2941962 * 2 ^ 59
def prefixEnd_2941962 : Nat := 4983230072969 + 3 ^ 40 * 2941962 * 2
def baseEnd_2941962 : Nat := 1510640573262723793845169

theorem tailTrace_2941962 : CollatzResearch.WordTrace tailWord_2941962 prefixEnd_2941962 1510640573262723793845169 := by
  unfold tailWord_2941962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26825542341945398988213035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71534779578521063968568093 26825542341945398988213035)
  ·
    refine ⟨40238313512918098482319553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26825542341945398988213035 40238313512918098482319553)
    ·
      refine ⟨30178735134688573861739665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40238313512918098482319553 30178735134688573861739665)
      ·
        refine ⟨22634051351016430396304749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30178735134688573861739665 22634051351016430396304749)
        ·
          refine ⟨8487769256631161398614281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22634051351016430396304749 8487769256631161398614281)
          ·
            refine ⟨6365826942473371048960711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487769256631161398614281 6365826942473371048960711)
            ·
              refine ⟨9548740413710056573441067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365826942473371048960711 9548740413710056573441067)
              ·
                refine ⟨14323110620565084860161601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9548740413710056573441067 14323110620565084860161601)
                ·
                  refine ⟨10742332965423813645121201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14323110620565084860161601 10742332965423813645121201)
                  ·
                    refine ⟨8056749724067860233840901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10742332965423813645121201 8056749724067860233840901)
                    ·
                      refine ⟨1510640573262723793845169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8056749724067860233840901 1510640573262723793845169)
                      ·
                        rfl

theorem cell23_2941962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2941962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941962 prefixEnd_2941962 := by exact prefixLift 2941962
  have htrace : WordTrace (prefixWord ++ tailWord_2941962) baseStart_2941962 baseEnd_2941962 := by
    simpa [prefixWord, tailWord_2941962, baseEnd_2941962] using wordTrace_append hprefix tailTrace_2941962
  have hstable : (prefixWord ++ tailWord_2941962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941962).length < 2 ^ (prefixWord ++ tailWord_2941962).sum := by decide
  have hdescent : baseEnd_2941962 < baseStart_2941962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941966 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2941966 : Nat := 118140960795 + 2941966 * 2 ^ 59
def prefixEnd_2941966 : Nat := 4983230072969 + 3 ^ 40 * 2941966 * 2
def baseEnd_2941966 : Nat := 1510642627185341778195151

theorem tailTrace_2941966 : CollatzResearch.WordTrace tailWord_2941966 prefixEnd_2941966 1510642627185341778195151 := by
  unfold tailWord_2941966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412789407470888079499719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71534876839844736423998501 13412789407470888079499719)
  ·
    refine ⟨20119184111206332119249579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13412789407470888079499719 20119184111206332119249579)
    ·
      refine ⟨30178776166809498178874369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20119184111206332119249579 30178776166809498178874369)
      ·
        refine ⟨22634082125107123634155777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30178776166809498178874369 22634082125107123634155777)
        ·
          refine ⟨16975561593830342725616833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22634082125107123634155777 16975561593830342725616833)
          ·
            refine ⟨12731671195372757044212625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16975561593830342725616833 12731671195372757044212625)
            ·
              refine ⟨9548753396529567783159469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12731671195372757044212625 9548753396529567783159469)
              ·
                refine ⟨3580782523698587918684801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9548753396529567783159469 3580782523698587918684801)
                ·
                  refine ⟨2685586892773940939013601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580782523698587918684801 2685586892773940939013601)
                  ·
                    refine ⟨2014190169580455704260201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2685586892773940939013601 2014190169580455704260201)
                    ·
                      refine ⟨1510642627185341778195151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014190169580455704260201 1510642627185341778195151)
                      ·
                        rfl

theorem cell23_2941966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2941966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2941966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2941966 prefixEnd_2941966 := by exact prefixLift 2941966
  have htrace : WordTrace (prefixWord ++ tailWord_2941966) baseStart_2941966 baseEnd_2941966 := by
    simpa [prefixWord, tailWord_2941966, baseEnd_2941966] using wordTrace_append hprefix tailTrace_2941966
  have hstable : (prefixWord ++ tailWord_2941966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941966).length < 2 ^ (prefixWord ++ tailWord_2941966).sum := by decide
  have hdescent : baseEnd_2941966 < baseStart_2941966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942056 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2942056 : Nat := 118140960795 + 2942056 * 2 ^ 59
def prefixEnd_2942056 : Nat := 4983230072969 + 3 ^ 40 * 2942056 * 2
def baseEnd_2942056 : Nat := 1510688840444246426069737

theorem tailTrace_2942056 : CollatzResearch.WordTrace tailWord_2942056 prefixEnd_2942056 1510688840444246426069737 := by
  unfold tailWord_2942056
  simp only [CollatzResearch.WordTrace]
  refine ⟨53652798914720525003387011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71537065219627366671182681 53652798914720525003387011)
  ·
    refine ⟨80479198372080787505080517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53652798914720525003387011 80479198372080787505080517)
    ·
      refine ⟨15089849694765147657202597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80479198372080787505080517 15089849694765147657202597)
      ·
        refine ⟨2829346817768465185725487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15089849694765147657202597 2829346817768465185725487)
        ·
          refine ⟨4244020226652697778588231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829346817768465185725487 4244020226652697778588231)
          ·
            refine ⟨6366030339979046667882347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244020226652697778588231 6366030339979046667882347)
            ·
              refine ⟨9549045509968570001823521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366030339979046667882347 9549045509968570001823521)
              ·
                refine ⟨7161784132476427501367641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9549045509968570001823521 7161784132476427501367641)
                ·
                  refine ⟨5371338099357320626025731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161784132476427501367641 5371338099357320626025731)
                  ·
                    refine ⟨8057007149035980939038597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371338099357320626025731 8057007149035980939038597)
                    ·
                      refine ⟨1510688840444246426069737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8057007149035980939038597 1510688840444246426069737)
                      ·
                        rfl

theorem cell23_2942056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2942056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942056 prefixEnd_2942056 := by exact prefixLift 2942056
  have htrace : WordTrace (prefixWord ++ tailWord_2942056) baseStart_2942056 baseEnd_2942056 := by
    simpa [prefixWord, tailWord_2942056, baseEnd_2942056] using wordTrace_append hprefix tailTrace_2942056
  have hstable : (prefixWord ++ tailWord_2942056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942056).length < 2 ^ (prefixWord ++ tailWord_2942056).sum := by decide
  have hdescent : baseEnd_2942056 < baseStart_2942056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942062 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_2942062 : Nat := 118140960795 + 2942062 * 2 ^ 59
def prefixEnd_2942062 : Nat := 4983230072969 + 3 ^ 40 * 2942062 * 2
def baseEnd_2942062 : Nat := 167854657925352600288301

theorem tailTrace_2942062 : CollatzResearch.WordTrace tailWord_2942062 prefixEnd_2942062 167854657925352600288301 := by
  unfold tailWord_2942062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13413227083427414128936555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71537211111612875354328293 13413227083427414128936555)
  ·
    refine ⟨20119840625141121193404833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13413227083427414128936555 20119840625141121193404833)
    ·
      refine ⟨15089880468855840895053625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20119840625141121193404833 15089880468855840895053625)
      ·
        refine ⟨11317410351641880671290219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15089880468855840895053625 11317410351641880671290219)
        ·
          refine ⟨16976115527462821006935329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11317410351641880671290219 16976115527462821006935329)
          ·
            refine ⟨12732086645597115755201497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16976115527462821006935329 12732086645597115755201497)
            ·
              refine ⟨9549064984197836816401123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12732086645597115755201497 9549064984197836816401123)
              ·
                refine ⟨14323597476296755224601685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9549064984197836816401123 14323597476296755224601685)
                ·
                  refine ⟨167854657925352600288301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14323597476296755224601685 167854657925352600288301)
                  ·
                    rfl

theorem cell23_2942062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_2942062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942062 prefixEnd_2942062 := by exact prefixLift 2942062
  have htrace : WordTrace (prefixWord ++ tailWord_2942062) baseStart_2942062 baseEnd_2942062 := by
    simpa [prefixWord, tailWord_2942062, baseEnd_2942062] using wordTrace_append hprefix tailTrace_2942062
  have hstable : (prefixWord ++ tailWord_2942062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942062).length < 2 ^ (prefixWord ++ tailWord_2942062).sum := by decide
  have hdescent : baseEnd_2942062 < baseStart_2942062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942065 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2942065 : Nat := 118140960795 + 2942065 * 2 ^ 59
def prefixEnd_2942065 : Nat := 4983230072969 + 3 ^ 40 * 2942065 * 2
def baseEnd_2942065 : Nat := 1510693461770136890857195

theorem tailTrace_2942065 : CollatzResearch.WordTrace tailWord_2942065 prefixEnd_2942065 1510693461770136890857195 := by
  unfold tailWord_2942065
  simp only [CollatzResearch.WordTrace]
  refine ⟨107305926086408444543851649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71537284057605629695901099 107305926086408444543851649)
  ·
    refine ⟨80479444564806333407888737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107305926086408444543851649 80479444564806333407888737)
    ·
      refine ⟨60359583423604750055916553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80479444564806333407888737 60359583423604750055916553)
      ·
        refine ⟨45269687567703562541937415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60359583423604750055916553 45269687567703562541937415)
        ·
          refine ⟨67904531351555343812906123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45269687567703562541937415 67904531351555343812906123)
          ·
            refine ⟨101856797027333015719359185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67904531351555343812906123 101856797027333015719359185)
            ·
              refine ⟨76392597770499761789519389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101856797027333015719359185 76392597770499761789519389)
              ·
                refine ⟨28647224163937410671069771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76392597770499761789519389 28647224163937410671069771)
                ·
                  refine ⟨42970836245906116006604657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28647224163937410671069771 42970836245906116006604657)
                  ·
                    refine ⟨32228127184429587004953493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42970836245906116006604657 32228127184429587004953493)
                    ·
                      refine ⟨1510693461770136890857195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32228127184429587004953493 1510693461770136890857195)
                      ·
                        rfl

theorem cell23_2942065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2942065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942065 prefixEnd_2942065 := by exact prefixLift 2942065
  have htrace : WordTrace (prefixWord ++ tailWord_2942065) baseStart_2942065 baseEnd_2942065 := by
    simpa [prefixWord, tailWord_2942065, baseEnd_2942065] using wordTrace_append hprefix tailTrace_2942065
  have hstable : (prefixWord ++ tailWord_2942065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942065).length < 2 ^ (prefixWord ++ tailWord_2942065).sum := by decide
  have hdescent : baseEnd_2942065 < baseStart_2942065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942099 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 2, 3, 2]
def baseStart_2942099 : Nat := 118140960795 + 2942099 * 2 ^ 59
def prefixEnd_2942099 : Nat := 4983230072969 + 3 ^ 40 * 2942099 * 2
def baseEnd_2942099 : Nat := 1510710920112389757832039

theorem tailTrace_2942099 : CollatzResearch.WordTrace tailWord_2942099 prefixEnd_2942099 1510710920112389757832039 := by
  unfold tailWord_2942099
  simp only [CollatzResearch.WordTrace]
  refine ⟨107307166168285268350589351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71538110778856845567059567 107307166168285268350589351)
  ·
    refine ⟨160960749252427902525884027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107307166168285268350589351 160960749252427902525884027)
    ·
      refine ⟨241441123878641853788826041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160960749252427902525884027 241441123878641853788826041)
      ·
        refine ⟨181080842908981390341619531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241441123878641853788826041 181080842908981390341619531)
        ·
          refine ⟨271621264363472085512429297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181080842908981390341619531 271621264363472085512429297)
          ·
            refine ⟨203715948272604064134321973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271621264363472085512429297 203715948272604064134321973)
            ·
              refine ⟨19098370150556631012592685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203715948272604064134321973 19098370150556631012592685)
              ·
                refine ⟨7161888806458736629722257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19098370150556631012592685 7161888806458736629722257)
                ·
                  refine ⟨5371416604844052472291693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161888806458736629722257 5371416604844052472291693)
                  ·
                    refine ⟨2014281226816519677109385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5371416604844052472291693 2014281226816519677109385)
                    ·
                      refine ⟨1510710920112389757832039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014281226816519677109385 1510710920112389757832039)
                      ·
                        rfl

theorem cell23_2942099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3, 2].length) (baseStart_2942099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942099 prefixEnd_2942099 := by exact prefixLift 2942099
  have htrace : WordTrace (prefixWord ++ tailWord_2942099) baseStart_2942099 baseEnd_2942099 := by
    simpa [prefixWord, tailWord_2942099, baseEnd_2942099] using wordTrace_append hprefix tailTrace_2942099
  have hstable : (prefixWord ++ tailWord_2942099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942099).length < 2 ^ (prefixWord ++ tailWord_2942099).sum := by decide
  have hdescent : baseEnd_2942099 < baseStart_2942099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942116 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_2942116 : Nat := 118140960795 + 2942116 * 2 ^ 59
def prefixEnd_2942116 : Nat := 4983230072969 + 3 ^ 40 * 2942116 * 2
def baseEnd_2942116 : Nat := 1510719649283516191319461

theorem tailTrace_2942116 : CollatzResearch.WordTrace tailWord_2942116 prefixEnd_2942116 1510719649283516191319461 := by
  unfold tailWord_2942116
  simp only [CollatzResearch.WordTrace]
  refine ⟨53653893104611840126979101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71538524139482453502638801 53653893104611840126979101)
  ·
    refine ⟨20120209914229440047617163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53653893104611840126979101 20120209914229440047617163)
    ·
      refine ⟨30180314871344160071425745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20120209914229440047617163 30180314871344160071425745)
      ·
        refine ⟨22635236153508120053569309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30180314871344160071425745 22635236153508120053569309)
        ·
          refine ⟨8488213557565545020088491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22635236153508120053569309 8488213557565545020088491)
          ·
            refine ⟨12732320336348317530132737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488213557565545020088491 12732320336348317530132737)
            ·
              refine ⟨9549240252261238147599553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12732320336348317530132737 9549240252261238147599553)
              ·
                refine ⟨7161930189195928610699665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9549240252261238147599553 7161930189195928610699665)
                ·
                  refine ⟨5371447641896946458024749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161930189195928610699665 5371447641896946458024749)
                  ·
                    refine ⟨2014292865711354921759281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5371447641896946458024749 2014292865711354921759281)
                    ·
                      refine ⟨1510719649283516191319461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014292865711354921759281 1510719649283516191319461)
                      ·
                        rfl

theorem cell23_2942116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_2942116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942116 prefixEnd_2942116 := by exact prefixLift 2942116
  have htrace : WordTrace (prefixWord ++ tailWord_2942116) baseStart_2942116 baseEnd_2942116 := by
    simpa [prefixWord, tailWord_2942116, baseEnd_2942116] using wordTrace_append hprefix tailTrace_2942116
  have hstable : (prefixWord ++ tailWord_2942116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942116).length < 2 ^ (prefixWord ++ tailWord_2942116).sum := by decide
  have hdescent : baseEnd_2942116 < baseStart_2942116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942129 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2942129 : Nat := 118140960795 + 2942129 * 2 ^ 59
def prefixEnd_2942129 : Nat := 4983230072969 + 3 ^ 40 * 2942129 * 2
def baseEnd_2942129 : Nat := 1510726324532024640456901

theorem tailTrace_2942129 : CollatzResearch.WordTrace tailWord_2942129 prefixEnd_2942129 1510726324532024640456901 := by
  unfold tailWord_2942129
  simp only [CollatzResearch.WordTrace]
  refine ⟨107308260358176583474181441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71538840238784388982787627 107308260358176583474181441)
  ·
    refine ⟨80481195268632437605636081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107308260358176583474181441 80481195268632437605636081)
    ·
      refine ⟨60360896451474328204227061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80481195268632437605636081 60360896451474328204227061)
      ·
        refine ⟨5658834042325718269146287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60360896451474328204227061 5658834042325718269146287)
        ·
          refine ⟨8488251063488577403719431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658834042325718269146287 8488251063488577403719431)
          ·
            refine ⟨12732376595232866105579147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488251063488577403719431 12732376595232866105579147)
            ·
              refine ⟨19098564892849299158368721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12732376595232866105579147 19098564892849299158368721)
              ·
                refine ⟨14323923669636974368776541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19098564892849299158368721 14323923669636974368776541)
                ·
                  refine ⟨5371471376113865388291203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14323923669636974368776541 5371471376113865388291203)
                  ·
                    refine ⟨8057207064170798082436805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5371471376113865388291203 8057207064170798082436805)
                    ·
                      refine ⟨1510726324532024640456901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8057207064170798082436805 1510726324532024640456901)
                      ·
                        rfl

theorem cell23_2942129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2942129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942129 prefixEnd_2942129 := by exact prefixLift 2942129
  have htrace : WordTrace (prefixWord ++ tailWord_2942129) baseStart_2942129 baseEnd_2942129 := by
    simpa [prefixWord, tailWord_2942129, baseEnd_2942129] using wordTrace_append hprefix tailTrace_2942129
  have hstable : (prefixWord ++ tailWord_2942129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942129).length < 2 ^ (prefixWord ++ tailWord_2942129).sum := by decide
  have hdescent : baseEnd_2942129 < baseStart_2942129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942149 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_2942149 : Nat := 118140960795 + 2942149 * 2 ^ 59
def prefixEnd_2942149 : Nat := 4983230072969 + 3 ^ 40 * 2942149 * 2
def baseEnd_2942149 : Nat := 1510736594145114562206809

theorem tailTrace_2942149 : CollatzResearch.WordTrace tailWord_2942149 prefixEnd_2942149 1510736594145114562206809 := by
  unfold tailWord_2942149
  simp only [CollatzResearch.WordTrace]
  refine ⟨107308989818104126889909501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71539326545402751259939667 107308989818104126889909501)
  ·
    refine ⟨40240871181789047583716063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107308989818104126889909501 40240871181789047583716063)
    ·
      refine ⟨60361306772683571375574095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40240871181789047583716063 60361306772683571375574095)
      ·
        refine ⟨90541960159025357063361143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60361306772683571375574095 90541960159025357063361143)
        ·
          refine ⟨135812940238538035595041715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90541960159025357063361143 135812940238538035595041715)
          ·
            refine ⟨203719410357807053392562573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135812940238538035595041715 203719410357807053392562573)
            ·
              refine ⟨76394778884177645022210965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203719410357807053392562573 76394778884177645022210965)
              ·
                refine ⟨3581005260195827110416139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76394778884177645022210965 3581005260195827110416139)
                ·
                  refine ⟨5371507890293740665624209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581005260195827110416139 5371507890293740665624209)
                  ·
                    refine ⟨4028630917720305499218157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371507890293740665624209 4028630917720305499218157)
                    ·
                      refine ⟨1510736594145114562206809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4028630917720305499218157 1510736594145114562206809)
                      ·
                        rfl

theorem cell23_2942149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_2942149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942149 prefixEnd_2942149 := by exact prefixLift 2942149
  have htrace : WordTrace (prefixWord ++ tailWord_2942149) baseStart_2942149 baseEnd_2942149 := by
    simpa [prefixWord, tailWord_2942149, baseEnd_2942149] using wordTrace_append hprefix tailTrace_2942149
  have hstable : (prefixWord ++ tailWord_2942149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942149).length < 2 ^ (prefixWord ++ tailWord_2942149).sum := by decide
  have hdescent : baseEnd_2942149 < baseStart_2942149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942289 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_2942289 : Nat := 118140960795 + 2942289 * 2 ^ 59
def prefixEnd_2942289 : Nat := 4983230072969 + 3 ^ 40 * 2942289 * 2
def baseEnd_2942289 : Nat := 503602827145581338152055

theorem tailTrace_2942289 : CollatzResearch.WordTrace tailWord_2942289 prefixEnd_2942289 503602827145581338152055 := by
  unfold tailWord_2942289
  simp only [CollatzResearch.WordTrace]
  refine ⟨107314096037596930800005921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71542730691731287200003947 107314096037596930800005921)
  ·
    refine ⟨80485572028197698100004441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107314096037596930800005921 80485572028197698100004441)
    ·
      refine ⟨60364179021148273575003331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80485572028197698100004441 60364179021148273575003331)
      ·
        refine ⟨90546268531722410362504997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60364179021148273575003331 90546268531722410362504997)
        ·
          refine ⟨16977425349697951942969687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90546268531722410362504997 16977425349697951942969687)
          ·
            refine ⟨25466138024546927914454531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16977425349697951942969687 25466138024546927914454531)
            ·
              refine ⟨38199207036820391871681797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25466138024546927914454531 38199207036820391871681797)
              ·
                refine ⟨7162351319403823475940337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38199207036820391871681797 7162351319403823475940337)
                ·
                  refine ⟨5371763489552867606955253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162351319403823475940337 5371763489552867606955253)
                  ·
                    refine ⟨503602827145581338152055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5371763489552867606955253 503602827145581338152055)
                    ·
                      rfl

theorem cell23_2942289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_2942289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942289 prefixEnd_2942289 := by exact prefixLift 2942289
  have htrace : WordTrace (prefixWord ++ tailWord_2942289) baseStart_2942289 baseEnd_2942289 := by
    simpa [prefixWord, tailWord_2942289, baseEnd_2942289] using wordTrace_append hprefix tailTrace_2942289
  have hstable : (prefixWord ++ tailWord_2942289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942289).length < 2 ^ (prefixWord ++ tailWord_2942289).sum := by decide
  have hdescent : baseEnd_2942289 < baseStart_2942289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942293 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 5]
def baseStart_2942293 : Nat := 118140960795 + 2942293 * 2 ^ 59
def prefixEnd_2942293 : Nat := 4983230072969 + 3 ^ 40 * 2942293 * 2
def baseEnd_2942293 : Nat := 167867837262151333200683

theorem tailTrace_2942293 : CollatzResearch.WordTrace tailWord_2942293 prefixEnd_2942293 167867837262151333200683 := by
  unfold tailWord_2942293
  simp only [CollatzResearch.WordTrace]
  refine ⟨107314241929582439483151533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71542827953054959655434355 107314241929582439483151533)
  ·
    refine ⟨40242840723593414806181825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107314241929582439483151533 40242840723593414806181825)
    ·
      refine ⟨30182130542695061104636369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40242840723593414806181825 30182130542695061104636369)
      ·
        refine ⟨22636597907021295828477277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30182130542695061104636369 22636597907021295828477277)
        ·
          refine ⟨8488724215132985935678979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22636597907021295828477277 8488724215132985935678979)
          ·
            refine ⟨12733086322699478903518469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488724215132985935678979 12733086322699478903518469)
            ·
              refine ⟨2387453685506152294409713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12733086322699478903518469 2387453685506152294409713)
              ·
                refine ⟨1790590264129614220807285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387453685506152294409713 1790590264129614220807285)
                ·
                  refine ⟨167867837262151333200683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1790590264129614220807285 167867837262151333200683)
                  ·
                    rfl

theorem cell23_2942293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_2942293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942293 prefixEnd_2942293 := by exact prefixLift 2942293
  have htrace : WordTrace (prefixWord ++ tailWord_2942293) baseStart_2942293 baseEnd_2942293 := by
    simpa [prefixWord, tailWord_2942293, baseEnd_2942293] using wordTrace_append hprefix tailTrace_2942293
  have hstable : (prefixWord ++ tailWord_2942293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942293).length < 2 ^ (prefixWord ++ tailWord_2942293).sum := by decide
  have hdescent : baseEnd_2942293 < baseStart_2942293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942309 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2942309 : Nat := 118140960795 + 2942309 * 2 ^ 59
def prefixEnd_2942309 : Nat := 4983230072969 + 3 ^ 40 * 2942309 * 2
def baseEnd_2942309 : Nat := 1510818751049833936206073

theorem tailTrace_2942309 : CollatzResearch.WordTrace tailWord_2942309 prefixEnd_2942309 1510818751049833936206073 := by
  unfold tailWord_2942309
  simp only [CollatzResearch.WordTrace]
  refine ⟨107314825497524474215733981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71543216998349649477155987 107314825497524474215733981)
  ·
    refine ⟨40243059561571677830900243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107314825497524474215733981 40243059561571677830900243)
    ·
      refine ⟨60364589342357516746350365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40243059561571677830900243 60364589342357516746350365)
      ·
        refine ⟨22636721003384068779881387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60364589342357516746350365 22636721003384068779881387)
        ·
          refine ⟨33955081505076103169822081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22636721003384068779881387 33955081505076103169822081)
          ·
            refine ⟨25466311128807077377366561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33955081505076103169822081 25466311128807077377366561)
            ·
              refine ⟨19099733346605308033024921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25466311128807077377366561 19099733346605308033024921)
              ·
                refine ⟨14324800009953981024768691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19099733346605308033024921 14324800009953981024768691)
                ·
                  refine ⟨21487200014930971537153037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14324800009953981024768691 21487200014930971537153037)
                  ·
                    refine ⟨8057700005599114326432389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21487200014930971537153037 8057700005599114326432389)
                    ·
                      refine ⟨1510818751049833936206073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8057700005599114326432389 1510818751049833936206073)
                      ·
                        rfl

theorem cell23_2942309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2942309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942309 prefixEnd_2942309 := by exact prefixLift 2942309
  have htrace : WordTrace (prefixWord ++ tailWord_2942309) baseStart_2942309 baseEnd_2942309 := by
    simpa [prefixWord, tailWord_2942309, baseEnd_2942309] using wordTrace_append hprefix tailTrace_2942309
  have hstable : (prefixWord ++ tailWord_2942309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942309).length < 2 ^ (prefixWord ++ tailWord_2942309).sum := by decide
  have hdescent : baseEnd_2942309 < baseStart_2942309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942339 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_2942339 : Nat := 118140960795 + 2942339 * 2 ^ 59
def prefixEnd_2942339 : Nat := 4983230072969 + 3 ^ 40 * 2942339 * 2
def baseEnd_2942339 : Nat := 1510834155469468818830935

theorem tailTrace_2942339 : CollatzResearch.WordTrace tailWord_2942339 prefixEnd_2942339 1510834155469468818830935 := by
  unfold tailWord_2942339
  simp only [CollatzResearch.WordTrace]
  refine ⟨107315919687415789339326071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71543946458277192892884047 107315919687415789339326071)
  ·
    refine ⟨160973879531123684008989107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107315919687415789339326071 160973879531123684008989107)
    ·
      refine ⟨241460819296685526013483661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160973879531123684008989107 241460819296685526013483661)
      ·
        refine ⟨90547807236257072255056373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241460819296685526013483661 90547807236257072255056373)
        ·
          refine ⟨8488856928399100523911535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90547807236257072255056373 8488856928399100523911535)
          ·
            refine ⟨12733285392598650785867303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488856928399100523911535 12733285392598650785867303)
            ·
              refine ⟨19099928088897976178800955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12733285392598650785867303 19099928088897976178800955)
              ·
                refine ⟨28649892133346964268201433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19099928088897976178800955 28649892133346964268201433)
                ·
                  refine ⟨21487419100010223201151075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28649892133346964268201433 21487419100010223201151075)
                  ·
                    refine ⟨32231128650015334801726613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21487419100010223201151075 32231128650015334801726613)
                    ·
                      refine ⟨1510834155469468818830935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32231128650015334801726613 1510834155469468818830935)
                      ·
                        rfl

theorem cell23_2942339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_2942339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942339 prefixEnd_2942339 := by exact prefixLift 2942339
  have htrace : WordTrace (prefixWord ++ tailWord_2942339) baseStart_2942339 baseEnd_2942339 := by
    simpa [prefixWord, tailWord_2942339, baseEnd_2942339] using wordTrace_append hprefix tailTrace_2942339
  have hstable : (prefixWord ++ tailWord_2942339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942339).length < 2 ^ (prefixWord ++ tailWord_2942339).sum := by decide
  have hdescent : baseEnd_2942339 < baseStart_2942339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942410 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_2942410 : Nat := 118140960795 + 2942410 * 2 ^ 59
def prefixEnd_2942410 : Nat := 4983230072969 + 3 ^ 40 * 2942410 * 2
def baseEnd_2942410 : Nat := 1510870612595938041043109

theorem tailTrace_2942410 : CollatzResearch.WordTrace tailWord_2942410 prefixEnd_2942410 1510870612595938041043109 := by
  unfold tailWord_2942410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829627317539642116290171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71545672846772378976773789 26829627317539642116290171)
  ·
    refine ⟨40244440976309463174435257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26829627317539642116290171 40244440976309463174435257)
    ·
      refine ⟨30183330732232097380826443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40244440976309463174435257 30183330732232097380826443)
      ·
        refine ⟨45274996098348146071239665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30183330732232097380826443 45274996098348146071239665)
        ·
          refine ⟨33956247073761109553429749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45274996098348146071239665 33956247073761109553429749)
          ·
            refine ⟨3183398163165104020634039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33956247073761109553429749 3183398163165104020634039)
            ·
              refine ⟨4775097244747656030951059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183398163165104020634039 4775097244747656030951059)
              ·
                refine ⟨7162645867121484046426589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775097244747656030951059 7162645867121484046426589)
                ·
                  refine ⟨2685992200170556517409971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7162645867121484046426589 2685992200170556517409971)
                  ·
                    refine ⟨4028988300255834776114957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2685992200170556517409971 4028988300255834776114957)
                    ·
                      refine ⟨1510870612595938041043109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4028988300255834776114957 1510870612595938041043109)
                      ·
                        rfl

theorem cell23_2942410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_2942410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942410 prefixEnd_2942410 := by exact prefixLift 2942410
  have htrace : WordTrace (prefixWord ++ tailWord_2942410) baseStart_2942410 baseEnd_2942410 := by
    simpa [prefixWord, tailWord_2942410, baseEnd_2942410] using wordTrace_append hprefix tailTrace_2942410
  have hstable : (prefixWord ++ tailWord_2942410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942410).length < 2 ^ (prefixWord ++ tailWord_2942410).sum := by decide
  have hdescent : baseEnd_2942410 < baseStart_2942410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942433 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2942433 : Nat := 118140960795 + 2942433 * 2 ^ 59
def prefixEnd_2942433 : Nat := 4983230072969 + 3 ^ 40 * 2942433 * 2
def baseEnd_2942433 : Nat := 1510882422650991451055503

theorem tailTrace_2942433 : CollatzResearch.WordTrace tailWord_2942433 prefixEnd_2942433 1510882422650991451055503 := by
  unfold tailWord_2942433
  simp only [CollatzResearch.WordTrace]
  refine ⟨107319348149075243393247953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71546232099383495595498635 107319348149075243393247953)
  ·
    refine ⟨80489511111806432544935965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107319348149075243393247953 80489511111806432544935965)
    ·
      refine ⟨30183566666927412204350987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80489511111806432544935965 30183566666927412204350987)
      ·
        refine ⟨45275350000391118306526481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30183566666927412204350987 45275350000391118306526481)
        ·
          refine ⟨33956512500293338729894861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45275350000391118306526481 33956512500293338729894861)
          ·
            refine ⟨12733692187610002023710573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33956512500293338729894861 12733692187610002023710573)
            ·
              refine ⟨4775134570353750758891465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12733692187610002023710573 4775134570353750758891465)
              ·
                refine ⟨3581350927765313069168599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775134570353750758891465 3581350927765313069168599)
                ·
                  refine ⟨5372026391647969603752899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581350927765313069168599 5372026391647969603752899)
                  ·
                    refine ⟨8058039587471954405629349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5372026391647969603752899 8058039587471954405629349)
                    ·
                      refine ⟨1510882422650991451055503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8058039587471954405629349 1510882422650991451055503)
                      ·
                        rfl

theorem cell23_2942433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2942433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942433 prefixEnd_2942433 := by exact prefixLift 2942433
  have htrace : WordTrace (prefixWord ++ tailWord_2942433) baseStart_2942433 baseEnd_2942433 := by
    simpa [prefixWord, tailWord_2942433, baseEnd_2942433] using wordTrace_append hprefix tailTrace_2942433
  have hstable : (prefixWord ++ tailWord_2942433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942433).length < 2 ^ (prefixWord ++ tailWord_2942433).sum := by decide
  have hdescent : baseEnd_2942433 < baseStart_2942433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942477 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2942477 : Nat := 118140960795 + 2942477 * 2 ^ 59
def prefixEnd_2942477 : Nat := 4983230072969 + 3 ^ 40 * 2942477 * 2
def baseEnd_2942477 : Nat := 503635005266596426301767

theorem tailTrace_2942477 : CollatzResearch.WordTrace tailWord_2942477 prefixEnd_2942477 503635005266596426301767 := by
  unfold tailWord_2942477
  simp only [CollatzResearch.WordTrace]
  refine ⟨107320952960915838907849685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71547301973943892605233123 107320952960915838907849685)
  ·
    refine ⟨2515334835021464974402727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107320952960915838907849685 2515334835021464974402727)
    ·
      refine ⟨3773002252532197461604091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515334835021464974402727 3773002252532197461604091)
      ·
        refine ⟨5659503378798296192406137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773002252532197461604091 5659503378798296192406137)
        ·
          refine ⟨4244627534098722144304603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5659503378798296192406137 4244627534098722144304603)
          ·
            refine ⟨6366941301148083216456905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244627534098722144304603 6366941301148083216456905)
            ·
              refine ⟨4775205975861062412342679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6366941301148083216456905 4775205975861062412342679)
              ·
                refine ⟨7162808963791593618514019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775205975861062412342679 7162808963791593618514019)
                ·
                  refine ⟨10744213445687390427771029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162808963791593618514019 10744213445687390427771029)
                  ·
                    refine ⟨503635005266596426301767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10744213445687390427771029 503635005266596426301767)
                    ·
                      rfl

theorem cell23_2942477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2942477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942477 prefixEnd_2942477 := by exact prefixLift 2942477
  have htrace : WordTrace (prefixWord ++ tailWord_2942477) baseStart_2942477 baseEnd_2942477 := by
    simpa [prefixWord, tailWord_2942477, baseEnd_2942477] using wordTrace_append hprefix tailTrace_2942477
  have hstable : (prefixWord ++ tailWord_2942477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942477).length < 2 ^ (prefixWord ++ tailWord_2942477).sum := by decide
  have hdescent : baseEnd_2942477 < baseStart_2942477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942483 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3]
def baseStart_2942483 : Nat := 118140960795 + 2942483 * 2 ^ 59
def prefixEnd_2942483 : Nat := 4983230072969 + 3 ^ 40 * 2942483 * 2
def baseEnd_2942483 : Nat := 1510908096683716255430273

theorem tailTrace_2942483 : CollatzResearch.WordTrace tailWord_2942483 prefixEnd_2942483 1510908096683716255430273 := by
  unfold tailWord_2942483
  simp only [CollatzResearch.WordTrace]
  refine ⟨107321171798894101932568103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71547447865929401288378735 107321171798894101932568103)
  ·
    refine ⟨160981757698341152898852155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107321171798894101932568103 160981757698341152898852155)
    ·
      refine ⟨241472636547511729348278233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160981757698341152898852155 241472636547511729348278233)
      ·
        refine ⟨181104477410633797011208675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241472636547511729348278233 181104477410633797011208675)
        ·
          refine ⟨271656716115950695516813013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181104477410633797011208675 271656716115950695516813013)
          ·
            refine ⟨6366954283967594426175305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 271656716115950695516813013 6366954283967594426175305)
            ·
              refine ⟨4775215712975695819631479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6366954283967594426175305 4775215712975695819631479)
              ·
                refine ⟨7162823569463543729447219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775215712975695819631479 7162823569463543729447219)
                ·
                  refine ⟨10744235354195315594170829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162823569463543729447219 10744235354195315594170829)
                  ·
                    refine ⟨4029088257823243347814061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10744235354195315594170829 4029088257823243347814061)
                    ·
                      refine ⟨1510908096683716255430273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029088257823243347814061 1510908096683716255430273)
                      ·
                        rfl

theorem cell23_2942483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_2942483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942483 prefixEnd_2942483 := by exact prefixLift 2942483
  have htrace : WordTrace (prefixWord ++ tailWord_2942483) baseStart_2942483 baseEnd_2942483 := by
    simpa [prefixWord, tailWord_2942483, baseEnd_2942483] using wordTrace_append hprefix tailTrace_2942483
  have hstable : (prefixWord ++ tailWord_2942483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942483).length < 2 ^ (prefixWord ++ tailWord_2942483).sum := by decide
  have hdescent : baseEnd_2942483 < baseStart_2942483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942484 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2942484 : Nat := 118140960795 + 2942484 * 2 ^ 59
def prefixEnd_2942484 : Nat := 4983230072969 + 3 ^ 40 * 2942484 * 2
def baseEnd_2942484 : Nat := 1510908610164370751517769

theorem tailTrace_2942484 : CollatzResearch.WordTrace tailWord_2942484 prefixEnd_2942484 1510908610164370751517769 := by
  unfold tailWord_2942484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53660604135945239551677253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71547472181260319402236337 53660604135945239551677253)
  ·
    refine ⟨10061363275489732415939485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53660604135945239551677253 10061363275489732415939485)
    ·
      refine ⟨3773011228308649655977307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10061363275489732415939485 3773011228308649655977307)
      ·
        refine ⟨5659516842462974483965961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773011228308649655977307 5659516842462974483965961)
        ·
          refine ⟨4244637631847230862974471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5659516842462974483965961 4244637631847230862974471)
          ·
            refine ⟨6366956447770846294461707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244637631847230862974471 6366956447770846294461707)
            ·
              refine ⟨9550434671656269441692561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366956447770846294461707 9550434671656269441692561)
              ·
                refine ⟨7162826003742202081269421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9550434671656269441692561 7162826003742202081269421)
                ·
                  refine ⟨2686059751403325780476033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7162826003742202081269421 2686059751403325780476033)
                  ·
                    refine ⟨2014544813552494335357025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686059751403325780476033 2014544813552494335357025)
                    ·
                      refine ⟨1510908610164370751517769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014544813552494335357025 1510908610164370751517769)
                      ·
                        rfl

theorem cell23_2942484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2942484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942484 prefixEnd_2942484 := by exact prefixLift 2942484
  have htrace : WordTrace (prefixWord ++ tailWord_2942484) baseStart_2942484 baseEnd_2942484 := by
    simpa [prefixWord, tailWord_2942484, baseEnd_2942484] using wordTrace_append hprefix tailTrace_2942484
  have hstable : (prefixWord ++ tailWord_2942484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942484).length < 2 ^ (prefixWord ++ tailWord_2942484).sum := by decide
  have hdescent : baseEnd_2942484 < baseStart_2942484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2942489 : Nat := 118140960795 + 2942489 * 2 ^ 59
def prefixEnd_2942489 : Nat := 4983230072969 + 3 ^ 40 * 2942489 * 2
def baseEnd_2942489 : Nat := 1510911177567643231955245

theorem tailTrace_2942489 : CollatzResearch.WordTrace tailWord_2942489 prefixEnd_2942489 1510911177567643231955245 := by
  unfold tailWord_2942489
  simp only [CollatzResearch.WordTrace]
  refine ⟨107321390636872364957286521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71547593757914909971524347 107321390636872364957286521)
  ·
    refine ⟨80491042977654273717964891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107321390636872364957286521 80491042977654273717964891)
    ·
      refine ⟨120736564466481410576947337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80491042977654273717964891 120736564466481410576947337)
      ·
        refine ⟨90552423349861057932710503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120736564466481410576947337 90552423349861057932710503)
        ·
          refine ⟨135828635024791586899065755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90552423349861057932710503 135828635024791586899065755)
          ·
            refine ⟨203742952537187380348598633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135828635024791586899065755 203742952537187380348598633)
            ·
              refine ⟨152807214402890535261448975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203742952537187380348598633 152807214402890535261448975)
              ·
                refine ⟨229210821604335802892173463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152807214402890535261448975 229210821604335802892173463)
                ·
                  refine ⟨343816232406503704338260195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229210821604335802892173463 343816232406503704338260195)
                  ·
                    refine ⟨515724348609755556507390293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343816232406503704338260195 515724348609755556507390293)
                    ·
                      refine ⟨1510911177567643231955245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 515724348609755556507390293 1510911177567643231955245)
                      ·
                        rfl

theorem cell23_2942489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2942489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942489 prefixEnd_2942489 := by exact prefixLift 2942489
  have htrace : WordTrace (prefixWord ++ tailWord_2942489) baseStart_2942489 baseEnd_2942489 := by
    simpa [prefixWord, tailWord_2942489, baseEnd_2942489] using wordTrace_append hprefix tailTrace_2942489
  have hstable : (prefixWord ++ tailWord_2942489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942489).length < 2 ^ (prefixWord ++ tailWord_2942489).sum := by decide
  have hdescent : baseEnd_2942489 < baseStart_2942489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942504 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2942504 : Nat := 118140960795 + 2942504 * 2 ^ 59
def prefixEnd_2942504 : Nat := 4983230072969 + 3 ^ 40 * 2942504 * 2
def baseEnd_2942504 : Nat := 1510918879777460673267677

theorem tailTrace_2942504 : CollatzResearch.WordTrace tailWord_2942504 prefixEnd_2942504 1510918879777460673267677 := by
  unfold tailWord_2942504
  simp only [CollatzResearch.WordTrace]
  refine ⟨53660968865909011259541283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71547958487878681679388377 53660968865909011259541283)
  ·
    refine ⟨80491453298863516889311925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53660968865909011259541283 80491453298863516889311925)
    ·
      refine ⟨7546073746768454708372993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80491453298863516889311925 7546073746768454708372993)
      ·
        refine ⟨5659555310076341031279745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546073746768454708372993 5659555310076341031279745)
        ·
          refine ⟨4244666482557255773459809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5659555310076341031279745 4244666482557255773459809)
          ·
            refine ⟨3183499861917941830094857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4244666482557255773459809 3183499861917941830094857)
            ·
              refine ⟨2387624896438456372571143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183499861917941830094857 2387624896438456372571143)
              ·
                refine ⟨3581437344657684558856715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387624896438456372571143 3581437344657684558856715)
                ·
                  refine ⟨5372156016986526838285073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581437344657684558856715 5372156016986526838285073)
                  ·
                    refine ⟨4029117012739895128713805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5372156016986526838285073 4029117012739895128713805)
                    ·
                      refine ⟨1510918879777460673267677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029117012739895128713805 1510918879777460673267677)
                      ·
                        rfl

theorem cell23_2942504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2942504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942504 prefixEnd_2942504 := by exact prefixLift 2942504
  have htrace : WordTrace (prefixWord ++ tailWord_2942504) baseStart_2942504 baseEnd_2942504 := by
    simpa [prefixWord, tailWord_2942504, baseEnd_2942504] using wordTrace_append hprefix tailTrace_2942504
  have hstable : (prefixWord ++ tailWord_2942504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942504).length < 2 ^ (prefixWord ++ tailWord_2942504).sum := by decide
  have hdescent : baseEnd_2942504 < baseStart_2942504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942517 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2942517 : Nat := 118140960795 + 2942517 * 2 ^ 59
def prefixEnd_2942517 : Nat := 4983230072969 + 3 ^ 40 * 2942517 * 2
def baseEnd_2942517 : Nat := 1510925555025969122405117

theorem tailTrace_2942517 : CollatzResearch.WordTrace tailWord_2942517 prefixEnd_2942517 1510925555025969122405117 := by
  unfold tailWord_2942517
  simp only [CollatzResearch.WordTrace]
  refine ⟨107322411880770925739305805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71548274587180617159537203 107322411880770925739305805)
  ·
    refine ⟨40245904455289097152239677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107322411880770925739305805 40245904455289097152239677)
    ·
      refine ⟨15092214170733411432089879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40245904455289097152239677 15092214170733411432089879)
      ·
        refine ⟨22638321256100117148134819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15092214170733411432089879 22638321256100117148134819)
        ·
          refine ⟨33957481884150175722202229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22638321256100117148134819 33957481884150175722202229)
          ·
            refine ⟨3183513926639078973956459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33957481884150175722202229 3183513926639078973956459)
            ·
              refine ⟨4775270889958618460934689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183513926639078973956459 4775270889958618460934689)
              ·
                refine ⟨3581453167468963845701017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775270889958618460934689 3581453167468963845701017)
                ·
                  refine ⟨2686089875601722884275763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581453167468963845701017 2686089875601722884275763)
                  ·
                    refine ⟨4029134813402584326413645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686089875601722884275763 4029134813402584326413645)
                    ·
                      refine ⟨1510925555025969122405117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029134813402584326413645 1510925555025969122405117)
                      ·
                        rfl

theorem cell23_2942517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2942517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942517 prefixEnd_2942517 := by exact prefixLift 2942517
  have htrace : WordTrace (prefixWord ++ tailWord_2942517) baseStart_2942517 baseEnd_2942517 := by
    simpa [prefixWord, tailWord_2942517, baseEnd_2942517] using wordTrace_append hprefix tailTrace_2942517
  have hstable : (prefixWord ++ tailWord_2942517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942517).length < 2 ^ (prefixWord ++ tailWord_2942517).sum := by decide
  have hdescent : baseEnd_2942517 < baseStart_2942517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942534 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2942534 : Nat := 118140960795 + 2942534 * 2 ^ 59
def prefixEnd_2942534 : Nat := 4983230072969 + 3 ^ 40 * 2942534 * 2
def baseEnd_2942534 : Nat := 1510934284197095555892539

theorem tailTrace_2942534 : CollatzResearch.WordTrace tailWord_2942534 prefixEnd_2942534 1510934284197095555892539 := by
  unfold tailWord_2942534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353844747553416801333583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71548687947806225095116437 3353844747553416801333583)
  ·
    refine ⟨5030767121330125202000375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353844747553416801333583 5030767121330125202000375)
    ·
      refine ⟨7546150681995187803000563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030767121330125202000375 7546150681995187803000563)
      ·
        refine ⟨11319226022992781704500845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546150681995187803000563 11319226022992781704500845)
        ·
          refine ⟨4244709758622293139187817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11319226022992781704500845 4244709758622293139187817)
          ·
            refine ⟨3183532318966719854390863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4244709758622293139187817 3183532318966719854390863)
            ·
              refine ⟨4775298478450079781586295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183532318966719854390863 4775298478450079781586295)
              ·
                refine ⟨7162947717675119672379443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775298478450079781586295 7162947717675119672379443)
                ·
                  refine ⟨10744421576512679508569165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162947717675119672379443 10744421576512679508569165)
                  ·
                    refine ⟨4029158091192254815713437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10744421576512679508569165 4029158091192254815713437)
                    ·
                      refine ⟨1510934284197095555892539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029158091192254815713437 1510934284197095555892539)
                      ·
                        rfl

theorem cell23_2942534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2942534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942534 prefixEnd_2942534 := by exact prefixLift 2942534
  have htrace : WordTrace (prefixWord ++ tailWord_2942534) baseStart_2942534 baseEnd_2942534 := by
    simpa [prefixWord, tailWord_2942534, baseEnd_2942534] using wordTrace_append hprefix tailTrace_2942534
  have hstable : (prefixWord ++ tailWord_2942534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942534).length < 2 ^ (prefixWord ++ tailWord_2942534).sum := by decide
  have hdescent : baseEnd_2942534 < baseStart_2942534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942540 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_2942540 : Nat := 118140960795 + 2942540 * 2 ^ 59
def prefixEnd_2942540 : Nat := 4983230072969 + 3 ^ 40 * 2942540 * 2
def baseEnd_2942540 : Nat := 1510937365081022532417511

theorem tailTrace_2942540 : CollatzResearch.WordTrace tailWord_2942540 prefixEnd_2942540 1510937365081022532417511 := by
  unfold tailWord_2942540
  simp only [CollatzResearch.WordTrace]
  refine ⟨53661625379843800333696537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71548833839791733778262049 53661625379843800333696537)
  ·
    refine ⟨40246219034882850250272403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53661625379843800333696537 40246219034882850250272403)
    ·
      refine ⟨60369328552324275375408605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40246219034882850250272403 60369328552324275375408605)
      ·
        refine ⟨22638498207121603265778227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60369328552324275375408605 22638498207121603265778227)
        ·
          refine ⟨33957747310682404898667341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22638498207121603265778227 33957747310682404898667341)
          ·
            refine ⟨12734155241505901837000253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33957747310682404898667341 12734155241505901837000253)
            ·
              refine ⟨4775308215564713188875095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12734155241505901837000253 4775308215564713188875095)
              ·
                refine ⟨7162962323347069783312643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775308215564713188875095 7162962323347069783312643)
                ·
                  refine ⟨10744443485020604674968965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162962323347069783312643 10744443485020604674968965)
                  ·
                    refine ⟨2014583153441363376556681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10744443485020604674968965 2014583153441363376556681)
                    ·
                      refine ⟨1510937365081022532417511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014583153441363376556681 1510937365081022532417511)
                      ·
                        rfl

theorem cell23_2942540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_2942540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942540 prefixEnd_2942540 := by exact prefixLift 2942540
  have htrace : WordTrace (prefixWord ++ tailWord_2942540) baseStart_2942540 baseEnd_2942540 := by
    simpa [prefixWord, tailWord_2942540, baseEnd_2942540] using wordTrace_append hprefix tailTrace_2942540
  have hstable : (prefixWord ++ tailWord_2942540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942540).length < 2 ^ (prefixWord ++ tailWord_2942540).sum := by decide
  have hdescent : baseEnd_2942540 < baseStart_2942540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942583 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_2942583 : Nat := 118140960795 + 2942583 * 2 ^ 59
def prefixEnd_2942583 : Nat := 4983230072969 + 3 ^ 40 * 2942583 * 2
def baseEnd_2942583 : Nat := 1510959444749165864179813

theorem tailTrace_2942583 : CollatzResearch.WordTrace tailWord_2942583 prefixEnd_2942583 1510959444749165864179813 := by
  unfold tailWord_2942583
  simp only [CollatzResearch.WordTrace]
  refine ⟨107324819098531819011208403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71549879399021212674138935 107324819098531819011208403)
  ·
    refine ⟨160987228647797728516812605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107324819098531819011208403 160987228647797728516812605)
    ·
      refine ⟨60370210742924148193804727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160987228647797728516812605 60370210742924148193804727)
      ·
        refine ⟨90555316114386222290707091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60370210742924148193804727 90555316114386222290707091)
        ·
          refine ⟨135832974171579333436060637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90555316114386222290707091 135832974171579333436060637)
          ·
            refine ⟨50937365314342250038522739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135832974171579333436060637 50937365314342250038522739)
            ·
              refine ⟨76406047971513375057784109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50937365314342250038522739 76406047971513375057784109)
              ·
                refine ⟨28652267989317515646669041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76406047971513375057784109 28652267989317515646669041)
                ·
                  refine ⟨21489200991988136735001781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28652267989317515646669041 21489200991988136735001781)
                  ·
                    refine ⟨2014612592998887818906417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21489200991988136735001781 2014612592998887818906417)
                    ·
                      refine ⟨1510959444749165864179813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014612592998887818906417 1510959444749165864179813)
                      ·
                        rfl

theorem cell23_2942583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_2942583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942583 prefixEnd_2942583 := by exact prefixLift 2942583
  have htrace : WordTrace (prefixWord ++ tailWord_2942583) baseStart_2942583 baseEnd_2942583 := by
    simpa [prefixWord, tailWord_2942583, baseEnd_2942583] using wordTrace_append hprefix tailTrace_2942583
  have hstable : (prefixWord ++ tailWord_2942583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942583).length < 2 ^ (prefixWord ++ tailWord_2942583).sum := by decide
  have hdescent : baseEnd_2942583 < baseStart_2942583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942653 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 6]
def baseStart_2942653 : Nat := 118140960795 + 2942653 * 2 ^ 59
def prefixEnd_2942653 : Nat := 4983230072969 + 3 ^ 40 * 2942653 * 2
def baseEnd_2942653 : Nat := 167888376488331176700499

theorem tailTrace_2942653 : CollatzResearch.WordTrace tailWord_2942653 prefixEnd_2942653 167888376488331176700499 := by
  unfold tailWord_2942653
  simp only [CollatzResearch.WordTrace]
  refine ⟨107327372208278220966256613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71551581472185480644171075 107327372208278220966256613)
  ·
    refine ⟨20123882289052166431173115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107327372208278220966256613 20123882289052166431173115)
    ·
      refine ⟨30185823433578249646759673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20123882289052166431173115 30185823433578249646759673)
      ·
        refine ⟨22639367575183687235069755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30185823433578249646759673 22639367575183687235069755)
        ·
          refine ⟨33959051362775530852604633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22639367575183687235069755 33959051362775530852604633)
          ·
            refine ⟨25469288522081648139453475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33959051362775530852604633 25469288522081648139453475)
            ·
              refine ⟨38203932783122472209180213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25469288522081648139453475 38203932783122472209180213)
              ·
                refine ⟨3581618698417731769610645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38203932783122472209180213 3581618698417731769610645)
                ·
                  refine ⟨167888376488331176700499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3581618698417731769610645 167888376488331176700499)
                  ·
                    rfl

theorem cell23_2942653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_2942653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942653 prefixEnd_2942653 := by exact prefixLift 2942653
  have htrace : WordTrace (prefixWord ++ tailWord_2942653) baseStart_2942653 baseEnd_2942653 := by
    simpa [prefixWord, tailWord_2942653, baseEnd_2942653] using wordTrace_append hprefix tailTrace_2942653
  have hstable : (prefixWord ++ tailWord_2942653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942653).length < 2 ^ (prefixWord ++ tailWord_2942653).sum := by decide
  have hdescent : baseEnd_2942653 < baseStart_2942653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942674 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_2942674 : Nat := 118140960795 + 2942674 * 2 ^ 59
def prefixEnd_2942674 : Nat := 4983230072969 + 3 ^ 40 * 2942674 * 2
def baseEnd_2942674 : Nat := 503668723829575002713965

theorem tailTrace_2942674 : CollatzResearch.WordTrace tailWord_2942674 prefixEnd_2942674 503668723829575002713965 := by
  unfold tailWord_2942674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832034535300535388192769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71552092094134761035180717 26832034535300535388192769)
  ·
    refine ⟨20124025901475401541144577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26832034535300535388192769 20124025901475401541144577)
    ·
      refine ⟨15093019426106551155858433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20124025901475401541144577 15093019426106551155858433)
      ·
        refine ⟨11319764569579913366893825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15093019426106551155858433 11319764569579913366893825)
        ·
          refine ⟨8489823427184935025170369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11319764569579913366893825 8489823427184935025170369)
          ·
            refine ⟨6367367570388701268877777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8489823427184935025170369 6367367570388701268877777)
            ·
              refine ⟨4775525677791525951658333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6367367570388701268877777 4775525677791525951658333)
              ·
                refine ⟨1790822129171822231871875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4775525677791525951658333 1790822129171822231871875)
                ·
                  refine ⟨2686233193757733347807813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790822129171822231871875 2686233193757733347807813)
                  ·
                    refine ⟨503668723829575002713965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2686233193757733347807813 503668723829575002713965)
                    ·
                      rfl

theorem cell23_2942674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_2942674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942674 prefixEnd_2942674 := by exact prefixLift 2942674
  have htrace : WordTrace (prefixWord ++ tailWord_2942674) baseStart_2942674 baseEnd_2942674 := by
    simpa [prefixWord, tailWord_2942674, baseEnd_2942674] using wordTrace_append hprefix tailTrace_2942674
  have hstable : (prefixWord ++ tailWord_2942674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942674).length < 2 ^ (prefixWord ++ tailWord_2942674).sum := by decide
  have hdescent : baseEnd_2942674 < baseStart_2942674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942680 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_2942680 : Nat := 118140960795 + 2942680 * 2 ^ 59
def prefixEnd_2942680 : Nat := 4983230072969 + 3 ^ 40 * 2942680 * 2
def baseEnd_2942680 : Nat := 1511009252372651984666867

theorem tailTrace_2942680 : CollatzResearch.WordTrace tailWord_2942680 prefixEnd_2942680 1511009252372651984666867 := by
  unfold tailWord_2942680
  simp only [CollatzResearch.WordTrace]
  refine ⟨53664178489590202288744747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71552237986120269718326329 53664178489590202288744747)
  ·
    refine ⟨80496267734385303433117121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53664178489590202288744747 80496267734385303433117121)
    ·
      refine ⟨60372200800788977574837841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80496267734385303433117121 60372200800788977574837841)
      ·
        refine ⟨45279150600591733181128381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60372200800788977574837841 45279150600591733181128381)
        ·
          refine ⟨16979681475221899942923143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45279150600591733181128381 16979681475221899942923143)
          ·
            refine ⟨25469522212832849914384715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16979681475221899942923143 25469522212832849914384715)
            ·
              refine ⟨38204283319249274871577073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25469522212832849914384715 38204283319249274871577073)
              ·
                refine ⟨28653212489436956153682805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38204283319249274871577073 28653212489436956153682805)
                ·
                  refine ⟨2686238670884714639407763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28653212489436956153682805 2686238670884714639407763)
                  ·
                    refine ⟨4029358006327071959111645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686238670884714639407763 4029358006327071959111645)
                    ·
                      refine ⟨1511009252372651984666867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029358006327071959111645 1511009252372651984666867)
                      ·
                        rfl

theorem cell23_2942680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_2942680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942680 prefixEnd_2942680 := by exact prefixLift 2942680
  have htrace : WordTrace (prefixWord ++ tailWord_2942680) baseStart_2942680 baseEnd_2942680 := by
    simpa [prefixWord, tailWord_2942680, baseEnd_2942680] using wordTrace_append hprefix tailTrace_2942680
  have hstable : (prefixWord ++ tailWord_2942680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942680).length < 2 ^ (prefixWord ++ tailWord_2942680).sum := by decide
  have hdescent : baseEnd_2942680 < baseStart_2942680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942730 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_2942730 : Nat := 118140960795 + 2942730 * 2 ^ 59
def prefixEnd_2942730 : Nat := 4983230072969 + 3 ^ 40 * 2942730 * 2
def baseEnd_2942730 : Nat := 503678308801792263013879

theorem tailTrace_2942730 : CollatzResearch.WordTrace tailWord_2942730 prefixEnd_2942730 503678308801792263013879 := by
  unfold tailWord_2942730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832545157249815779202411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71553453752666175411206429 26832545157249815779202411)
  ·
    refine ⟨40248817735874723668803617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26832545157249815779202411 40248817735874723668803617)
    ·
      refine ⟨30186613301906042751602713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40248817735874723668803617 30186613301906042751602713)
      ·
        refine ⟨22639959976429532063702035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30186613301906042751602713 22639959976429532063702035)
        ·
          refine ⟨33959939964644298095553053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22639959976429532063702035 33959939964644298095553053)
          ·
            refine ⟨12734977486741611785832395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33959939964644298095553053 12734977486741611785832395)
            ·
              refine ⟨19102466230112417678748593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12734977486741611785832395 19102466230112417678748593)
              ·
                refine ⟨14326849672584313259061445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19102466230112417678748593 14326849672584313259061445)
                ·
                  refine ⟨2686284313609558736074021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14326849672584313259061445 2686284313609558736074021)
                  ·
                    refine ⟨503678308801792263013879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2686284313609558736074021 503678308801792263013879)
                    ·
                      rfl

theorem cell23_2942730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_2942730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942730 prefixEnd_2942730 := by exact prefixLift 2942730
  have htrace : WordTrace (prefixWord ++ tailWord_2942730) baseStart_2942730 baseEnd_2942730 := by
    simpa [prefixWord, tailWord_2942730, baseEnd_2942730] using wordTrace_append hprefix tailTrace_2942730
  have hstable : (prefixWord ++ tailWord_2942730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942730).length < 2 ^ (prefixWord ++ tailWord_2942730).sum := by decide
  have hdescent : baseEnd_2942730 < baseStart_2942730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942743 : List Nat := [1, 1, 3, 4, 2, 1, 11]
def baseStart_2942743 : Nat := 118140960795 + 2942743 * 2 ^ 59
def prefixEnd_2942743 : Nat := 4983230072969 + 3 ^ 40 * 2942743 * 2
def baseEnd_2942743 : Nat := 18654834588319570841717

theorem tailTrace_2942743 : CollatzResearch.WordTrace tailWord_2942743 prefixEnd_2942743 18654834588319570841717 := by
  unfold tailWord_2942743
  simp only [CollatzResearch.WordTrace]
  refine ⟨107330654777952166337032883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71553769851968110891355255 107330654777952166337032883)
  ·
    refine ⟨160995982166928249505549325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107330654777952166337032883 160995982166928249505549325)
    ·
      refine ⟨60373493312598093564580997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160995982166928249505549325 60373493312598093564580997)
      ·
        refine ⟨11320029996112142543358937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60373493312598093564580997 11320029996112142543358937)
        ·
          refine ⟨8490022497084106907519203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11320029996112142543358937 8490022497084106907519203)
          ·
            refine ⟨12735033745626160361278805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490022497084106907519203 12735033745626160361278805)
            ·
              refine ⟨18654834588319570841717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12735033745626160361278805 18654834588319570841717)
              ·
                rfl

theorem cell23_2942743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 11].length) (baseStart_2942743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942743 prefixEnd_2942743 := by exact prefixLift 2942743
  have htrace : WordTrace (prefixWord ++ tailWord_2942743) baseStart_2942743 baseEnd_2942743 := by
    simpa [prefixWord, tailWord_2942743, baseEnd_2942743] using wordTrace_append hprefix tailTrace_2942743
  have hstable : (prefixWord ++ tailWord_2942743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942743).length < 2 ^ (prefixWord ++ tailWord_2942743).sum := by decide
  have hdescent : baseEnd_2942743 < baseStart_2942743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942760 : List Nat := [2, 1, 5, 1, 1, 3, 2, 8]
def baseStart_2942760 : Nat := 118140960795 + 2942760 * 2 ^ 59
def prefixEnd_2942760 : Nat := 4983230072969 + 3 ^ 40 * 2942760 * 2
def baseEnd_2942760 : Nat := 55964827067593024876537

theorem tailTrace_2942760 : CollatzResearch.WordTrace tailWord_2942760 prefixEnd_2942760 55964827067593024876537 := by
  unfold tailWord_2942760
  simp only [CollatzResearch.WordTrace]
  refine ⟨53665637409445289120200867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71554183212593718826934489 53665637409445289120200867)
  ·
    refine ⟨80498456114167933680301301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53665637409445289120200867 80498456114167933680301301)
    ·
      refine ⟨7546730260703243782528247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80498456114167933680301301 7546730260703243782528247)
      ·
        refine ⟨11320095391054865673792371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546730260703243782528247 11320095391054865673792371)
        ·
          refine ⟨16980143086582298510688557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11320095391054865673792371 16980143086582298510688557)
          ·
            refine ⟨6367553657468361941508209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16980143086582298510688557 6367553657468361941508209)
            ·
              refine ⟨4775665243101271456131157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6367553657468361941508209 4775665243101271456131157)
              ·
                refine ⟨55964827067593024876537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4775665243101271456131157 55964827067593024876537)
                ·
                  rfl

theorem cell23_2942760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 8].length) (baseStart_2942760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942760 prefixEnd_2942760 := by exact prefixLift 2942760
  have htrace : WordTrace (prefixWord ++ tailWord_2942760) baseStart_2942760 baseEnd_2942760 := by
    simpa [prefixWord, tailWord_2942760, baseEnd_2942760] using wordTrace_append hprefix tailTrace_2942760
  have hstable : (prefixWord ++ tailWord_2942760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942760).length < 2 ^ (prefixWord ++ tailWord_2942760).sum := by decide
  have hdescent : baseEnd_2942760 < baseStart_2942760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942764 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_2942764 : Nat := 118140960795 + 2942764 * 2 ^ 59
def prefixEnd_2942764 : Nat := 4983230072969 + 3 ^ 40 * 2942764 * 2
def baseEnd_2942764 : Nat := 503684128249209885338827

theorem tailTrace_2942764 : CollatzResearch.WordTrace tailWord_2942764 prefixEnd_2942764 503684128249209885338827 := by
  unfold tailWord_2942764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53665710355438043461773673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71554280473917391282364897 53665710355438043461773673)
  ·
    refine ⟨40249282766578532596330255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53665710355438043461773673 40249282766578532596330255)
    ·
      refine ⟨60373924149867798894495383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40249282766578532596330255 60373924149867798894495383)
      ·
        refine ⟨90560886224801698341743075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60373924149867798894495383 90560886224801698341743075)
        ·
          refine ⟨135841329337202547512614613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90560886224801698341743075 135841329337202547512614613)
          ·
            refine ⟨3183781156340684707326905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135841329337202547512614613 3183781156340684707326905)
            ·
              refine ⟨2387835867255513530495179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183781156340684707326905 2387835867255513530495179)
              ·
                refine ⟨3581753800883270295742769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387835867255513530495179 3581753800883270295742769)
                ·
                  refine ⟨2686315350662452721807077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581753800883270295742769 2686315350662452721807077)
                  ·
                    refine ⟨503684128249209885338827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2686315350662452721807077 503684128249209885338827)
                    ·
                      rfl

theorem cell23_2942764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_2942764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942764 prefixEnd_2942764 := by exact prefixLift 2942764
  have htrace : WordTrace (prefixWord ++ tailWord_2942764) baseStart_2942764 baseEnd_2942764 := by
    simpa [prefixWord, tailWord_2942764, baseEnd_2942764] using wordTrace_append hprefix tailTrace_2942764
  have hstable : (prefixWord ++ tailWord_2942764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942764).length < 2 ^ (prefixWord ++ tailWord_2942764).sum := by decide
  have hdescent : baseEnd_2942764 < baseStart_2942764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942774 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2942774 : Nat := 118140960795 + 2942774 * 2 ^ 59
def prefixEnd_2942774 : Nat := 4983230072969 + 3 ^ 40 * 2942774 * 2
def baseEnd_2942774 : Nat := 1511057519554174616891435

theorem tailTrace_2942774 : CollatzResearch.WordTrace tailWord_2942774 prefixEnd_2942774 1511057519554174616891435 := by
  unfold tailWord_2942774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708236590052491164463211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71554523627226572420940917 6708236590052491164463211)
  ·
    refine ⟨10062354885078736746694817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6708236590052491164463211 10062354885078736746694817)
    ·
      refine ⟨7546766163809052560021113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10062354885078736746694817 7546766163809052560021113)
      ·
        refine ⟨5660074622856789420015835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546766163809052560021113 5660074622856789420015835)
        ·
          refine ⟨8490111934285184130023753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660074622856789420015835 8490111934285184130023753)
          ·
            refine ⟨6367583950713888097517815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8490111934285184130023753 6367583950713888097517815)
            ·
              refine ⟨9551375926070832146276723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367583950713888097517815 9551375926070832146276723)
              ·
                refine ⟨14327063889106248219415085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551375926070832146276723 14327063889106248219415085)
                ·
                  refine ⟨5372648958414843082280657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14327063889106248219415085 5372648958414843082280657)
                  ·
                    refine ⟨4029486718811132311710493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5372648958414843082280657 4029486718811132311710493)
                    ·
                      refine ⟨1511057519554174616891435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029486718811132311710493 1511057519554174616891435)
                      ·
                        rfl

theorem cell23_2942774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2942774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942774 prefixEnd_2942774 := by exact prefixLift 2942774
  have htrace : WordTrace (prefixWord ++ tailWord_2942774) baseStart_2942774 baseEnd_2942774 := by
    simpa [prefixWord, tailWord_2942774, baseEnd_2942774] using wordTrace_append hprefix tailTrace_2942774
  have hstable : (prefixWord ++ tailWord_2942774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942774).length < 2 ^ (prefixWord ++ tailWord_2942774).sum := by decide
  have hdescent : baseEnd_2942774 < baseStart_2942774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942804 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2942804 : Nat := 118140960795 + 2942804 * 2 ^ 59
def prefixEnd_2942804 : Nat := 4983230072969 + 3 ^ 40 * 2942804 * 2
def baseEnd_2942804 : Nat := 1511072923973809499516297

theorem tailTrace_2942804 : CollatzResearch.WordTrace tailWord_2942804 prefixEnd_2942804 1511072923973809499516297 := by
  unfold tailWord_2942804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53666439815365586877501733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71555253087154115836668977 53666439815365586877501733)
  ·
    refine ⟨10062457465381047539531575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53666439815365586877501733 10062457465381047539531575)
    ·
      refine ⟨15093686198071571309297363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10062457465381047539531575 15093686198071571309297363)
      ·
        refine ⟨22640529297107356963946045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15093686198071571309297363 22640529297107356963946045)
        ·
          refine ⟨8490198486415258861479767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22640529297107356963946045 8490198486415258861479767)
          ·
            refine ⟨12735297729622888292219651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490198486415258861479767 12735297729622888292219651)
            ·
              refine ⟨19102946594434332438329477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12735297729622888292219651 19102946594434332438329477)
              ·
                refine ⟨3581802486456437332186777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19102946594434332438329477 3581802486456437332186777)
                ·
                  refine ⟨2686351864842327999140083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581802486456437332186777 2686351864842327999140083)
                  ·
                    refine ⟨4029527797263491998710125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686351864842327999140083 4029527797263491998710125)
                    ·
                      refine ⟨1511072923973809499516297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029527797263491998710125 1511072923973809499516297)
                      ·
                        rfl

theorem cell23_2942804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2942804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942804 prefixEnd_2942804 := by exact prefixLift 2942804
  have htrace : WordTrace (prefixWord ++ tailWord_2942804) baseStart_2942804 baseEnd_2942804 := by
    simpa [prefixWord, tailWord_2942804, baseEnd_2942804] using wordTrace_append hprefix tailTrace_2942804
  have hstable : (prefixWord ++ tailWord_2942804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942804).length < 2 ^ (prefixWord ++ tailWord_2942804).sum := by decide
  have hdescent : baseEnd_2942804 < baseStart_2942804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942827 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 6, 2, 2]
def baseStart_2942827 : Nat := 118140960795 + 2942827 * 2 ^ 59
def prefixEnd_2942827 : Nat := 4983230072969 + 3 ^ 40 * 2942827 * 2
def baseEnd_2942827 : Nat := 1511084734028862909528691

theorem tailTrace_2942827 : CollatzResearch.WordTrace tailWord_2942827 prefixEnd_2942827 1511084734028862909528691 := by
  unfold tailWord_2942827
  simp only [CollatzResearch.WordTrace]
  refine ⟨107333718509647848683090735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71555812339765232455393823 107333718509647848683090735)
  ·
    refine ⟨161000577764471773024636103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107333718509647848683090735 161000577764471773024636103)
    ·
      refine ⟨241500866646707659536954155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161000577764471773024636103 241500866646707659536954155)
      ·
        refine ⟨362251299970061489305431233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241500866646707659536954155 362251299970061489305431233)
        ·
          refine ⟨271688474977546116979073425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362251299970061489305431233 271688474977546116979073425)
          ·
            refine ⟨203766356233159587734305069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271688474977546116979073425 203766356233159587734305069)
            ·
              refine ⟨76412383587434845400364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203766356233159587734305069 76412383587434845400364401)
              ·
                refine ⟨57309287690576134050273301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76412383587434845400364401 57309287690576134050273301)
                ·
                  refine ⟨2686372860495756283606561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57309287690576134050273301 2686372860495756283606561)
                  ·
                    refine ⟨2014779645371817212704921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686372860495756283606561 2014779645371817212704921)
                    ·
                      refine ⟨1511084734028862909528691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014779645371817212704921 1511084734028862909528691)
                      ·
                        rfl

theorem cell23_2942827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2, 2].length) (baseStart_2942827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942827 prefixEnd_2942827 := by exact prefixLift 2942827
  have htrace : WordTrace (prefixWord ++ tailWord_2942827) baseStart_2942827 baseEnd_2942827 := by
    simpa [prefixWord, tailWord_2942827, baseEnd_2942827] using wordTrace_append hprefix tailTrace_2942827
  have hstable : (prefixWord ++ tailWord_2942827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942827).length < 2 ^ (prefixWord ++ tailWord_2942827).sum := by decide
  have hdescent : baseEnd_2942827 < baseStart_2942827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_2942843 : Nat := 118140960795 + 2942843 * 2 ^ 59
def prefixEnd_2942843 : Nat := 4983230072969 + 3 ^ 40 * 2942843 * 2
def baseEnd_2942843 : Nat := 1511092949719334846928617

theorem tailTrace_2942843 : CollatzResearch.WordTrace tailWord_2942843 prefixEnd_2942843 1511092949719334846928617 := by
  unfold tailWord_2942843
  simp only [CollatzResearch.WordTrace]
  refine ⟨107334302077589883415673183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71556201385059922277115455 107334302077589883415673183)
  ·
    refine ⟨161001453116384825123509775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107334302077589883415673183 161001453116384825123509775)
    ·
      refine ⟨241502179674577237685264663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161001453116384825123509775 241502179674577237685264663)
      ·
        refine ⟨362253269511865856527896995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241502179674577237685264663 362253269511865856527896995)
        ·
          refine ⟨543379904267798784791845493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362253269511865856527896995 543379904267798784791845493)
          ·
            refine ⟨50941866025106136074235515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 543379904267798784791845493 50941866025106136074235515)
            ·
              refine ⟨76412799037659204111353273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50941866025106136074235515 76412799037659204111353273)
              ·
                refine ⟨57309599278244403083514955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76412799037659204111353273 57309599278244403083514955)
                ·
                  refine ⟨85964398917366604625272433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57309599278244403083514955 85964398917366604625272433)
                  ·
                    refine ⟨64473299188024953468954325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85964398917366604625272433 64473299188024953468954325)
                    ·
                      refine ⟨1511092949719334846928617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64473299188024953468954325 1511092949719334846928617)
                      ·
                        rfl

theorem cell23_2942843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_2942843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942843 prefixEnd_2942843 := by exact prefixLift 2942843
  have htrace : WordTrace (prefixWord ++ tailWord_2942843) baseStart_2942843 baseEnd_2942843 := by
    simpa [prefixWord, tailWord_2942843, baseEnd_2942843] using wordTrace_append hprefix tailTrace_2942843
  have hstable : (prefixWord ++ tailWord_2942843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942843).length < 2 ^ (prefixWord ++ tailWord_2942843).sum := by decide
  have hdescent : baseEnd_2942843 < baseStart_2942843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942877 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2942877 : Nat := 118140960795 + 2942877 * 2 ^ 59
def prefixEnd_2942877 : Nat := 4983230072969 + 3 ^ 40 * 2942877 * 2
def baseEnd_2942877 : Nat := 1511110408061587713903461

theorem tailTrace_2942877 : CollatzResearch.WordTrace tailWord_2942877 prefixEnd_2942877 1511110408061587713903461 := by
  unfold tailWord_2942877
  simp only [CollatzResearch.WordTrace]
  refine ⟨107335542159466707222410885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71557028106311138148273923 107335542159466707222410885)
  ·
    refine ⟨20125414154900007604202041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107335542159466707222410885 20125414154900007604202041)
    ·
      refine ⟨15094060616175005703151531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20125414154900007604202041 15094060616175005703151531)
      ·
        refine ⟨22641090924262508554727297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15094060616175005703151531 22641090924262508554727297)
        ·
          refine ⟨16980818193196881416045473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22641090924262508554727297 16980818193196881416045473)
          ·
            refine ⟨12735613644897661062034105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16980818193196881416045473 12735613644897661062034105)
            ·
              refine ⟨9551710233673245796525579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12735613644897661062034105 9551710233673245796525579)
              ·
                refine ⟨14327565350509868694788369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551710233673245796525579 14327565350509868694788369)
                ·
                  refine ⟨10745674012882401521091277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14327565350509868694788369 10745674012882401521091277)
                  ·
                    refine ⟨4029627754830900570409229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10745674012882401521091277 4029627754830900570409229)
                    ·
                      refine ⟨1511110408061587713903461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029627754830900570409229 1511110408061587713903461)
                      ·
                        rfl

theorem cell23_2942877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2942877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942877 prefixEnd_2942877 := by exact prefixLift 2942877
  have htrace : WordTrace (prefixWord ++ tailWord_2942877) baseStart_2942877 baseEnd_2942877 := by
    simpa [prefixWord, tailWord_2942877, baseEnd_2942877] using wordTrace_append hprefix tailTrace_2942877
  have hstable : (prefixWord ++ tailWord_2942877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942877).length < 2 ^ (prefixWord ++ tailWord_2942877).sum := by decide
  have hdescent : baseEnd_2942877 < baseStart_2942877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942917 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_2942917 : Nat := 118140960795 + 2942917 * 2 ^ 59
def prefixEnd_2942917 : Nat := 4983230072969 + 3 ^ 40 * 2942917 * 2
def baseEnd_2942917 : Nat := 1511130947287767557403277

theorem tailTrace_2942917 : CollatzResearch.WordTrace tailWord_2942917 prefixEnd_2942917 1511130947287767557403277 := by
  unfold tailWord_2942917
  simp only [CollatzResearch.WordTrace]
  refine ⟨107337001079321794053867005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71558000719547862702578003 107337001079321794053867005)
  ·
    refine ⟨40251375404745672770200127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107337001079321794053867005 40251375404745672770200127)
    ·
      refine ⟨60377063107118509155300191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40251375404745672770200127 60377063107118509155300191)
      ·
        refine ⟨90565594660677763732950287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60377063107118509155300191 90565594660677763732950287)
        ·
          refine ⟨135848391991016645599425431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90565594660677763732950287 135848391991016645599425431)
          ·
            refine ⟨203772587986524968399138147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135848391991016645599425431 203772587986524968399138147)
            ·
              refine ⟨305658881979787452598707221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203772587986524968399138147 305658881979787452598707221)
              ·
                refine ⟨14327760092802536840564401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305658881979787452598707221 14327760092802536840564401)
                ·
                  refine ⟨10745820069601902630423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14327760092802536840564401 10745820069601902630423301)
                  ·
                    refine ⟨2014841263050356743204369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10745820069601902630423301 2014841263050356743204369)
                    ·
                      refine ⟨1511130947287767557403277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014841263050356743204369 1511130947287767557403277)
                      ·
                        rfl

theorem cell23_2942917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_2942917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942917 prefixEnd_2942917 := by exact prefixLift 2942917
  have htrace : WordTrace (prefixWord ++ tailWord_2942917) baseStart_2942917 baseEnd_2942917 := by
    simpa [prefixWord, tailWord_2942917, baseEnd_2942917] using wordTrace_append hprefix tailTrace_2942917
  have hstable : (prefixWord ++ tailWord_2942917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942917).length < 2 ^ (prefixWord ++ tailWord_2942917).sum := by decide
  have hdescent : baseEnd_2942917 < baseStart_2942917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942954 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_2942954 : Nat := 118140960795 + 2942954 * 2 ^ 59
def prefixEnd_2942954 : Nat := 4983230072969 + 3 ^ 40 * 2942954 * 2
def baseEnd_2942954 : Nat := 1511149946071983912640607

theorem tailTrace_2942954 : CollatzResearch.WordTrace tailWord_2942954 prefixEnd_2942954 1511149946071983912640607 := by
  unfold tailWord_2942954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26834587645046937343240979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71558900386791832915309277 26834587645046937343240979)
  ·
    refine ⟨40251881467570406014861469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26834587645046937343240979 40251881467570406014861469)
    ·
      refine ⟨15094455550338902255573051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40251881467570406014861469 15094455550338902255573051)
      ·
        refine ⟨22641683325508353383359577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15094455550338902255573051 22641683325508353383359577)
        ·
          refine ⟨16981262494131265037519683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22641683325508353383359577 16981262494131265037519683)
          ·
            refine ⟨25471893741196897556279525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16981262494131265037519683 25471893741196897556279525)
            ·
              refine ⟨4775980076474418291802411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25471893741196897556279525 4775980076474418291802411)
              ·
                refine ⟨7163970114711627437703617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775980076474418291802411 7163970114711627437703617)
                ·
                  refine ⟨5372977586033720578277713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7163970114711627437703617 5372977586033720578277713)
                  ·
                    refine ⟨4029733189525290433708285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5372977586033720578277713 4029733189525290433708285)
                    ·
                      refine ⟨1511149946071983912640607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029733189525290433708285 1511149946071983912640607)
                      ·
                        rfl

theorem cell23_2942954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_2942954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942954 prefixEnd_2942954 := by exact prefixLift 2942954
  have htrace : WordTrace (prefixWord ++ tailWord_2942954) baseStart_2942954 baseEnd_2942954 := by
    simpa [prefixWord, tailWord_2942954, baseEnd_2942954] using wordTrace_append hprefix tailTrace_2942954
  have hstable : (prefixWord ++ tailWord_2942954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942954).length < 2 ^ (prefixWord ++ tailWord_2942954).sum := by decide
  have hdescent : baseEnd_2942954 < baseStart_2942954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942974 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2942974 : Nat := 118140960795 + 2942974 * 2 ^ 59
def prefixEnd_2942974 : Nat := 4983230072969 + 3 ^ 40 * 2942974 * 2
def baseEnd_2942974 : Nat := 167906690631674870487835

theorem tailTrace_2942974 : CollatzResearch.WordTrace tailWord_2942974 prefixEnd_2942974 167906690631674870487835 := by
  unfold tailWord_2942974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417385005014411598586497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71559386693410195192461317 13417385005014411598586497)
  ·
    refine ⟨10063038753760808698939873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13417385005014411598586497 10063038753760808698939873)
    ·
      refine ⟨7547279065320606524204905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10063038753760808698939873 7547279065320606524204905)
      ·
        refine ⟨5660459298990454893153679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7547279065320606524204905 5660459298990454893153679)
        ·
          refine ⟨8490688948485682339730519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660459298990454893153679 8490688948485682339730519)
          ·
            refine ⟨12736033422728523509595779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490688948485682339730519 12736033422728523509595779)
            ·
              refine ⟨19104050134092785264393669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12736033422728523509595779 19104050134092785264393669)
              ·
                refine ⟨3582009400142397237073813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19104050134092785264393669 3582009400142397237073813)
                ·
                  refine ⟨167906690631674870487835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3582009400142397237073813 167906690631674870487835)
                  ·
                    rfl

theorem cell23_2942974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2942974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942974 prefixEnd_2942974 := by exact prefixLift 2942974
  have htrace : WordTrace (prefixWord ++ tailWord_2942974) baseStart_2942974 baseEnd_2942974 := by
    simpa [prefixWord, tailWord_2942974, baseEnd_2942974] using wordTrace_append hprefix tailTrace_2942974
  have hstable : (prefixWord ++ tailWord_2942974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942974).length < 2 ^ (prefixWord ++ tailWord_2942974).sum := by decide
  have hdescent : baseEnd_2942974 < baseStart_2942974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942984 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2942984 : Nat := 118140960795 + 2942984 * 2 ^ 59
def prefixEnd_2942984 : Nat := 4983230072969 + 3 ^ 40 * 2942984 * 2
def baseEnd_2942984 : Nat := 1511165350491618795265469

theorem tailTrace_2942984 : CollatzResearch.WordTrace tailWord_2942984 prefixEnd_2942984 1511165350491618795265469 := by
  unfold tailWord_2942984
  simp only [CollatzResearch.WordTrace]
  refine ⟨53669722385039532248278003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71559629846719376331037337 53669722385039532248278003)
  ·
    refine ⟨80504583577559298372417005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53669722385039532248278003 80504583577559298372417005)
    ·
      refine ⟨30189218841584736889656377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80504583577559298372417005 30189218841584736889656377)
      ·
        refine ⟨22641914131188552667242283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30189218841584736889656377 22641914131188552667242283)
        ·
          refine ⟨33962871196782829000863425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22641914131188552667242283 33962871196782829000863425)
          ·
            refine ⟨25472153397587121750647569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33962871196782829000863425 25472153397587121750647569)
            ·
              refine ⟨19104115048190341312985677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25472153397587121750647569 19104115048190341312985677)
              ·
                refine ⟨7164043143071377992369629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19104115048190341312985677 7164043143071377992369629)
                ·
                  refine ⟨2686516178651766747138611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7164043143071377992369629 2686516178651766747138611)
                  ·
                    refine ⟨4029774267977650120707917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686516178651766747138611 4029774267977650120707917)
                    ·
                      refine ⟨1511165350491618795265469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029774267977650120707917 1511165350491618795265469)
                      ·
                        rfl

theorem cell23_2942984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2942984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2942984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2942984 prefixEnd_2942984 := by exact prefixLift 2942984
  have htrace : WordTrace (prefixWord ++ tailWord_2942984) baseStart_2942984 baseEnd_2942984 := by
    simpa [prefixWord, tailWord_2942984, baseEnd_2942984] using wordTrace_append hprefix tailTrace_2942984
  have hstable : (prefixWord ++ tailWord_2942984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942984).length < 2 ^ (prefixWord ++ tailWord_2942984).sum := by decide
  have hdescent : baseEnd_2942984 < baseStart_2942984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943007 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2943007 : Nat := 118140960795 + 2943007 * 2 ^ 59
def prefixEnd_2943007 : Nat := 4983230072969 + 3 ^ 40 * 2943007 * 2
def baseEnd_2943007 : Nat := 1511177160546672205277863

theorem tailTrace_2943007 : CollatzResearch.WordTrace tailWord_2943007 prefixEnd_2943007 1511177160546672205277863 := by
  unfold tailWord_2943007
  simp only [CollatzResearch.WordTrace]
  refine ⟨107340283648995739424643275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71560189099330492949762183 107340283648995739424643275)
  ·
    refine ⟨161010425473493609136964913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107340283648995739424643275 161010425473493609136964913)
    ·
      refine ⟨120757819105120206852723685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161010425473493609136964913 120757819105120206852723685)
      ·
        refine ⟨22642091082210038784885691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120757819105120206852723685 22642091082210038784885691)
        ·
          refine ⟨33963136623315058177328537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22642091082210038784885691 33963136623315058177328537)
          ·
            refine ⟨25472352467486293632996403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33963136623315058177328537 25472352467486293632996403)
            ·
              refine ⟨38208528701229440449494605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25472352467486293632996403 38208528701229440449494605)
              ·
                refine ⟨14328198262961040168560477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38208528701229440449494605 14328198262961040168560477)
                ·
                  refine ⟨5373074348610390063210179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14328198262961040168560477 5373074348610390063210179)
                  ·
                    refine ⟨8059611522915585094815269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5373074348610390063210179 8059611522915585094815269)
                    ·
                      refine ⟨1511177160546672205277863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8059611522915585094815269 1511177160546672205277863)
                      ·
                        rfl

theorem cell23_2943007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2943007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943007 prefixEnd_2943007 := by exact prefixLift 2943007
  have htrace : WordTrace (prefixWord ++ tailWord_2943007) baseStart_2943007 baseEnd_2943007 := by
    simpa [prefixWord, tailWord_2943007, baseEnd_2943007] using wordTrace_append hprefix tailTrace_2943007
  have hstable : (prefixWord ++ tailWord_2943007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943007).length < 2 ^ (prefixWord ++ tailWord_2943007).sum := by decide
  have hdescent : baseEnd_2943007 < baseStart_2943007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943018 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2943018 : Nat := 118140960795 + 2943018 * 2 ^ 59
def prefixEnd_2943018 : Nat := 4983230072969 + 3 ^ 40 * 2943018 * 2
def baseEnd_2943018 : Nat := 1511182808833871662240313

theorem tailTrace_2943018 : CollatzResearch.WordTrace tailWord_2943018 prefixEnd_2943018 1511182808833871662240313 := by
  unfold tailWord_2943018
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835171212988972075823427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71560456567970592202195805 26835171212988972075823427)
  ·
    refine ⟨40252756819483458113735141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835171212988972075823427 40252756819483458113735141)
    ·
      refine ⟨7547391903653148396325339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40252756819483458113735141 7547391903653148396325339)
      ·
        refine ⟨11321087855479722594488009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547391903653148396325339 11321087855479722594488009)
        ·
          refine ⟨8490815891609791945866007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11321087855479722594488009 8490815891609791945866007)
          ·
            refine ⟨12736223837414687918799011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490815891609791945866007 12736223837414687918799011)
            ·
              refine ⟨19104335756122031878198517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12736223837414687918799011 19104335756122031878198517)
              ·
                refine ⟨1791031477136440488581111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19104335756122031878198517 1791031477136440488581111)
                ·
                  refine ⟨2686547215704660732871667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791031477136440488581111 2686547215704660732871667)
                  ·
                    refine ⟨4029820823556991099307501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686547215704660732871667 4029820823556991099307501)
                    ·
                      refine ⟨1511182808833871662240313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029820823556991099307501 1511182808833871662240313)
                      ·
                        rfl

theorem cell23_2943018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2943018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943018 prefixEnd_2943018 := by exact prefixLift 2943018
  have htrace : WordTrace (prefixWord ++ tailWord_2943018) baseStart_2943018 baseEnd_2943018 := by
    simpa [prefixWord, tailWord_2943018, baseEnd_2943018] using wordTrace_append hprefix tailTrace_2943018
  have hstable : (prefixWord ++ tailWord_2943018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943018).length < 2 ^ (prefixWord ++ tailWord_2943018).sum := by decide
  have hdescent : baseEnd_2943018 < baseStart_2943018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943024 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_2943024 : Nat := 118140960795 + 2943024 * 2 ^ 59
def prefixEnd_2943024 : Nat := 4983230072969 + 3 ^ 40 * 2943024 * 2
def baseEnd_2943024 : Nat := 1511185889717798638765285

theorem tailTrace_2943024 : CollatzResearch.WordTrace tailWord_2943024 prefixEnd_2943024 1511185889717798638765285 := by
  unfold tailWord_2943024
  simp only [CollatzResearch.WordTrace]
  refine ⟨53670451844967075664006063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71560602459956100885341417 53670451844967075664006063)
  ·
    refine ⟨80505677767450613496009095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53670451844967075664006063 80505677767450613496009095)
    ·
      refine ⟨120758516651175920244013643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80505677767450613496009095 120758516651175920244013643)
      ·
        refine ⟨181137774976763880366020465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120758516651175920244013643 181137774976763880366020465)
        ·
          refine ⟨135853331232572910274515349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181137774976763880366020465 135853331232572910274515349)
          ·
            refine ⟨6368124901526855169117907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135853331232572910274515349 6368124901526855169117907)
            ·
              refine ⟨9552187352290282753676861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368124901526855169117907 9552187352290282753676861)
              ·
                refine ⟨3582070257108856032628823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9552187352290282753676861 3582070257108856032628823)
                ·
                  refine ⟨5373105385663284048943235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582070257108856032628823 5373105385663284048943235)
                  ·
                    refine ⟨8059658078494926073414853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5373105385663284048943235 8059658078494926073414853)
                    ·
                      refine ⟨1511185889717798638765285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8059658078494926073414853 1511185889717798638765285)
                      ·
                        rfl

theorem cell23_2943024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_2943024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943024 prefixEnd_2943024 := by exact prefixLift 2943024
  have htrace : WordTrace (prefixWord ++ tailWord_2943024) baseStart_2943024 baseEnd_2943024 := by
    simpa [prefixWord, tailWord_2943024, baseEnd_2943024] using wordTrace_append hprefix tailTrace_2943024
  have hstable : (prefixWord ++ tailWord_2943024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943024).length < 2 ^ (prefixWord ++ tailWord_2943024).sum := by decide
  have hdescent : baseEnd_2943024 < baseStart_2943024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943037 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2943037 : Nat := 118140960795 + 2943037 * 2 ^ 59
def prefixEnd_2943037 : Nat := 4983230072969 + 3 ^ 40 * 2943037 * 2
def baseEnd_2943037 : Nat := 1511192564966307087902725

theorem tailTrace_2943037 : CollatzResearch.WordTrace tailWord_2943037 prefixEnd_2943037 1511192564966307087902725 := by
  unfold tailWord_2943037
  simp only [CollatzResearch.WordTrace]
  refine ⟨107341377838887054548235365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71560918559258036365490243 107341377838887054548235365)
  ·
    refine ⟨20126508344791322727794131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107341377838887054548235365 20126508344791322727794131)
    ·
      refine ⟨30189762517186984091691197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20126508344791322727794131 30189762517186984091691197)
      ·
        refine ⟨11321160943945119034384199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30189762517186984091691197 11321160943945119034384199)
        ·
          refine ⟨16981741415917678551576299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11321160943945119034384199 16981741415917678551576299)
          ·
            refine ⟨25472612123876517827364449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16981741415917678551576299 25472612123876517827364449)
            ·
              refine ⟨19104459092907388370523337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25472612123876517827364449 19104459092907388370523337)
              ·
                refine ⟨14328344319680541277892503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19104459092907388370523337 14328344319680541277892503)
                ·
                  refine ⟨21492516479520811916838755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14328344319680541277892503 21492516479520811916838755)
                  ·
                    refine ⟨32238774719281217875258133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21492516479520811916838755 32238774719281217875258133)
                    ·
                      refine ⟨1511192564966307087902725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32238774719281217875258133 1511192564966307087902725)
                      ·
                        rfl

theorem cell23_2943037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2943037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943037 prefixEnd_2943037 := by exact prefixLift 2943037
  have htrace : WordTrace (prefixWord ++ tailWord_2943037) baseStart_2943037 baseEnd_2943037 := by
    simpa [prefixWord, tailWord_2943037, baseEnd_2943037] using wordTrace_append hprefix tailTrace_2943037
  have hstable : (prefixWord ++ tailWord_2943037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943037).length < 2 ^ (prefixWord ++ tailWord_2943037).sum := by decide
  have hdescent : baseEnd_2943037 < baseStart_2943037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943054 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2943054 : Nat := 118140960795 + 2943054 * 2 ^ 59
def prefixEnd_2943054 : Nat := 4983230072969 + 3 ^ 40 * 2943054 * 2
def baseEnd_2943054 : Nat := 1511201294137433521390147

theorem tailTrace_2943054 : CollatzResearch.WordTrace tailWord_2943054 prefixEnd_2943054 1511201294137433521390147 := by
  unfold tailWord_2943054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417749734978183306450527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71561331919883644301069477 13417749734978183306450527)
  ·
    refine ⟨20126624602467274959675791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13417749734978183306450527 20126624602467274959675791)
    ·
      refine ⟨30189936903700912439513687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20126624602467274959675791 30189936903700912439513687)
      ·
        refine ⟨45284905355551368659270531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30189936903700912439513687 45284905355551368659270531)
        ·
          refine ⟨67927358033327052988905797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45284905355551368659270531 67927358033327052988905797)
          ·
            refine ⟨12736379631248822435419837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67927358033327052988905797 12736379631248822435419837)
            ·
              refine ⟨4776142361718308413282439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12736379631248822435419837 4776142361718308413282439)
              ·
                refine ⟨7164213542577462619923659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776142361718308413282439 7164213542577462619923659)
                ·
                  refine ⟨10746320313866193929885489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7164213542577462619923659 10746320313866193929885489)
                  ·
                    refine ⟨8059740235399645447414117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10746320313866193929885489 8059740235399645447414117)
                    ·
                      refine ⟨1511201294137433521390147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8059740235399645447414117 1511201294137433521390147)
                      ·
                        rfl

theorem cell23_2943054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2943054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943054 prefixEnd_2943054 := by exact prefixLift 2943054
  have htrace : WordTrace (prefixWord ++ tailWord_2943054) baseStart_2943054 baseEnd_2943054 := by
    simpa [prefixWord, tailWord_2943054, baseEnd_2943054] using wordTrace_append hprefix tailTrace_2943054
  have hstable : (prefixWord ++ tailWord_2943054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943054).length < 2 ^ (prefixWord ++ tailWord_2943054).sum := by decide
  have hdescent : baseEnd_2943054 < baseStart_2943054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943061 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2943061 : Nat := 118140960795 + 2943061 * 2 ^ 59
def prefixEnd_2943061 : Nat := 4983230072969 + 3 ^ 40 * 2943061 * 2
def baseEnd_2943061 : Nat := 1511204888502014994002615

theorem tailTrace_2943061 : CollatzResearch.WordTrace tailWord_2943061 prefixEnd_2943061 1511204888502014994002615 := by
  unfold tailWord_2943061
  simp only [CollatzResearch.WordTrace]
  refine ⟨107342253190800106647109037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71561502127200071098072691 107342253190800106647109037)
  ·
    refine ⟨40253344946550039992665889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107342253190800106647109037 40253344946550039992665889)
    ·
      refine ⟨30190008709912529994499417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40253344946550039992665889 30190008709912529994499417)
      ·
        refine ⟨22642506532434397495874563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30190008709912529994499417 22642506532434397495874563)
        ·
          refine ⟨33963759798651596243811845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22642506532434397495874563 33963759798651596243811845)
          ·
            refine ⟨6368204962247174295714721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33963759798651596243811845 6368204962247174295714721)
            ·
              refine ⟨4776153721685380721786041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6368204962247174295714721 4776153721685380721786041)
              ·
                refine ⟨3582115291264035541339531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4776153721685380721786041 3582115291264035541339531)
                ·
                  refine ⟨5373172936896053312009297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582115291264035541339531 5373172936896053312009297)
                  ·
                    refine ⟨4029879702672039984006973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5373172936896053312009297 4029879702672039984006973)
                    ·
                      refine ⟨1511204888502014994002615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4029879702672039984006973 1511204888502014994002615)
                      ·
                        rfl

theorem cell23_2943061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2943061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943061 prefixEnd_2943061 := by exact prefixLift 2943061
  have htrace : WordTrace (prefixWord ++ tailWord_2943061) baseStart_2943061 baseEnd_2943061 := by
    simpa [prefixWord, tailWord_2943061, baseEnd_2943061] using wordTrace_append hprefix tailTrace_2943061
  have hstable : (prefixWord ++ tailWord_2943061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943061).length < 2 ^ (prefixWord ++ tailWord_2943061).sum := by decide
  have hdescent : baseEnd_2943061 < baseStart_2943061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943064 : List Nat := [2, 1, 2, 2, 1, 6, 2, 7]
def baseStart_2943064 : Nat := 118140960795 + 2943064 * 2 ^ 59
def prefixEnd_2943064 : Nat := 4983230072969 + 3 ^ 40 * 2943064 * 2
def baseEnd_2943064 : Nat := 55970608479406610454263

theorem tailTrace_2943064 : CollatzResearch.WordTrace tailWord_2943064 prefixEnd_2943064 55970608479406610454263 := by
  unfold tailWord_2943064
  simp only [CollatzResearch.WordTrace]
  refine ⟨53671181304894619079734123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71561575073192825439645497 53671181304894619079734123)
  ·
    refine ⟨80506771957341928619601185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53671181304894619079734123 80506771957341928619601185)
    ·
      refine ⟨60380078968006446464700889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80506771957341928619601185 60380078968006446464700889)
      ·
        refine ⟨45285059226004834848525667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60380078968006446464700889 45285059226004834848525667)
        ·
          refine ⟨67927588839007252272788501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45285059226004834848525667 67927588839007252272788501)
          ·
            refine ⟨3184105726828464950286961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67927588839007252272788501 3184105726828464950286961)
            ·
              refine ⟨2388079295121348712715221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184105726828464950286961 2388079295121348712715221)
              ·
                refine ⟨55970608479406610454263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2388079295121348712715221 55970608479406610454263)
                ·
                  rfl

theorem cell23_2943064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 7].length) (baseStart_2943064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943064 prefixEnd_2943064 := by exact prefixLift 2943064
  have htrace : WordTrace (prefixWord ++ tailWord_2943064) baseStart_2943064 baseEnd_2943064 := by
    simpa [prefixWord, tailWord_2943064, baseEnd_2943064] using wordTrace_append hprefix tailTrace_2943064
  have hstable : (prefixWord ++ tailWord_2943064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943064).length < 2 ^ (prefixWord ++ tailWord_2943064).sum := by decide
  have hdescent : baseEnd_2943064 < baseStart_2943064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943118 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2943118 : Nat := 118140960795 + 2943118 * 2 ^ 59
def prefixEnd_2943118 : Nat := 4983230072969 + 3 ^ 40 * 2943118 * 2
def baseEnd_2943118 : Nat := 1511234156899321270989853

theorem tailTrace_2943118 : CollatzResearch.WordTrace tailWord_2943118 prefixEnd_2943118 1511234156899321270989853 := by
  unfold tailWord_2943118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418041518949200672741751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71562888101062403587956005 13418041518949200672741751)
  ·
    refine ⟨20127062278423801009112627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13418041518949200672741751 20127062278423801009112627)
    ·
      refine ⟨30190593417635701513668941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20127062278423801009112627 30190593417635701513668941)
      ·
        refine ⟨11321472531613388067625853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30190593417635701513668941 11321472531613388067625853)
        ·
          refine ⟨4245552199355020525359695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11321472531613388067625853 4245552199355020525359695)
          ·
            refine ⟨6368328299032530788039543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245552199355020525359695 6368328299032530788039543)
            ·
              refine ⟨9552492448548796182059315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368328299032530788039543 9552492448548796182059315)
              ·
                refine ⟨14328738672823194273088973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552492448548796182059315 14328738672823194273088973)
                ·
                  refine ⟨5373277002308697852408365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14328738672823194273088973 5373277002308697852408365)
                  ·
                    refine ⟨2014978875865761694653137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5373277002308697852408365 2014978875865761694653137)
                    ·
                      refine ⟨1511234156899321270989853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014978875865761694653137 1511234156899321270989853)
                      ·
                        rfl

theorem cell23_2943118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2943118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943118 prefixEnd_2943118 := by exact prefixLift 2943118
  have htrace : WordTrace (prefixWord ++ tailWord_2943118) baseStart_2943118 baseEnd_2943118 := by
    simpa [prefixWord, tailWord_2943118, baseEnd_2943118] using wordTrace_append hprefix tailTrace_2943118
  have hstable : (prefixWord ++ tailWord_2943118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943118).length < 2 ^ (prefixWord ++ tailWord_2943118).sum := by decide
  have hdescent : baseEnd_2943118 < baseStart_2943118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943135 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2943135 : Nat := 118140960795 + 2943135 * 2 ^ 59
def prefixEnd_2943135 : Nat := 4983230072969 + 3 ^ 40 * 2943135 * 2
def baseEnd_2943135 : Nat := 1511242886070447704477275

theorem tailTrace_2943135 : CollatzResearch.WordTrace tailWord_2943135 prefixEnd_2943135 1511242886070447704477275 := by
  unfold tailWord_2943135
  simp only [CollatzResearch.WordTrace]
  refine ⟨107344952192532017285302859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71563301461688011523535239 107344952192532017285302859)
  ·
    refine ⟨161017428288798025927954289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107344952192532017285302859 161017428288798025927954289)
    ·
      refine ⟨120763071216598519445965717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161017428288798025927954289 120763071216598519445965717)
      ·
        refine ⟨5660768963278055599029643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120763071216598519445965717 5660768963278055599029643)
        ·
          refine ⟨8491153444917083398544465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660768963278055599029643 8491153444917083398544465)
          ·
            refine ⟨6368365083687812548908349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491153444917083398544465 6368365083687812548908349)
            ·
              refine ⟨2388136906382929705840631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6368365083687812548908349 2388136906382929705840631)
              ·
                refine ⟨3582205359574394558760947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388136906382929705840631 3582205359574394558760947)
                ·
                  refine ⟨5373308039361591838141421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582205359574394558760947 5373308039361591838141421)
                  ·
                    refine ⟨2014990514760596939303033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5373308039361591838141421 2014990514760596939303033)
                    ·
                      refine ⟨1511242886070447704477275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2014990514760596939303033 1511242886070447704477275)
                      ·
                        rfl

theorem cell23_2943135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2943135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943135 prefixEnd_2943135 := by exact prefixLift 2943135
  have htrace : WordTrace (prefixWord ++ tailWord_2943135) baseStart_2943135 baseEnd_2943135 := by
    simpa [prefixWord, tailWord_2943135, baseEnd_2943135] using wordTrace_append hprefix tailTrace_2943135
  have hstable : (prefixWord ++ tailWord_2943135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943135).length < 2 ^ (prefixWord ++ tailWord_2943135).sum := by decide
  have hdescent : baseEnd_2943135 < baseStart_2943135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943167 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 7]
def baseStart_2943167 : Nat := 118140960795 + 2943167 * 2 ^ 59
def prefixEnd_2943167 : Nat := 4983230072969 + 3 ^ 40 * 2943167 * 2
def baseEnd_2943167 : Nat := 503753105817130526425709

theorem tailTrace_2943167 : CollatzResearch.WordTrace tailWord_2943167 prefixEnd_2943167 503753105817130526425709 := by
  unfold tailWord_2943167
  simp only [CollatzResearch.WordTrace]
  refine ⟨107346119328416086750467755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71564079552277391166978503 107346119328416086750467755)
  ·
    refine ⟨161019178992624130125701633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107346119328416086750467755 161019178992624130125701633)
    ·
      refine ⟨120764384244468097594276225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161019178992624130125701633 120764384244468097594276225)
      ·
        refine ⟨90573288183351073195707169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120764384244468097594276225 90573288183351073195707169)
        ·
          refine ⟨67929966137513304896780377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90573288183351073195707169 67929966137513304896780377)
          ·
            refine ⟨50947474603134978672585283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67929966137513304896780377 50947474603134978672585283)
            ·
              refine ⟨76421211904702468008877925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50947474603134978672585283 76421211904702468008877925)
              ·
                refine ⟨14328977232131712751664611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76421211904702468008877925 14328977232131712751664611)
                ·
                  refine ⟨21493465848197569127496917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14328977232131712751664611 21493465848197569127496917)
                  ·
                    refine ⟨503753105817130526425709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21493465848197569127496917 503753105817130526425709)
                    ·
                      rfl

theorem cell23_2943167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_2943167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943167 prefixEnd_2943167 := by exact prefixLift 2943167
  have htrace : WordTrace (prefixWord ++ tailWord_2943167) baseStart_2943167 baseEnd_2943167 := by
    simpa [prefixWord, tailWord_2943167, baseEnd_2943167] using wordTrace_append hprefix tailTrace_2943167
  have hstable : (prefixWord ++ tailWord_2943167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943167).length < 2 ^ (prefixWord ++ tailWord_2943167).sum := by decide
  have hdescent : baseEnd_2943167 < baseStart_2943167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943177 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2943177 : Nat := 118140960795 + 2943177 * 2 ^ 59
def prefixEnd_2943177 : Nat := 4983230072969 + 3 ^ 40 * 2943177 * 2
def baseEnd_2943177 : Nat := 1511264452257936540152081

theorem tailTrace_2943177 : CollatzResearch.WordTrace tailWord_2943177 prefixEnd_2943177 1511264452257936540152081 := by
  unfold tailWord_2943177
  simp only [CollatzResearch.WordTrace]
  refine ⟨107346484058379858458331785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71564322705586572305554523 107346484058379858458331785)
  ·
    refine ⟨80509863043784893843748839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107346484058379858458331785 80509863043784893843748839)
    ·
      refine ⟨120764794565677340765623259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80509863043784893843748839 120764794565677340765623259)
      ·
        refine ⟨181147191848516011148434889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120764794565677340765623259 181147191848516011148434889)
        ·
          refine ⟨135860393886387008361326167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181147191848516011148434889 135860393886387008361326167)
          ·
            refine ⟨203790590829580512541989251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135860393886387008361326167 203790590829580512541989251)
            ·
              refine ⟨305685886244370768812983877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203790590829580512541989251 305685886244370768812983877)
              ·
                refine ⟨57316103670819519152434477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305685886244370768812983877 57316103670819519152434477)
                ·
                  refine ⟨21493538876557319682162929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57316103670819519152434477 21493538876557319682162929)
                  ·
                    refine ⟨16120154157417989761622197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21493538876557319682162929 16120154157417989761622197)
                    ·
                      refine ⟨1511264452257936540152081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16120154157417989761622197 1511264452257936540152081)
                      ·
                        rfl

theorem cell23_2943177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2943177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943177 prefixEnd_2943177 := by exact prefixLift 2943177
  have htrace : WordTrace (prefixWord ++ tailWord_2943177) baseStart_2943177 baseEnd_2943177 := by
    simpa [prefixWord, tailWord_2943177, baseEnd_2943177] using wordTrace_append hprefix tailTrace_2943177
  have hstable : (prefixWord ++ tailWord_2943177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943177).length < 2 ^ (prefixWord ++ tailWord_2943177).sum := by decide
  have hdescent : baseEnd_2943177 < baseStart_2943177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943204 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2943204 : Nat := 118140960795 + 2943204 * 2 ^ 59
def prefixEnd_2943204 : Nat := 4983230072969 + 3 ^ 40 * 2943204 * 2
def baseEnd_2943204 : Nat := 1511278316235607934514457

theorem tailTrace_2943204 : CollatzResearch.WordTrace tailWord_2943204 prefixEnd_2943204 1511278316235607934514457 := by
  unfold tailWord_2943204
  simp only [CollatzResearch.WordTrace]
  refine ⟨53673734414641021034782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71564979219521361379709777 53673734414641021034782333)
  ·
    refine ⟨20127650405490382888043375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53673734414641021034782333 20127650405490382888043375)
    ·
      refine ⟨30191475608235574332065063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20127650405490382888043375 30191475608235574332065063)
      ·
        refine ⟨45287213412353361498097595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30191475608235574332065063 45287213412353361498097595)
        ·
          refine ⟨67930820118530042247146393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45287213412353361498097595 67930820118530042247146393)
          ·
            refine ⟨50948115088897531685359795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67930820118530042247146393 50948115088897531685359795)
            ·
              refine ⟨76422172633346297528039693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50948115088897531685359795 76422172633346297528039693)
              ·
                refine ⟨28658314737504861573014885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76422172633346297528039693 28658314737504861573014885)
                ·
                  refine ⟨5373434013282161544940291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28658314737504861573014885 5373434013282161544940291)
                  ·
                    refine ⟨8060151019923242317410437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5373434013282161544940291 8060151019923242317410437)
                    ·
                      refine ⟨1511278316235607934514457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8060151019923242317410437 1511278316235607934514457)
                      ·
                        rfl

theorem cell23_2943204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2943204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943204 prefixEnd_2943204 := by exact prefixLift 2943204
  have htrace : WordTrace (prefixWord ++ tailWord_2943204) baseStart_2943204 baseEnd_2943204 := by
    simpa [prefixWord, tailWord_2943204, baseEnd_2943204] using wordTrace_append hprefix tailTrace_2943204
  have hstable : (prefixWord ++ tailWord_2943204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943204).length < 2 ^ (prefixWord ++ tailWord_2943204).sum := by decide
  have hdescent : baseEnd_2943204 < baseStart_2943204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943258 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_2943258 : Nat := 118140960795 + 2943258 * 2 ^ 59
def prefixEnd_2943258 : Nat := 4983230072969 + 3 ^ 40 * 2943258 * 2
def baseEnd_2943258 : Nat := 1511306044190950723239209

theorem tailTrace_2943258 : CollatzResearch.WordTrace tailWord_2943258 prefixEnd_2943258 1511306044190950723239209 := by
  unfold tailWord_2943258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26837359592771602323007607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71566292247390939528020285 26837359592771602323007607)
  ·
    refine ⟨40256039389157403484511411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26837359592771602323007607 40256039389157403484511411)
    ·
      refine ⟨60384059083736105226767117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40256039389157403484511411 60384059083736105226767117)
      ·
        refine ⟨22644022156401039460037669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60384059083736105226767117 22644022156401039460037669)
        ·
          refine ⟨4245754154325194898757063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22644022156401039460037669 4245754154325194898757063)
          ·
            refine ⟨6368631231487792348135595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245754154325194898757063 6368631231487792348135595)
            ·
              refine ⟨9552946847231688522203393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368631231487792348135595 9552946847231688522203393)
              ·
                refine ⟨7164710135423766391652545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9552946847231688522203393 7164710135423766391652545)
                ·
                  refine ⟨5373532601567824793739409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7164710135423766391652545 5373532601567824793739409)
                  ·
                    refine ⟨4030149451175868595304557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5373532601567824793739409 4030149451175868595304557)
                    ·
                      refine ⟨1511306044190950723239209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4030149451175868595304557 1511306044190950723239209)
                      ·
                        rfl

theorem cell23_2943258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_2943258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943258 prefixEnd_2943258 := by exact prefixLift 2943258
  have htrace : WordTrace (prefixWord ++ tailWord_2943258) baseStart_2943258 baseEnd_2943258 := by
    simpa [prefixWord, tailWord_2943258, baseEnd_2943258] using wordTrace_append hprefix tailTrace_2943258
  have hstable : (prefixWord ++ tailWord_2943258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943258).length < 2 ^ (prefixWord ++ tailWord_2943258).sum := by decide
  have hdescent : baseEnd_2943258 < baseStart_2943258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943304 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_2943304 : Nat := 118140960795 + 2943304 * 2 ^ 59
def prefixEnd_2943304 : Nat := 4983230072969 + 3 ^ 40 * 2943304 * 2
def baseEnd_2943304 : Nat := 503776554767019181087999

theorem tailTrace_2943304 : CollatzResearch.WordTrace tailWord_2943304 prefixEnd_2943304 503776554767019181087999 := by
  unfold tailWord_2943304
  simp only [CollatzResearch.WordTrace]
  refine ⟨53675558064459879574102483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71567410752613172765469977 53675558064459879574102483)
  ·
    refine ⟨80513337096689819361153725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53675558064459879574102483 80513337096689819361153725)
    ·
      refine ⟨30192501411258682260432647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80513337096689819361153725 30192501411258682260432647)
      ·
        refine ⟨45288752116888023390648971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30192501411258682260432647 45288752116888023390648971)
        ·
          refine ⟨67933128175332035085973457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45288752116888023390648971 67933128175332035085973457)
          ·
            refine ⟨50949846131499026314480093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67933128175332035085973457 50949846131499026314480093)
            ·
              refine ⟨19106192299312134867930035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50949846131499026314480093 19106192299312134867930035)
              ·
                refine ⟨28659288448968202301895053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19106192299312134867930035 28659288448968202301895053)
                ·
                  refine ⟨10747233168363075863210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28659288448968202301895053 10747233168363075863210645)
                  ·
                    refine ⟨503776554767019181087999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10747233168363075863210645 503776554767019181087999)
                    ·
                      rfl

theorem cell23_2943304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_2943304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943304 prefixEnd_2943304 := by exact prefixLift 2943304
  have htrace : WordTrace (prefixWord ++ tailWord_2943304) baseStart_2943304 baseEnd_2943304 := by
    simpa [prefixWord, tailWord_2943304, baseEnd_2943304] using wordTrace_append hprefix tailTrace_2943304
  have hstable : (prefixWord ++ tailWord_2943304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943304).length < 2 ^ (prefixWord ++ tailWord_2943304).sum := by decide
  have hdescent : baseEnd_2943304 < baseStart_2943304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943308 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_2943308 : Nat := 118140960795 + 2943308 * 2 ^ 59
def prefixEnd_2943308 : Nat := 4983230072969 + 3 ^ 40 * 2943308 * 2
def baseEnd_2943308 : Nat := 503777239407891842537993

theorem tailTrace_2943308 : CollatzResearch.WordTrace tailWord_2943308 prefixEnd_2943308 503777239407891842537993 := by
  unfold tailWord_2943308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53675631010452633915675289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71567508013936845220900385 53675631010452633915675289)
  ·
    refine ⟨40256723257839475436756467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53675631010452633915675289 40256723257839475436756467)
    ·
      refine ⟨60385084886759213155134701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40256723257839475436756467 60385084886759213155134701)
      ·
        refine ⟨22644406832534704933175513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60385084886759213155134701 22644406832534704933175513)
        ·
          refine ⟨16983305124401028699881635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22644406832534704933175513 16983305124401028699881635)
          ·
            refine ⟨25474957686601543049822453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16983305124401028699881635 25474957686601543049822453)
            ·
              refine ⟨2388277283118894660920855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25474957686601543049822453 2388277283118894660920855)
              ·
                refine ⟨3582415924678341991381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388277283118894660920855 3582415924678341991381283)
                ·
                  refine ⟨5373623887017512987071925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582415924678341991381283 5373623887017512987071925)
                  ·
                    refine ⟨503777239407891842537993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5373623887017512987071925 503777239407891842537993)
                    ·
                      rfl

theorem cell23_2943308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_2943308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943308 prefixEnd_2943308 := by exact prefixLift 2943308
  have htrace : WordTrace (prefixWord ++ tailWord_2943308) baseStart_2943308 baseEnd_2943308 := by
    simpa [prefixWord, tailWord_2943308, baseEnd_2943308] using wordTrace_append hprefix tailTrace_2943308
  have hstable : (prefixWord ++ tailWord_2943308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943308).length < 2 ^ (prefixWord ++ tailWord_2943308).sum := by decide
  have hdescent : baseEnd_2943308 < baseStart_2943308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943331 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2943331 : Nat := 118140960795 + 2943331 * 2 ^ 59
def prefixEnd_2943331 : Nat := 4983230072969 + 3 ^ 40 * 2943331 * 2
def baseEnd_2943331 : Nat := 1511343528278728937626373

theorem tailTrace_2943331 : CollatzResearch.WordTrace tailWord_2943331 prefixEnd_2943331 1511343528278728937626373 := by
  unfold tailWord_2943331
  simp only [CollatzResearch.WordTrace]
  refine ⟨107352100899821942759437847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71568067266547961839625231 107352100899821942759437847)
  ·
    refine ⟨161028151349732914139156771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107352100899821942759437847 161028151349732914139156771)
    ·
      refine ⟨241542227024599371208735157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161028151349732914139156771 241542227024599371208735157)
      ·
        refine ⟨22644583783556191050818921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241542227024599371208735157 22644583783556191050818921)
        ·
          refine ⟨16983437837667143288114191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22644583783556191050818921 16983437837667143288114191)
          ·
            refine ⟨25475156756500714932171287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16983437837667143288114191 25475156756500714932171287)
            ·
              refine ⟨38212735134751072398256931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25475156756500714932171287 38212735134751072398256931)
              ·
                refine ⟨57319102702126608597385397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38212735134751072398256931 57319102702126608597385397)
                ·
                  refine ⟨5373665878324369556004881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57319102702126608597385397 5373665878324369556004881)
                  ·
                    refine ⟨4030249408743277167003661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5373665878324369556004881 4030249408743277167003661)
                    ·
                      refine ⟨1511343528278728937626373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4030249408743277167003661 1511343528278728937626373)
                      ·
                        rfl

theorem cell23_2943331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2943331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943331 prefixEnd_2943331 := by exact prefixLift 2943331
  have htrace : WordTrace (prefixWord ++ tailWord_2943331) baseStart_2943331 baseEnd_2943331 := by
    simpa [prefixWord, tailWord_2943331, baseEnd_2943331] using wordTrace_append hprefix tailTrace_2943331
  have hstable : (prefixWord ++ tailWord_2943331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943331).length < 2 ^ (prefixWord ++ tailWord_2943331).sum := by decide
  have hdescent : baseEnd_2943331 < baseStart_2943331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943338 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2943338 : Nat := 118140960795 + 2943338 * 2 ^ 59
def prefixEnd_2943338 : Nat := 4983230072969 + 3 ^ 40 * 2943338 * 2
def baseEnd_2943338 : Nat := 503782374214436803412947

theorem tailTrace_2943338 : CollatzResearch.WordTrace tailWord_2943338 prefixEnd_2943338 503782374214436803412947 := by
  unfold tailWord_2943338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838089052699145738735667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71568237473864388636628445 26838089052699145738735667)
  ·
    refine ⟨40257133579048718608103501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26838089052699145738735667 40257133579048718608103501)
    ·
      refine ⟨15096425092143269478038813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40257133579048718608103501 15096425092143269478038813)
      ·
        refine ⟨5661159409553726054264555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15096425092143269478038813 5661159409553726054264555)
        ·
          refine ⟨8491739114330589081396833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661159409553726054264555 8491739114330589081396833)
          ·
            refine ⟨6368804335747941811047625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491739114330589081396833 6368804335747941811047625)
            ·
              refine ⟨4776603251810956358285719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6368804335747941811047625 4776603251810956358285719)
              ·
                refine ⟨7164904877716434537428579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776603251810956358285719 7164904877716434537428579)
                ·
                  refine ⟨10747357316574651806142869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7164904877716434537428579 10747357316574651806142869)
                  ·
                    refine ⟨503782374214436803412947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10747357316574651806142869 503782374214436803412947)
                    ·
                      rfl

theorem cell23_2943338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2943338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943338 prefixEnd_2943338 := by exact prefixLift 2943338
  have htrace : WordTrace (prefixWord ++ tailWord_2943338) baseStart_2943338 baseEnd_2943338 := by
    simpa [prefixWord, tailWord_2943338, baseEnd_2943338] using wordTrace_append hprefix tailTrace_2943338
  have hstable : (prefixWord ++ tailWord_2943338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943338).length < 2 ^ (prefixWord ++ tailWord_2943338).sum := by decide
  have hdescent : baseEnd_2943338 < baseStart_2943338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943362 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2943362 : Nat := 118140960795 + 2943362 * 2 ^ 59
def prefixEnd_2943362 : Nat := 4983230072969 + 3 ^ 40 * 2943362 * 2
def baseEnd_2943362 : Nat := 1511359446179018316338731

theorem tailTrace_2943362 : CollatzResearch.WordTrace tailWord_2943362 prefixEnd_2943362 1511359446179018316338731 := by
  unfold tailWord_2943362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838307890677408763454085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71568821041806423369210893 26838307890677408763454085)
  ·
    refine ⟨5032182729502014143147641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26838307890677408763454085 5032182729502014143147641)
    ·
      refine ⟨3774137047126510607360731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5032182729502014143147641 3774137047126510607360731)
      ·
        refine ⟨5661205570689765911041097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774137047126510607360731 5661205570689765911041097)
        ·
          refine ⟨4245904178017324433280823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661205570689765911041097 4245904178017324433280823)
          ·
            refine ⟨6368856267025986649921235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245904178017324433280823 6368856267025986649921235)
            ·
              refine ⟨9553284400538979974881853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368856267025986649921235 9553284400538979974881853)
              ·
                refine ⟨3582481650202117490580695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9553284400538979974881853 3582481650202117490580695)
                ·
                  refine ⟨5373722475303176235871043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582481650202117490580695 5373722475303176235871043)
                  ·
                    refine ⟨8060583712954764353806565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5373722475303176235871043 8060583712954764353806565)
                    ·
                      refine ⟨1511359446179018316338731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8060583712954764353806565 1511359446179018316338731)
                      ·
                        rfl

theorem cell23_2943362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2943362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943362 prefixEnd_2943362 := by exact prefixLift 2943362
  have htrace : WordTrace (prefixWord ++ tailWord_2943362) baseStart_2943362 baseEnd_2943362 := by
    simpa [prefixWord, tailWord_2943362, baseEnd_2943362] using wordTrace_append hprefix tailTrace_2943362
  have hstable : (prefixWord ++ tailWord_2943362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943362).length < 2 ^ (prefixWord ++ tailWord_2943362).sum := by decide
  have hdescent : baseEnd_2943362 < baseStart_2943362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943418 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_2943418 : Nat := 118140960795 + 2943418 * 2 ^ 59
def prefixEnd_2943418 : Nat := 4983230072969 + 3 ^ 40 * 2943418 * 2
def baseEnd_2943418 : Nat := 1511388201095670097238473

theorem tailTrace_2943418 : CollatzResearch.WordTrace tailWord_2943418 prefixEnd_2943418 1511388201095670097238473 := by
  unfold tailWord_2943418
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838818512626689154463727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71570182700337837745236605 26838818512626689154463727)
  ·
    refine ⟨40258227768940033731695591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26838818512626689154463727 40258227768940033731695591)
    ·
      refine ⟨60387341653410050597543387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40258227768940033731695591 60387341653410050597543387)
      ·
        refine ⟨90581012480115075896315081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60387341653410050597543387 90581012480115075896315081)
        ·
          refine ⟨67935759360086306922236311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90581012480115075896315081 67935759360086306922236311)
          ·
            refine ⟨101903639040129460383354467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67935759360086306922236311 101903639040129460383354467)
            ·
              refine ⟨152855458560194190575031701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101903639040129460383354467 152855458560194190575031701)
              ·
                refine ⟨7165099620009102683204611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152855458560194190575031701 7165099620009102683204611)
                ·
                  refine ⟨10747649430013654024806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7165099620009102683204611 10747649430013654024806917)
                  ·
                    refine ⟨2015184268127560129651297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10747649430013654024806917 2015184268127560129651297)
                    ·
                      refine ⟨1511388201095670097238473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015184268127560129651297 1511388201095670097238473)
                      ·
                        rfl

theorem cell23_2943418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_2943418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943418 prefixEnd_2943418 := by exact prefixLift 2943418
  have htrace : WordTrace (prefixWord ++ tailWord_2943418) baseStart_2943418 baseEnd_2943418 := by
    simpa [prefixWord, tailWord_2943418, baseEnd_2943418] using wordTrace_append hprefix tailTrace_2943418
  have hstable : (prefixWord ++ tailWord_2943418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943418).length < 2 ^ (prefixWord ++ tailWord_2943418).sum := by decide
  have hdescent : baseEnd_2943418 < baseStart_2943418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943421 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2943421 : Nat := 118140960795 + 2943421 * 2 ^ 59
def prefixEnd_2943421 : Nat := 4983230072969 + 3 ^ 40 * 2943421 * 2
def baseEnd_2943421 : Nat := 1511389741537633585500959

theorem tailTrace_2943421 : CollatzResearch.WordTrace tailWord_2943421 prefixEnd_2943421 1511389741537633585500959 := by
  unfold tailWord_2943421
  simp only [CollatzResearch.WordTrace]
  refine ⟨107355383469495888130214117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71570255646330592086809411 107355383469495888130214117)
  ·
    refine ⟨20129134400530479024415147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107355383469495888130214117 20129134400530479024415147)
    ·
      refine ⟨30193701600795718536622721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20129134400530479024415147 30193701600795718536622721)
      ·
        refine ⟨22645276200596788902467041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30193701600795718536622721 22645276200596788902467041)
        ·
          refine ⟨16983957150447591676850281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22645276200596788902467041 16983957150447591676850281)
          ·
            refine ⟨12737967862835693757637711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16983957150447591676850281 12737967862835693757637711)
            ·
              refine ⟨19106951794253540636456567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12737967862835693757637711 19106951794253540636456567)
              ·
                refine ⟨28660427691380310954684851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19106951794253540636456567 28660427691380310954684851)
                ·
                  refine ⟨42990641537070466432027277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28660427691380310954684851 42990641537070466432027277)
                  ·
                    refine ⟨16121490576401424912010229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42990641537070466432027277 16121490576401424912010229)
                    ·
                      refine ⟨1511389741537633585500959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16121490576401424912010229 1511389741537633585500959)
                      ·
                        rfl

theorem cell23_2943421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2943421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943421 prefixEnd_2943421 := by exact prefixLift 2943421
  have htrace : WordTrace (prefixWord ++ tailWord_2943421) baseStart_2943421 baseEnd_2943421 := by
    simpa [prefixWord, tailWord_2943421, baseEnd_2943421] using wordTrace_append hprefix tailTrace_2943421
  have hstable : (prefixWord ++ tailWord_2943421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943421).length < 2 ^ (prefixWord ++ tailWord_2943421).sum := by decide
  have hdescent : baseEnd_2943421 < baseStart_2943421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943435 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 2, 2, 2]
def baseStart_2943435 : Nat := 118140960795 + 2943435 * 2 ^ 59
def prefixEnd_2943435 : Nat := 4983230072969 + 3 ^ 40 * 2943435 * 2
def baseEnd_2943435 : Nat := 1511396930266796530725895

theorem tailTrace_2943435 : CollatzResearch.WordTrace tailWord_2943435 prefixEnd_2943435 1511396930266796530725895 := by
  unfold tailWord_2943435
  simp only [CollatzResearch.WordTrace]
  refine ⟨107355894091445168521223759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71570596060963445680815839 107355894091445168521223759)
  ·
    refine ⟨161033841137167752781835639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107355894091445168521223759 161033841137167752781835639)
    ·
      refine ⟨241550761705751629172753459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161033841137167752781835639 241550761705751629172753459)
      ·
        refine ⟨362326142558627443759130189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241550761705751629172753459 362326142558627443759130189)
        ·
          refine ⟨135872303459485291409673821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362326142558627443759130189 135872303459485291409673821)
          ·
            refine ⟨50952113797306984278627683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135872303459485291409673821 50952113797306984278627683)
            ·
              refine ⟨76428170695960476417941525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50952113797306984278627683 76428170695960476417941525)
              ·
                refine ⟨3582570501373147332091009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76428170695960476417941525 3582570501373147332091009)
                ·
                  refine ⟨2686927876029860499068257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3582570501373147332091009 2686927876029860499068257)
                  ·
                    refine ⟨2015195907022395374301193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686927876029860499068257 2015195907022395374301193)
                    ·
                      refine ⟨1511396930266796530725895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015195907022395374301193 1511396930266796530725895)
                      ·
                        rfl

theorem cell23_2943435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2, 2].length) (baseStart_2943435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943435 prefixEnd_2943435 := by exact prefixLift 2943435
  have htrace : WordTrace (prefixWord ++ tailWord_2943435) baseStart_2943435 baseEnd_2943435 := by
    simpa [prefixWord, tailWord_2943435, baseEnd_2943435] using wordTrace_append hprefix tailTrace_2943435
  have hstable : (prefixWord ++ tailWord_2943435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943435).length < 2 ^ (prefixWord ++ tailWord_2943435).sum := by decide
  have hdescent : baseEnd_2943435 < baseStart_2943435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943481 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2943481 : Nat := 118140960795 + 2943481 * 2 ^ 59
def prefixEnd_2943481 : Nat := 4983230072969 + 3 ^ 40 * 2943481 * 2
def baseEnd_2943481 : Nat := 1511420550376903350750683

theorem tailTrace_2943481 : CollatzResearch.WordTrace tailWord_2943481 prefixEnd_2943481 1511420550376903350750683 := by
  unfold tailWord_2943481
  simp only [CollatzResearch.WordTrace]
  refine ⟨107357571849278518377398297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71571714566185678918265531 107357571849278518377398297)
  ·
    refine ⟨80518178886958888783048723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107357571849278518377398297 80518178886958888783048723)
    ·
      refine ⟨120777268330438333174573085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80518178886958888783048723 120777268330438333174573085)
      ·
        refine ⟨45291475623914374940464907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120777268330438333174573085 45291475623914374940464907)
        ·
          refine ⟨67937213435871562410697361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45291475623914374940464907 67937213435871562410697361)
          ·
            refine ⟨50952910076903671808023021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67937213435871562410697361 50952910076903671808023021)
            ·
              refine ⟨19107341278838876928008633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50952910076903671808023021 19107341278838876928008633)
              ·
                refine ⟨14330505959129157696006475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19107341278838876928008633 14330505959129157696006475)
                ·
                  refine ⟨21495758938693736544009713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14330505959129157696006475 21495758938693736544009713)
                  ·
                    refine ⟨16121819204020302408007285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21495758938693736544009713 16121819204020302408007285)
                    ·
                      refine ⟨1511420550376903350750683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16121819204020302408007285 1511420550376903350750683)
                      ·
                        rfl

theorem cell23_2943481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2943481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943481 prefixEnd_2943481 := by exact prefixLift 2943481
  have htrace : WordTrace (prefixWord ++ tailWord_2943481) baseStart_2943481 baseEnd_2943481 := by
    simpa [prefixWord, tailWord_2943481, baseEnd_2943481] using wordTrace_append hprefix tailTrace_2943481
  have hstable : (prefixWord ++ tailWord_2943481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943481).length < 2 ^ (prefixWord ++ tailWord_2943481).sum := by decide
  have hdescent : baseEnd_2943481 < baseStart_2943481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943492 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 5]
def baseStart_2943492 : Nat := 118140960795 + 2943492 * 2 ^ 59
def prefixEnd_2943492 : Nat := 4983230072969 + 3 ^ 40 * 2943492 * 2
def baseEnd_2943492 : Nat := 167936244296011423079237

theorem tailTrace_2943492 : CollatzResearch.WordTrace tailWord_2943492 prefixEnd_2943492 167936244296011423079237 := by
  unfold tailWord_2943492
  simp only [CollatzResearch.WordTrace]
  refine ⟨53678986526119333628024365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71571982034825778170699153 53678986526119333628024365)
  ·
    refine ⟨20129619947294750110509137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53678986526119333628024365 20129619947294750110509137)
    ·
      refine ⟨15097214960471062582881853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20129619947294750110509137 15097214960471062582881853)
      ·
        refine ⟨5661455610176648468580695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15097214960471062582881853 5661455610176648468580695)
        ·
          refine ⟨8492183415264972702871043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661455610176648468580695 8492183415264972702871043)
          ·
            refine ⟨12738275122897459054306565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492183415264972702871043 12738275122897459054306565)
            ·
              refine ⟨2388426585543273572682481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12738275122897459054306565 2388426585543273572682481)
              ·
                refine ⟨1791319939157455179511861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388426585543273572682481 1791319939157455179511861)
                ·
                  refine ⟨167936244296011423079237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791319939157455179511861 167936244296011423079237)
                  ·
                    rfl

theorem cell23_2943492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_2943492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943492 prefixEnd_2943492 := by exact prefixLift 2943492
  have htrace : WordTrace (prefixWord ++ tailWord_2943492) baseStart_2943492 baseEnd_2943492 := by
    simpa [prefixWord, tailWord_2943492, baseEnd_2943492] using wordTrace_append hprefix tailTrace_2943492
  have hstable : (prefixWord ++ tailWord_2943492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943492).length < 2 ^ (prefixWord ++ tailWord_2943492).sum := by decide
  have hdescent : baseEnd_2943492 < baseStart_2943492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943542 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_2943542 : Nat := 118140960795 + 2943542 * 2 ^ 59
def prefixEnd_2943542 : Nat := 4983230072969 + 3 ^ 40 * 2943542 * 2
def baseEnd_2943542 : Nat := 1511451872696827612087903

theorem tailTrace_2943542 : CollatzResearch.WordTrace tailWord_2943542 prefixEnd_2943542 1511451872696827612087903 := by
  unfold tailWord_2943542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709987293878595362210555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71573197801371683863579253 6709987293878595362210555)
  ·
    refine ⟨10064980940817893043315833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6709987293878595362210555 10064980940817893043315833)
    ·
      refine ⟨7548735705613419782486875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10064980940817893043315833 7548735705613419782486875)
      ·
        refine ⟨11323103558420129673730313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7548735705613419782486875 11323103558420129673730313)
        ·
          refine ⟨8492327668815097255297735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11323103558420129673730313 8492327668815097255297735)
          ·
            refine ⟨12738491503222645882946603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492327668815097255297735 12738491503222645882946603)
            ·
              refine ⟨19107737254833968824419905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12738491503222645882946603 19107737254833968824419905)
              ·
                refine ⟨14330802941125476618314929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19107737254833968824419905 14330802941125476618314929)
                ·
                  refine ⟨10748102205844107463736197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14330802941125476618314929 10748102205844107463736197)
                  ·
                    refine ⟨2015269163595770149450537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10748102205844107463736197 2015269163595770149450537)
                    ·
                      refine ⟨1511451872696827612087903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015269163595770149450537 1511451872696827612087903)
                      ·
                        rfl

theorem cell23_2943542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_2943542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943542 prefixEnd_2943542 := by exact prefixLift 2943542
  have htrace : WordTrace (prefixWord ++ tailWord_2943542) baseStart_2943542 baseEnd_2943542 := by
    simpa [prefixWord, tailWord_2943542, baseEnd_2943542] using wordTrace_append hprefix tailTrace_2943542
  have hstable : (prefixWord ++ tailWord_2943542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943542).length < 2 ^ (prefixWord ++ tailWord_2943542).sum := by decide
  have hdescent : baseEnd_2943542 < baseStart_2943542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943548 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 8]
def baseStart_2943548 : Nat := 118140960795 + 2943548 * 2 ^ 59
def prefixEnd_2943548 : Nat := 4983230072969 + 3 ^ 40 * 2943548 * 2
def baseEnd_2943548 : Nat := 167939439286750509845875

theorem tailTrace_2943548 : CollatzResearch.WordTrace tailWord_2943548 prefixEnd_2943548 167939439286750509845875 := by
  unfold tailWord_2943548
  simp only [CollatzResearch.WordTrace]
  refine ⟨53680007770017894410043649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71573343693357192546724865 53680007770017894410043649)
  ·
    refine ⟨40260005827513420807532737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53680007770017894410043649 40260005827513420807532737)
    ·
      refine ⟨30195004370635065605649553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40260005827513420807532737 30195004370635065605649553)
      ·
        refine ⟨22646253277976299204237165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30195004370635065605649553 22646253277976299204237165)
        ·
          refine ⟨8492344979241112201588937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22646253277976299204237165 8492344979241112201588937)
          ·
            refine ⟨6369258734430834151191703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8492344979241112201588937 6369258734430834151191703)
            ·
              refine ⟨9553888101646251226787555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369258734430834151191703 9553888101646251226787555)
              ·
                refine ⟨14330832152469376840181333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9553888101646251226787555 14330832152469376840181333)
                ·
                  refine ⟨167939439286750509845875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14330832152469376840181333 167939439286750509845875)
                  ·
                    rfl

theorem cell23_2943548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_2943548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943548 prefixEnd_2943548 := by exact prefixLift 2943548
  have htrace : WordTrace (prefixWord ++ tailWord_2943548) baseStart_2943548 baseEnd_2943548 := by
    simpa [prefixWord, tailWord_2943548, baseEnd_2943548] using wordTrace_append hprefix tailTrace_2943548
  have hstable : (prefixWord ++ tailWord_2943548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943548).length < 2 ^ (prefixWord ++ tailWord_2943548).sum := by decide
  have hdescent : baseEnd_2943548 < baseStart_2943548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943551 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_2943551 : Nat := 118140960795 + 2943551 * 2 ^ 59
def prefixEnd_2943551 : Nat := 4983230072969 + 3 ^ 40 * 2943551 * 2
def baseEnd_2943551 : Nat := 1511456494022718076875361

theorem tailTrace_2943551 : CollatzResearch.WordTrace tailWord_2943551 prefixEnd_2943551 1511456494022718076875361 := by
  unfold tailWord_2943551
  simp only [CollatzResearch.WordTrace]
  refine ⟨107360124959024920332446507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71573416639349946888297671 107360124959024920332446507)
  ·
    refine ⟨161040187438537380498669761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107360124959024920332446507 161040187438537380498669761)
    ·
      refine ⟨120780140578903035374002321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161040187438537380498669761 120780140578903035374002321)
      ·
        refine ⟨90585105434177276530501741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120780140578903035374002321 90585105434177276530501741)
        ·
          refine ⟨33969414537816478698938153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90585105434177276530501741 33969414537816478698938153)
          ·
            refine ⟨25477060903362359024203615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33969414537816478698938153 25477060903362359024203615)
            ·
              refine ⟨38215591355043538536305423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25477060903362359024203615 38215591355043538536305423)
              ·
                refine ⟨57323387032565307804458135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38215591355043538536305423 57323387032565307804458135)
                ·
                  refine ⟨85985080548847961706687203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57323387032565307804458135 85985080548847961706687203)
                  ·
                    refine ⟨128977620823271942560030805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85985080548847961706687203 128977620823271942560030805)
                    ·
                      refine ⟨1511456494022718076875361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128977620823271942560030805 1511456494022718076875361)
                      ·
                        rfl

theorem cell23_2943551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_2943551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943551 prefixEnd_2943551 := by exact prefixLift 2943551
  have htrace : WordTrace (prefixWord ++ tailWord_2943551) baseStart_2943551 baseEnd_2943551 := by
    simpa [prefixWord, tailWord_2943551, baseEnd_2943551] using wordTrace_append hprefix tailTrace_2943551
  have hstable : (prefixWord ++ tailWord_2943551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943551).length < 2 ^ (prefixWord ++ tailWord_2943551).sum := by decide
  have hdescent : baseEnd_2943551 < baseStart_2943551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943575 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_2943575 : Nat := 118140960795 + 2943575 * 2 ^ 59
def prefixEnd_2943575 : Nat := 4983230072969 + 3 ^ 40 * 2943575 * 2
def baseEnd_2943575 : Nat := 1511468817558425982975251

theorem tailTrace_2943575 : CollatzResearch.WordTrace tailWord_2943575 prefixEnd_2943575 1511468817558425982975251 := by
  unfold tailWord_2943575
  simp only [CollatzResearch.WordTrace]
  refine ⟨107361000310937972431320179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71574000207291981620880119 107361000310937972431320179)
  ·
    refine ⟨161041500466406958646980269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107361000310937972431320179 161041500466406958646980269)
    ·
      refine ⟨60390562674902609492617601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161041500466406958646980269 60390562674902609492617601)
      ·
        refine ⟨45292922006176957119463201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60390562674902609492617601 45292922006176957119463201)
        ·
          refine ⟨33969691504632717839597401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45292922006176957119463201 33969691504632717839597401)
          ·
            refine ⟨25477268628474538379698051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33969691504632717839597401 25477268628474538379698051)
            ·
              refine ⟨38215902942711807569547077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25477268628474538379698051 38215902942711807569547077)
              ·
                refine ⟨7165481801758463919290077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38215902942711807569547077 7165481801758463919290077)
                ·
                  refine ⟨2687055675659423969733779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7165481801758463919290077 2687055675659423969733779)
                  ·
                    refine ⟨4030583513489135954600669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2687055675659423969733779 4030583513489135954600669)
                    ·
                      refine ⟨1511468817558425982975251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4030583513489135954600669 1511468817558425982975251)
                      ·
                        rfl

theorem cell23_2943575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_2943575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943575 prefixEnd_2943575 := by exact prefixLift 2943575
  have htrace : WordTrace (prefixWord ++ tailWord_2943575) baseStart_2943575 baseEnd_2943575 := by
    simpa [prefixWord, tailWord_2943575, baseEnd_2943575] using wordTrace_append hprefix tailTrace_2943575
  have hstable : (prefixWord ++ tailWord_2943575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943575).length < 2 ^ (prefixWord ++ tailWord_2943575).sum := by decide
  have hdescent : baseEnd_2943575 < baseStart_2943575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943585 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_2943585 : Nat := 118140960795 + 2943585 * 2 ^ 59
def prefixEnd_2943585 : Nat := 4983230072969 + 3 ^ 40 * 2943585 * 2
def baseEnd_2943585 : Nat := 1511473952364970943850205

theorem tailTrace_2943585 : CollatzResearch.WordTrace tailWord_2943585 prefixEnd_2943585 1511473952364970943850205 := by
  unfold tailWord_2943585
  simp only [CollatzResearch.WordTrace]
  refine ⟨107361365040901744139184209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71574243360601162759456139 107361365040901744139184209)
  ·
    refine ⟨80521023780676308104388157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107361365040901744139184209 80521023780676308104388157)
    ·
      refine ⟨30195383917753615539145559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80521023780676308104388157 30195383917753615539145559)
      ·
        refine ⟨45293075876630423308718339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30195383917753615539145559 45293075876630423308718339)
        ·
          refine ⟨67939613814945634963077509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45293075876630423308718339 67939613814945634963077509)
          ·
            refine ⟨12738677590302306555577033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67939613814945634963077509 12738677590302306555577033)
            ·
              refine ⟨9554008192726729916682775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12738677590302306555577033 9554008192726729916682775)
              ·
                refine ⟨14331012289090094875024163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9554008192726729916682775 14331012289090094875024163)
                ·
                  refine ⟨21496518433635142312536245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14331012289090094875024163 21496518433635142312536245)
                  ·
                    refine ⟨2015298603153294591800273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21496518433635142312536245 2015298603153294591800273)
                    ·
                      refine ⟨1511473952364970943850205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015298603153294591800273 1511473952364970943850205)
                      ·
                        rfl

theorem cell23_2943585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_2943585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943585 prefixEnd_2943585 := by exact prefixLift 2943585
  have htrace : WordTrace (prefixWord ++ tailWord_2943585) baseStart_2943585 baseEnd_2943585 := by
    simpa [prefixWord, tailWord_2943585, baseEnd_2943585] using wordTrace_append hprefix tailTrace_2943585
  have hstable : (prefixWord ++ tailWord_2943585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943585).length < 2 ^ (prefixWord ++ tailWord_2943585).sum := by decide
  have hdescent : baseEnd_2943585 < baseStart_2943585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943642 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_2943642 : Nat := 118140960795 + 2943642 * 2 ^ 59
def prefixEnd_2943642 : Nat := 4983230072969 + 3 ^ 40 * 2943642 * 2
def baseEnd_2943642 : Nat := 503834406920759073612481

theorem tailTrace_2943642 : CollatzResearch.WordTrace tailWord_2943642 prefixEnd_2943642 503834406920759073612481 := by
  unfold tailWord_2943642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26840861000423810718502295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71575629334463495249339453 26840861000423810718502295)
  ·
    refine ⟨40261291500635716077753443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26840861000423810718502295 40261291500635716077753443)
    ·
      refine ⟨60391937250953574116630165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40261291500635716077753443 60391937250953574116630165)
      ·
        refine ⟨2830872058638448786717039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60391937250953574116630165 2830872058638448786717039)
        ·
          refine ⟨4246308087957673180075559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830872058638448786717039 4246308087957673180075559)
          ·
            refine ⟨6369462131936509770113339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246308087957673180075559 6369462131936509770113339)
            ·
              refine ⟨9554193197904764655170009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369462131936509770113339 9554193197904764655170009)
              ·
                refine ⟨7165644898428573491377507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9554193197904764655170009 7165644898428573491377507)
                ·
                  refine ⟨10748467347642860237066261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7165644898428573491377507 10748467347642860237066261)
                  ·
                    refine ⟨503834406920759073612481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10748467347642860237066261 503834406920759073612481)
                    ·
                      rfl

theorem cell23_2943642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_2943642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943642 prefixEnd_2943642 := by exact prefixLift 2943642
  have htrace : WordTrace (prefixWord ++ tailWord_2943642) baseStart_2943642 baseEnd_2943642 := by
    simpa [prefixWord, tailWord_2943642, baseEnd_2943642] using wordTrace_append hprefix tailTrace_2943642
  have hstable : (prefixWord ++ tailWord_2943642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943642).length < 2 ^ (prefixWord ++ tailWord_2943642).sum := by decide
  have hdescent : baseEnd_2943642 < baseStart_2943642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943649 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2943649 : Nat := 118140960795 + 2943649 * 2 ^ 59
def prefixEnd_2943649 : Nat := 4983230072969 + 3 ^ 40 * 2943649 * 2
def baseEnd_2943649 : Nat := 1511506815126858693449911

theorem tailTrace_2943649 : CollatzResearch.WordTrace tailWord_2943649 prefixEnd_2943649 1511506815126858693449911 := by
  unfold tailWord_2943649
  simp only [CollatzResearch.WordTrace]
  refine ⟨107363699312669883069514001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71575799541779922046342667 107363699312669883069514001)
  ·
    refine ⟨80522774484502412302135501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107363699312669883069514001 80522774484502412302135501)
    ·
      refine ⟨30196040431688404613300813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80522774484502412302135501 30196040431688404613300813)
      ·
        refine ⟨11323515161883151729987805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30196040431688404613300813 11323515161883151729987805)
        ·
          refine ⟨4246318185706181898745427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11323515161883151729987805 4246318185706181898745427)
          ·
            refine ⟨6369477278559272848118141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246318185706181898745427 6369477278559272848118141)
            ·
              refine ⟨2388553979459727318044303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6369477278559272848118141 2388553979459727318044303)
              ·
                refine ⟨3582830969189590977066455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388553979459727318044303 3582830969189590977066455)
                ·
                  refine ⟨5374246453784386465599683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582830969189590977066455 5374246453784386465599683)
                  ·
                    refine ⟨8061369680676579698399525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5374246453784386465599683 8061369680676579698399525)
                    ·
                      refine ⟨1511506815126858693449911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8061369680676579698399525 1511506815126858693449911)
                      ·
                        rfl

theorem cell23_2943649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2943649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943649 prefixEnd_2943649 := by exact prefixLift 2943649
  have htrace : WordTrace (prefixWord ++ tailWord_2943649) baseStart_2943649 baseEnd_2943649 := by
    simpa [prefixWord, tailWord_2943649, baseEnd_2943649] using wordTrace_append hprefix tailTrace_2943649
  have hstable : (prefixWord ++ tailWord_2943649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943649).length < 2 ^ (prefixWord ++ tailWord_2943649).sum := by decide
  have hdescent : baseEnd_2943649 < baseStart_2943649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943655 : List Nat := [1, 1, 6, 3, 1, 11]
def baseStart_2943655 : Nat := 118140960795 + 2943655 * 2 ^ 59
def prefixEnd_2943655 : Nat := 4983230072969 + 3 ^ 40 * 2943655 * 2
def baseEnd_2943655 : Nat := 6220205333377718806481

theorem tailTrace_2943655 : CollatzResearch.WordTrace tailWord_2943655 prefixEnd_2943655 6220205333377718806481 := by
  unfold tailWord_2943655
  simp only [CollatzResearch.WordTrace]
  refine ⟨107363918150648146094232419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71575945433765430729488279 107363918150648146094232419)
  ·
    refine ⟨161045877225972219141348629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107363918150648146094232419 161045877225972219141348629)
    ·
      refine ⟨7549025494967447772250717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161045877225972219141348629 7549025494967447772250717)
      ·
        refine ⟨2830884560612792914594019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7549025494967447772250717 2830884560612792914594019)
        ·
          refine ⟨4246326840919189371891029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830884560612792914594019 4246326840919189371891029)
          ·
            refine ⟨6220205333377718806481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4246326840919189371891029 6220205333377718806481)
            ·
              rfl

theorem cell23_2943655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 11].length) (baseStart_2943655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943655 prefixEnd_2943655 := by exact prefixLift 2943655
  have htrace : WordTrace (prefixWord ++ tailWord_2943655) baseStart_2943655 baseEnd_2943655 := by
    simpa [prefixWord, tailWord_2943655, baseEnd_2943655] using wordTrace_append hprefix tailTrace_2943655
  have hstable : (prefixWord ++ tailWord_2943655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943655).length < 2 ^ (prefixWord ++ tailWord_2943655).sum := by decide
  have hdescent : baseEnd_2943655 < baseStart_2943655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943715 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 2, 6]
def baseStart_2943715 : Nat := 118140960795 + 2943715 * 2 ^ 59
def prefixEnd_2943715 : Nat := 4983230072969 + 3 ^ 40 * 2943715 * 2
def baseEnd_2943715 : Nat := 503846901616685145074869

theorem tailTrace_2943715 : CollatzResearch.WordTrace tailWord_2943715 prefixEnd_2943715 503846901616685145074869 := by
  unfold tailWord_2943715
  simp only [CollatzResearch.WordTrace]
  refine ⟨107366106530430776341416599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71577404353620517560944399 107366106530430776341416599)
  ·
    refine ⟨161049159795646164512124899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107366106530430776341416599 161049159795646164512124899)
    ·
      refine ⟨241573739693469246768187349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161049159795646164512124899 241573739693469246768187349)
      ·
        refine ⟨5661884524065685471129391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 241573739693469246768187349 5661884524065685471129391)
        ·
          refine ⟨8492826786098528206694087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661884524065685471129391 8492826786098528206694087)
          ·
            refine ⟨12739240179147792310041131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492826786098528206694087 12739240179147792310041131)
            ·
              refine ⟨19108860268721688465061697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12739240179147792310041131 19108860268721688465061697)
              ·
                refine ⟨14331645201541266348796273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19108860268721688465061697 14331645201541266348796273)
                ·
                  refine ⟨10748733901155949761597205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14331645201541266348796273 10748733901155949761597205)
                  ·
                    refine ⟨503846901616685145074869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10748733901155949761597205 503846901616685145074869)
                    ·
                      rfl

theorem cell23_2943715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 6].length) (baseStart_2943715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943715 prefixEnd_2943715 := by exact prefixLift 2943715
  have htrace : WordTrace (prefixWord ++ tailWord_2943715) baseStart_2943715 baseEnd_2943715 := by
    simpa [prefixWord, tailWord_2943715, baseEnd_2943715] using wordTrace_append hprefix tailTrace_2943715
  have hstable : (prefixWord ++ tailWord_2943715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943715).length < 2 ^ (prefixWord ++ tailWord_2943715).sum := by decide
  have hdescent : baseEnd_2943715 < baseStart_2943715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943733 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2943733 : Nat := 118140960795 + 2943733 * 2 ^ 59
def prefixEnd_2943733 : Nat := 4983230072969 + 3 ^ 40 * 2943733 * 2
def baseEnd_2943733 : Nat := 1511549947501836364799525

theorem tailTrace_2943733 : CollatzResearch.WordTrace tailWord_2943733 prefixEnd_2943733 1511549947501836364799525 := by
  unfold tailWord_2943733
  simp only [CollatzResearch.WordTrace]
  refine ⟨107366763044365565415571853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71577842029577043610381235 107366763044365565415571853)
  ·
    refine ⟨40262536141637087030839445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107366763044365565415571853 40262536141637087030839445)
    ·
      refine ⟨1887306381639238454570599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40262536141637087030839445 1887306381639238454570599)
      ·
        refine ⟨2830959572458857681855899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887306381639238454570599 2830959572458857681855899)
        ·
          refine ⟨4246439358688286522783849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830959572458857681855899 4246439358688286522783849)
          ·
            refine ⟨3184829519016214892087887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246439358688286522783849 3184829519016214892087887)
            ·
              refine ⟨4777244278524322338131831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184829519016214892087887 4777244278524322338131831)
              ·
                refine ⟨7165866417786483507197747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777244278524322338131831 7165866417786483507197747)
                ·
                  refine ⟨10748799626679725260796621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7165866417786483507197747 10748799626679725260796621)
                  ·
                    refine ⟨4030799860004896972798733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10748799626679725260796621 4030799860004896972798733)
                    ·
                      refine ⟨1511549947501836364799525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4030799860004896972798733 1511549947501836364799525)
                      ·
                        rfl

theorem cell23_2943733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2943733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943733 prefixEnd_2943733 := by exact prefixLift 2943733
  have htrace : WordTrace (prefixWord ++ tailWord_2943733) baseStart_2943733 baseEnd_2943733 := by
    simpa [prefixWord, tailWord_2943733, baseEnd_2943733] using wordTrace_append hprefix tailTrace_2943733
  have hstable : (prefixWord ++ tailWord_2943733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943733).length < 2 ^ (prefixWord ++ tailWord_2943733).sum := by decide
  have hdescent : baseEnd_2943733 < baseStart_2943733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943775 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 4, 5]
def baseStart_2943775 : Nat := 118140960795 + 2943775 * 2 ^ 59
def prefixEnd_2943775 : Nat := 4983230072969 + 3 ^ 40 * 2943775 * 2
def baseEnd_2943775 : Nat := 503857171229775066824777

theorem tailTrace_2943775 : CollatzResearch.WordTrace tailWord_2943775 prefixEnd_2943775 503857171229775066824777 := by
  unfold tailWord_2943775
  simp only [CollatzResearch.WordTrace]
  refine ⟨107368294910213406588600779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71578863273475604392400519 107368294910213406588600779)
  ·
    refine ⟨161052442365320109882901169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107368294910213406588600779 161052442365320109882901169)
    ·
      refine ⟨120789331773990082412175877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161052442365320109882901169 120789331773990082412175877)
      ·
        refine ⟨22647999707623140452282977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120789331773990082412175877 22647999707623140452282977)
        ·
          refine ⟨16985999780717355339212233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22647999707623140452282977 16985999780717355339212233)
          ·
            refine ⟨12739499835538016504409175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16985999780717355339212233 12739499835538016504409175)
            ·
              refine ⟨19109249753307024756613763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12739499835538016504409175 19109249753307024756613763)
              ·
                refine ⟨28663874629960537134920645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19109249753307024756613763 28663874629960537134920645)
                ·
                  refine ⟨5374476493117600712797621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28663874629960537134920645 5374476493117600712797621)
                  ·
                    refine ⟨503857171229775066824777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5374476493117600712797621 503857171229775066824777)
                    ·
                      rfl

theorem cell23_2943775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_2943775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943775 prefixEnd_2943775 := by exact prefixLift 2943775
  have htrace : WordTrace (prefixWord ++ tailWord_2943775) baseStart_2943775 baseEnd_2943775 := by
    simpa [prefixWord, tailWord_2943775, baseEnd_2943775] using wordTrace_append hprefix tailTrace_2943775
  have hstable : (prefixWord ++ tailWord_2943775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943775).length < 2 ^ (prefixWord ++ tailWord_2943775).sum := by decide
  have hdescent : baseEnd_2943775 < baseStart_2943775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943790 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2943790 : Nat := 118140960795 + 2943790 * 2 ^ 59
def prefixEnd_2943790 : Nat := 4983230072969 + 3 ^ 40 * 2943790 * 2
def baseEnd_2943790 : Nat := 1511579215899142641786763

theorem tailTrace_2943790 : CollatzResearch.WordTrace tailWord_2943790 prefixEnd_2943790 1511579215899142641786763 := by
  unfold tailWord_2943790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13421105250644883018799603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71579228003439376100264549 13421105250644883018799603)
  ·
    refine ⟨20131657875967324528199405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13421105250644883018799603 20131657875967324528199405)
    ·
      refine ⟨7549371703487746698074777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20131657875967324528199405 7549371703487746698074777)
      ·
        refine ⟨5662028777615810023556083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7549371703487746698074777 5662028777615810023556083)
        ·
          refine ⟨8493043166423715035334125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662028777615810023556083 8493043166423715035334125)
          ·
            refine ⟨3184891187408893138250297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8493043166423715035334125 3184891187408893138250297)
            ·
              refine ⟨2388668390556669853687723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184891187408893138250297 2388668390556669853687723)
              ·
                refine ⟨3583002585835004780531585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388668390556669853687723 3583002585835004780531585)
                ·
                  refine ⟨2687251939376253585398689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583002585835004780531585 2687251939376253585398689)
                  ·
                    refine ⟨2015438954532190189049017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687251939376253585398689 2015438954532190189049017)
                    ·
                      refine ⟨1511579215899142641786763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015438954532190189049017 1511579215899142641786763)
                      ·
                        rfl

theorem cell23_2943790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2943790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943790 prefixEnd_2943790 := by exact prefixLift 2943790
  have htrace : WordTrace (prefixWord ++ tailWord_2943790) baseStart_2943790 baseEnd_2943790 := by
    simpa [prefixWord, tailWord_2943790, baseEnd_2943790] using wordTrace_append hprefix tailTrace_2943790
  have hstable : (prefixWord ++ tailWord_2943790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943790).length < 2 ^ (prefixWord ++ tailWord_2943790).sum := by decide
  have hdescent : baseEnd_2943790 < baseStart_2943790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943839 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 1, 4]
def baseStart_2943839 : Nat := 118140960795 + 2943839 * 2 ^ 59
def prefixEnd_2943839 : Nat := 4983230072969 + 3 ^ 40 * 2943839 * 2
def baseEnd_2943839 : Nat := 503868125483737650024679

theorem tailTrace_2943839 : CollatzResearch.WordTrace tailWord_2943839 prefixEnd_2943839 503868125483737650024679 := by
  unfold tailWord_2943839
  simp only [CollatzResearch.WordTrace]
  refine ⟨107370629181981545518930571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71580419454654363679287047 107370629181981545518930571)
  ·
    refine ⟨161055943772972318278395857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107370629181981545518930571 161055943772972318278395857)
    ·
      refine ⟨120791957829729238708796893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161055943772972318278395857 120791957829729238708796893)
      ·
        refine ⟨45296984186148464515798835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120791957829729238708796893 45296984186148464515798835)
        ·
          refine ⟨67945476279222696773698253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45296984186148464515798835 67945476279222696773698253)
          ·
            refine ⟨25479553604708511290136845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67945476279222696773698253 25479553604708511290136845)
            ·
              refine ⟨9554832601765691733801317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25479553604708511290136845 9554832601765691733801317)
              ·
                refine ⟨1791531112831067200087747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9554832601765691733801317 1791531112831067200087747)
                ·
                  refine ⟨2687296669246600800131621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791531112831067200087747 2687296669246600800131621)
                  ·
                    refine ⟨503868125483737650024679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2687296669246600800131621 503868125483737650024679)
                    ·
                      rfl

theorem cell23_2943839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 4].length) (baseStart_2943839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943839 prefixEnd_2943839 := by exact prefixLift 2943839
  have htrace : WordTrace (prefixWord ++ tailWord_2943839) baseStart_2943839 baseEnd_2943839 := by
    simpa [prefixWord, tailWord_2943839, baseEnd_2943839] using wordTrace_append hprefix tailTrace_2943839
  have hstable : (prefixWord ++ tailWord_2943839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943839).length < 2 ^ (prefixWord ++ tailWord_2943839).sum := by decide
  have hdescent : baseEnd_2943839 < baseStart_2943839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943915 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_2943915 : Nat := 118140960795 + 2943915 * 2 ^ 59
def prefixEnd_2943915 : Nat := 4983230072969 + 3 ^ 40 * 2943915 * 2
def baseEnd_2943915 : Nat := 1511643400980954652723687

theorem tailTrace_2943915 : CollatzResearch.WordTrace tailWord_2943915 prefixEnd_2943915 1511643400980954652723687 := by
  unfold tailWord_2943915
  simp only [CollatzResearch.WordTrace]
  refine ⟨107373401129706210498697199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71582267419804140332464799 107373401129706210498697199)
  ·
    refine ⟨161060101694559315748045799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107373401129706210498697199 161060101694559315748045799)
    ·
      refine ⟨241590152541838973622068699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161060101694559315748045799 241590152541838973622068699)
      ·
        refine ⟨362385228812758460433103049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241590152541838973622068699 362385228812758460433103049)
        ·
          refine ⟨271788921609568845324827287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362385228812758460433103049 271788921609568845324827287)
          ·
            refine ⟨407683382414353267987240931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271788921609568845324827287 407683382414353267987240931)
            ·
              refine ⟨611525073621529901980861397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407683382414353267987240931 611525073621529901980861397)
              ·
                refine ⟨14332618913004607077676439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 611525073621529901980861397 14332618913004607077676439)
                ·
                  refine ⟨21498928369506910616514659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332618913004607077676439 21498928369506910616514659)
                  ·
                    refine ⟨32248392554260365924771989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21498928369506910616514659 32248392554260365924771989)
                    ·
                      refine ⟨1511643400980954652723687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32248392554260365924771989 1511643400980954652723687)
                      ·
                        rfl

theorem cell23_2943915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_2943915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943915 prefixEnd_2943915 := by exact prefixLift 2943915
  have htrace : WordTrace (prefixWord ++ tailWord_2943915) baseStart_2943915 baseEnd_2943915 := by
    simpa [prefixWord, tailWord_2943915, baseEnd_2943915] using wordTrace_append hprefix tailTrace_2943915
  have hstable : (prefixWord ++ tailWord_2943915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943915).length < 2 ^ (prefixWord ++ tailWord_2943915).sum := by decide
  have hdescent : baseEnd_2943915 < baseStart_2943915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943919 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 5, 2, 2]
def baseStart_2943919 : Nat := 118140960795 + 2943919 * 2 ^ 59
def prefixEnd_2943919 : Nat := 4983230072969 + 3 ^ 40 * 2943919 * 2
def baseEnd_2943919 : Nat := 1511645454903572637073669

theorem tailTrace_2943919 : CollatzResearch.WordTrace tailWord_2943919 prefixEnd_2943919 1511645454903572637073669 := by
  unfold tailWord_2943919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107373547021691719181842811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71582364681127812787895207 107373547021691719181842811)
  ·
    refine ⟨161060320532537578772764217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107373547021691719181842811 161060320532537578772764217)
    ·
      refine ⟨120795240399403184079573163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161060320532537578772764217 120795240399403184079573163)
      ·
        refine ⟨181192860599104776119359745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120795240399403184079573163 181192860599104776119359745)
        ·
          refine ⟨135894645449328582089519809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181192860599104776119359745 135894645449328582089519809)
          ·
            refine ⟨101920984086996436567139857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135894645449328582089519809 101920984086996436567139857)
            ·
              refine ⟨76440738065247327425354893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101920984086996436567139857 76440738065247327425354893)
              ·
                refine ⟨28665276774467747784508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76440738065247327425354893 28665276774467747784508085)
                ·
                  refine ⟨2687369697606351354797633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28665276774467747784508085 2687369697606351354797633)
                  ·
                    refine ⟨2015527273204763516098225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687369697606351354797633 2015527273204763516098225)
                    ·
                      refine ⟨1511645454903572637073669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015527273204763516098225 1511645454903572637073669)
                      ·
                        rfl

theorem cell23_2943919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2, 2].length) (baseStart_2943919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943919 prefixEnd_2943919 := by exact prefixLift 2943919
  have htrace : WordTrace (prefixWord ++ tailWord_2943919) baseStart_2943919 baseEnd_2943919 := by
    simpa [prefixWord, tailWord_2943919, baseEnd_2943919] using wordTrace_append hprefix tailTrace_2943919
  have hstable : (prefixWord ++ tailWord_2943919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943919).length < 2 ^ (prefixWord ++ tailWord_2943919).sum := by decide
  have hdescent : baseEnd_2943919 < baseStart_2943919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943945 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2943945 : Nat := 118140960795 + 2943945 * 2 ^ 59
def prefixEnd_2943945 : Nat := 4983230072969 + 3 ^ 40 * 2943945 * 2
def baseEnd_2943945 : Nat := 1511658805400589535348549

theorem tailTrace_2943945 : CollatzResearch.WordTrace tailWord_2943945 prefixEnd_2943945 1511658805400589535348549 := by
  unfold tailWord_2943945
  simp only [CollatzResearch.WordTrace]
  refine ⟨107374495319597525622289289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71582996879731683748192859 107374495319597525622289289)
  ·
    refine ⟨80530871489698144216716967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107374495319597525622289289 80530871489698144216716967)
    ·
      refine ⟨120796307234547216325075451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80530871489698144216716967 120796307234547216325075451)
      ·
        refine ⟨181194460851820824487613177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120796307234547216325075451 181194460851820824487613177)
        ·
          refine ⟨135895845638865618365709883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181194460851820824487613177 135895845638865618365709883)
          ·
            refine ⟨203843768458298427548564825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135895845638865618365709883 203843768458298427548564825)
            ·
              refine ⟨152882826343723820661423619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203843768458298427548564825 152882826343723820661423619)
              ·
                refine ⟨229324239515585730992135429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152882826343723820661423619 229324239515585730992135429)
                ·
                  refine ⟨42998294909172324561025393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229324239515585730992135429 42998294909172324561025393)
                  ·
                    refine ⟨32248721181879243420769045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42998294909172324561025393 32248721181879243420769045)
                    ·
                      refine ⟨1511658805400589535348549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32248721181879243420769045 1511658805400589535348549)
                      ·
                        rfl

theorem cell23_2943945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2943945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2943945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2943945 prefixEnd_2943945 := by exact prefixLift 2943945
  have htrace : WordTrace (prefixWord ++ tailWord_2943945) baseStart_2943945 baseEnd_2943945 := by
    simpa [prefixWord, tailWord_2943945, baseEnd_2943945] using wordTrace_append hprefix tailTrace_2943945
  have hstable : (prefixWord ++ tailWord_2943945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943945).length < 2 ^ (prefixWord ++ tailWord_2943945).sum := by decide
  have hdescent : baseEnd_2943945 < baseStart_2943945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944026 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_2944026 : Nat := 118140960795 + 2944026 * 2 ^ 59
def prefixEnd_2944026 : Nat := 4983230072969 + 3 ^ 40 * 2944026 * 2
def baseEnd_2944026 : Nat := 1511700397333603718435677

theorem tailTrace_2944026 : CollatzResearch.WordTrace tailWord_2944026 prefixEnd_2944026 1511700397333603718435677 := by
  unfold tailWord_2944026
  simp only [CollatzResearch.WordTrace]
  refine ⟨26844362408076019113996983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71584966421536050970658621 26844362408076019113996983)
  ·
    refine ⟨40266543612114028670995475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26844362408076019113996983 40266543612114028670995475)
    ·
      refine ⟨60399815418171043006493213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40266543612114028670995475 60399815418171043006493213)
      ·
        refine ⟨22649930781814141127434955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60399815418171043006493213 22649930781814141127434955)
        ·
          refine ⟨33974896172721211691152433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22649930781814141127434955 33974896172721211691152433)
          ·
            refine ⟨25481172129540908768364325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33974896172721211691152433 25481172129540908768364325)
            ·
              refine ⟨4777719774288920394068311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25481172129540908768364325 4777719774288920394068311)
              ·
                refine ⟨7166579661433380591102467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777719774288920394068311 7166579661433380591102467)
                ·
                  refine ⟨10749869492150070886653701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7166579661433380591102467 10749869492150070886653701)
                  ·
                    refine ⟨2015600529778138291247569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10749869492150070886653701 2015600529778138291247569)
                    ·
                      refine ⟨1511700397333603718435677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015600529778138291247569 1511700397333603718435677)
                      ·
                        rfl

theorem cell23_2944026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_2944026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944026 prefixEnd_2944026 := by exact prefixLift 2944026
  have htrace : WordTrace (prefixWord ++ tailWord_2944026) baseStart_2944026 baseEnd_2944026 := by
    simpa [prefixWord, tailWord_2944026, baseEnd_2944026] using wordTrace_append hprefix tailTrace_2944026
  have hstable : (prefixWord ++ tailWord_2944026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944026).length < 2 ^ (prefixWord ++ tailWord_2944026).sum := by decide
  have hdescent : baseEnd_2944026 < baseStart_2944026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944060 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_2944060 : Nat := 118140960795 + 2944060 * 2 ^ 59
def prefixEnd_2944060 : Nat := 4983230072969 + 3 ^ 40 * 2944060 * 2
def baseEnd_2944060 : Nat := 1511717855675856585410521

theorem tailTrace_2944060 : CollatzResearch.WordTrace tailWord_2944060 prefixEnd_2944060 1511717855675856585410521 := by
  unfold tailWord_2944060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53689344857090450131362817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71585793142787266841817089 53689344857090450131362817)
  ·
    refine ⟨40267008642817837598522113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53689344857090450131362817 40267008642817837598522113)
    ·
      refine ⟨30200256482113378198891585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40267008642817837598522113 30200256482113378198891585)
      ·
        refine ⟨22650192361585033649168689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30200256482113378198891585 22650192361585033649168689)
        ·
          refine ⟨16987644271188775236876517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22650192361585033649168689 16987644271188775236876517)
          ·
            refine ⟨3185183300847895356914347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16987644271188775236876517 3185183300847895356914347)
            ·
              refine ⟨4777774951271843035371521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185183300847895356914347 4777774951271843035371521)
              ·
                refine ⟨3583331213453882276528641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777774951271843035371521 3583331213453882276528641)
                ·
                  refine ⟨2687498410090411707396481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583331213453882276528641 2687498410090411707396481)
                  ·
                    refine ⟨2015623807567808780547361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687498410090411707396481 2015623807567808780547361)
                    ·
                      refine ⟨1511717855675856585410521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015623807567808780547361 1511717855675856585410521)
                      ·
                        rfl

theorem cell23_2944060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_2944060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944060 prefixEnd_2944060 := by exact prefixLift 2944060
  have htrace : WordTrace (prefixWord ++ tailWord_2944060) baseStart_2944060 baseEnd_2944060 := by
    simpa [prefixWord, tailWord_2944060, baseEnd_2944060] using wordTrace_append hprefix tailTrace_2944060
  have hstable : (prefixWord ++ tailWord_2944060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944060).length < 2 ^ (prefixWord ++ tailWord_2944060).sum := by decide
  have hdescent : baseEnd_2944060 < baseStart_2944060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944069 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_2944069 : Nat := 118140960795 + 2944069 * 2 ^ 59
def prefixEnd_2944069 : Nat := 4983230072969 + 3 ^ 40 * 2944069 * 2
def baseEnd_2944069 : Nat := 1511722477001747050197979

theorem tailTrace_2944069 : CollatzResearch.WordTrace tailWord_2944069 prefixEnd_2944069 1511722477001747050197979 := by
  unfold tailWord_2944069
  simp only [CollatzResearch.WordTrace]
  refine ⟨107379017971148294799803261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71586011980765529866535507 107379017971148294799803261)
  ·
    refine ⟨40267131739180610549926223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107379017971148294799803261 40267131739180610549926223)
    ·
      refine ⟨60400697608770915824889335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40267131739180610549926223 60400697608770915824889335)
      ·
        refine ⟨90601046413156373737334003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60400697608770915824889335 90601046413156373737334003)
        ·
          refine ⟨135901569619734560606001005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90601046413156373737334003 135901569619734560606001005)
          ·
            refine ⟨50963088607400460227250377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135901569619734560606001005 50963088607400460227250377)
            ·
              refine ⟨38222316455550345170437783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50963088607400460227250377 38222316455550345170437783)
              ·
                refine ⟨57333474683325517755656675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38222316455550345170437783 57333474683325517755656675)
                ·
                  refine ⟨86000212024988276633485013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57333474683325517755656675 86000212024988276633485013)
                  ·
                    refine ⟨2015629969335662733597305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86000212024988276633485013 2015629969335662733597305)
                    ·
                      refine ⟨1511722477001747050197979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015629969335662733597305 1511722477001747050197979)
                      ·
                        rfl

theorem cell23_2944069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_2944069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944069 prefixEnd_2944069 := by exact prefixLift 2944069
  have htrace : WordTrace (prefixWord ++ tailWord_2944069) baseStart_2944069 baseEnd_2944069 := by
    simpa [prefixWord, tailWord_2944069, baseEnd_2944069] using wordTrace_append hprefix tailTrace_2944069
  have hstable : (prefixWord ++ tailWord_2944069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944069).length < 2 ^ (prefixWord ++ tailWord_2944069).sum := by decide
  have hdescent : baseEnd_2944069 < baseStart_2944069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944072 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2944072 : Nat := 118140960795 + 2944072 * 2 ^ 59
def prefixEnd_2944072 : Nat := 4983230072969 + 3 ^ 40 * 2944072 * 2
def baseEnd_2944072 : Nat := 1511724017443710538460465

theorem tailTrace_2944072 : CollatzResearch.WordTrace tailWord_2944072 prefixEnd_2944072 1511724017443710538460465 := by
  unfold tailWord_2944072
  simp only [CollatzResearch.WordTrace]
  refine ⟨53689563695068713156081235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71586084926758284208108313 53689563695068713156081235)
  ·
    refine ⟨80534345542603069734121853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53689563695068713156081235 80534345542603069734121853)
    ·
      refine ⟨30200379578476151150295695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80534345542603069734121853 30200379578476151150295695)
      ·
        refine ⟨45300569367714226725443543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30200379578476151150295695 45300569367714226725443543)
        ·
          refine ⟨67950854051571340088165315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45300569367714226725443543 67950854051571340088165315)
          ·
            refine ⟨101926281077357010132247973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67950854051571340088165315 101926281077357010132247973)
            ·
              refine ⟨19111177702004439399796495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101926281077357010132247973 19111177702004439399796495)
              ·
                refine ⟨28666766553006659099694743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19111177702004439399796495 28666766553006659099694743)
                ·
                  refine ⟨43000149829509988649542115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28666766553006659099694743 43000149829509988649542115)
                  ·
                    refine ⟨64500224744264982974313173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43000149829509988649542115 64500224744264982974313173)
                    ·
                      refine ⟨1511724017443710538460465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64500224744264982974313173 1511724017443710538460465)
                      ·
                        rfl

theorem cell23_2944072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2944072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944072 prefixEnd_2944072 := by exact prefixLift 2944072
  have htrace : WordTrace (prefixWord ++ tailWord_2944072) baseStart_2944072 baseEnd_2944072 := by
    simpa [prefixWord, tailWord_2944072, baseEnd_2944072] using wordTrace_append hprefix tailTrace_2944072
  have hstable : (prefixWord ++ tailWord_2944072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944072).length < 2 ^ (prefixWord ++ tailWord_2944072).sum := by decide
  have hdescent : baseEnd_2944072 < baseStart_2944072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944077 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_2944077 : Nat := 118140960795 + 2944077 * 2 ^ 59
def prefixEnd_2944077 : Nat := 4983230072969 + 3 ^ 40 * 2944077 * 2
def baseEnd_2944077 : Nat := 1511726584846983018897943

theorem tailTrace_2944077 : CollatzResearch.WordTrace tailWord_2944077 prefixEnd_2944077 1511726584846983018897943 := by
  unfold tailWord_2944077
  simp only [CollatzResearch.WordTrace]
  refine ⟨107379309755119312166094485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71586206503412874777396323 107379309755119312166094485)
  ·
    refine ⟨5033405144771217757785679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107379309755119312166094485 5033405144771217757785679)
    ·
      refine ⟨7550107717156826636678519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033405144771217757785679 7550107717156826636678519)
      ·
        refine ⟨11325161575735239955017779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550107717156826636678519 11325161575735239955017779)
        ·
          refine ⟨16987742363602859932526669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325161575735239955017779 16987742363602859932526669)
          ·
            refine ⟨6370403386351072474697501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16987742363602859932526669 6370403386351072474697501)
            ·
              refine ⟨2388901269881652178011563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6370403386351072474697501 2388901269881652178011563)
              ·
                refine ⟨3583351904822478267017345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388901269881652178011563 3583351904822478267017345)
                ·
                  refine ⟨2687513928616858700263009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583351904822478267017345 2687513928616858700263009)
                  ·
                    refine ⟨2015635446462644025197257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687513928616858700263009 2015635446462644025197257)
                    ·
                      refine ⟨1511726584846983018897943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015635446462644025197257 1511726584846983018897943)
                      ·
                        rfl

theorem cell23_2944077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_2944077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944077 prefixEnd_2944077 := by exact prefixLift 2944077
  have htrace : WordTrace (prefixWord ++ tailWord_2944077) baseStart_2944077 baseEnd_2944077 := by
    simpa [prefixWord, tailWord_2944077, baseEnd_2944077] using wordTrace_append hprefix tailTrace_2944077
  have hstable : (prefixWord ++ tailWord_2944077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944077).length < 2 ^ (prefixWord ++ tailWord_2944077).sum := by decide
  have hdescent : baseEnd_2944077 < baseStart_2944077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944099 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2944099 : Nat := 118140960795 + 2944099 * 2 ^ 59
def prefixEnd_2944099 : Nat := 4983230072969 + 3 ^ 40 * 2944099 * 2
def baseEnd_2944099 : Nat := 1511737881421381932822841

theorem tailTrace_2944099 : CollatzResearch.WordTrace tailWord_2944099 prefixEnd_2944099 1511737881421381932822841 := by
  unfold tailWord_2944099
  simp only [CollatzResearch.WordTrace]
  refine ⟨107380112161039609923395351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71586741440693073282263567 107380112161039609923395351)
  ·
    refine ⟨161070168241559414885093027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107380112161039609923395351 161070168241559414885093027)
    ·
      refine ⟨241605252362339122327639541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161070168241559414885093027 241605252362339122327639541)
      ·
        refine ⟨22650492408969292718216207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241605252362339122327639541 22650492408969292718216207)
        ·
          refine ⟨33975738613453939077324311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22650492408969292718216207 33975738613453939077324311)
          ·
            refine ⟨50963607920180908615986467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33975738613453939077324311 50963607920180908615986467)
            ·
              refine ⟨76445411880271362923979701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50963607920180908615986467 76445411880271362923979701)
              ·
                refine ⟨7166757363775440274123097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76445411880271362923979701 7166757363775440274123097)
                ·
                  refine ⟨5375068022831580205592323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7166757363775440274123097 5375068022831580205592323)
                  ·
                    refine ⟨8062602034247370308388485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375068022831580205592323 8062602034247370308388485)
                    ·
                      refine ⟨1511737881421381932822841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8062602034247370308388485 1511737881421381932822841)
                      ·
                        rfl

theorem cell23_2944099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2944099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944099 prefixEnd_2944099 := by exact prefixLift 2944099
  have htrace : WordTrace (prefixWord ++ tailWord_2944099) baseStart_2944099 baseEnd_2944099 := by
    simpa [prefixWord, tailWord_2944099, baseEnd_2944099] using wordTrace_append hprefix tailTrace_2944099
  have hstable : (prefixWord ++ tailWord_2944099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944099).length < 2 ^ (prefixWord ++ tailWord_2944099).sum := by decide
  have hdescent : baseEnd_2944099 < baseStart_2944099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944173 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2944173 : Nat := 118140960795 + 2944173 * 2 ^ 59
def prefixEnd_2944173 : Nat := 4983230072969 + 3 ^ 40 * 2944173 * 2
def baseEnd_2944173 : Nat := 167975097665534960366389

theorem tailTrace_2944173 : CollatzResearch.WordTrace tailWord_2944173 prefixEnd_2944173 167975097665534960366389 := by
  unfold tailWord_2944173
  simp only [CollatzResearch.WordTrace]
  refine ⟨107382811162771520561589173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71588540775181013707726115 107382811162771520561589173)
  ·
    refine ⟨10067138546509830052648985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107382811162771520561589173 10067138546509830052648985)
    ·
      refine ⟨7550353909882372539486739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10067138546509830052648985 7550353909882372539486739)
      ·
        refine ⟨11325530864823558809230109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550353909882372539486739 11325530864823558809230109)
        ·
          refine ⟨4247074074308834553461291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11325530864823558809230109 4247074074308834553461291)
          ·
            refine ⟨6370611111463251830191937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247074074308834553461291 6370611111463251830191937)
            ·
              refine ⟨4777958333597438872643953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6370611111463251830191937 4777958333597438872643953)
              ·
                refine ⟨3583468750198079154482965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777958333597438872643953 3583468750198079154482965)
                ·
                  refine ⟨167975097665534960366389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3583468750198079154482965 167975097665534960366389)
                  ·
                    rfl

theorem cell23_2944173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2944173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944173 prefixEnd_2944173 := by exact prefixLift 2944173
  have htrace : WordTrace (prefixWord ++ tailWord_2944173) baseStart_2944173 baseEnd_2944173 := by
    simpa [prefixWord, tailWord_2944173, baseEnd_2944173] using wordTrace_append hprefix tailTrace_2944173
  have hstable : (prefixWord ++ tailWord_2944173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944173).length < 2 ^ (prefixWord ++ tailWord_2944173).sum := by decide
  have hdescent : baseEnd_2944173 < baseStart_2944173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944177 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 1, 4]
def baseStart_2944177 : Nat := 118140960795 + 2944177 * 2 ^ 59
def prefixEnd_2944177 : Nat := 4983230072969 + 3 ^ 40 * 2944177 * 2
def baseEnd_2944177 : Nat := 503925977637477542549161

theorem tailTrace_2944177 : CollatzResearch.WordTrace tailWord_2944177 prefixEnd_2944177 503925977637477542549161 := by
  unfold tailWord_2944177
  simp only [CollatzResearch.WordTrace]
  refine ⟨107382957054757029244734785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71588638036504686163156523 107382957054757029244734785)
  ·
    refine ⟨80537217791067771933551089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107382957054757029244734785 80537217791067771933551089)
    ·
      refine ⟨60402913343300828950163317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80537217791067771933551089 60402913343300828950163317)
      ·
        refine ⟨5662773125934452714077811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60402913343300828950163317 5662773125934452714077811)
        ·
          refine ⟨8494159688901679071116717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662773125934452714077811 8494159688901679071116717)
          ·
            refine ⟨3185309883338129651668769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8494159688901679071116717 3185309883338129651668769)
            ·
              refine ⟨2388982412503597238751577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185309883338129651668769 2388982412503597238751577)
              ·
                refine ⟨1791736809377697929063683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388982412503597238751577 1791736809377697929063683)
                ·
                  refine ⟨2687605214066546893595525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791736809377697929063683 2687605214066546893595525)
                  ·
                    refine ⟨503925977637477542549161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2687605214066546893595525 503925977637477542549161)
                    ·
                      rfl

theorem cell23_2944177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_2944177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944177 prefixEnd_2944177 := by exact prefixLift 2944177
  have htrace : WordTrace (prefixWord ++ tailWord_2944177) baseStart_2944177 baseEnd_2944177 := by
    simpa [prefixWord, tailWord_2944177, baseEnd_2944177] using wordTrace_append hprefix tailTrace_2944177
  have hstable : (prefixWord ++ tailWord_2944177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944177).length < 2 ^ (prefixWord ++ tailWord_2944177).sum := by decide
  have hdescent : baseEnd_2944177 < baseStart_2944177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944223 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 1, 1, 4]
def baseStart_2944223 : Nat := 118140960795 + 2944223 * 2 ^ 59
def prefixEnd_2944223 : Nat := 4983230072969 + 3 ^ 40 * 2944223 * 2
def baseEnd_2944223 : Nat := 1511801553022539447672271

theorem tailTrace_2944223 : CollatzResearch.WordTrace tailWord_2944223 prefixEnd_2944223 1511801553022539447672271 := by
  unfold tailWord_2944223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107384634812590379100909323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71589756541726919400606215 107384634812590379100909323)
  ·
    refine ⟨161076952218885568651363985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107384634812590379100909323 161076952218885568651363985)
    ·
      refine ⟨120807714164164176488522989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161076952218885568651363985 120807714164164176488522989)
      ·
        refine ⟨45302892811561566183196121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120807714164164176488522989 45302892811561566183196121)
        ·
          refine ⟨33977169608671174637397091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45302892811561566183196121 33977169608671174637397091)
          ·
            refine ⟨50965754413006761956095637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33977169608671174637397091 50965754413006761956095637)
            ·
              refine ⟨2389019738109691966691983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50965754413006761956095637 2389019738109691966691983)
              ·
                refine ⟨3583529607164537950037975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389019738109691966691983 3583529607164537950037975)
                ·
                  refine ⟨5375294410746806925056963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583529607164537950037975 5375294410746806925056963)
                  ·
                    refine ⟨8062941616120210387585445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5375294410746806925056963 8062941616120210387585445)
                    ·
                      refine ⟨1511801553022539447672271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8062941616120210387585445 1511801553022539447672271)
                      ·
                        rfl

theorem cell23_2944223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_2944223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944223 prefixEnd_2944223 := by exact prefixLift 2944223
  have htrace : WordTrace (prefixWord ++ tailWord_2944223) baseStart_2944223 baseEnd_2944223 := by
    simpa [prefixWord, tailWord_2944223, baseEnd_2944223] using wordTrace_append hprefix tailTrace_2944223
  have hstable : (prefixWord ++ tailWord_2944223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944223).length < 2 ^ (prefixWord ++ tailWord_2944223).sum := by decide
  have hdescent : baseEnd_2944223 < baseStart_2944223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944260 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2944260 : Nat := 118140960795 + 2944260 * 2 ^ 59
def prefixEnd_2944260 : Nat := 4983230072969 + 3 ^ 40 * 2944260 * 2
def baseEnd_2944260 : Nat := 1511820551806755802909601

theorem tailTrace_2944260 : CollatzResearch.WordTrace tailWord_2944260 prefixEnd_2944260 1511820551806755802909601 := by
  unfold tailWord_2944260
  simp only [CollatzResearch.WordTrace]
  refine ⟨53692992156728167210003117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71590656208970889613337489 53692992156728167210003117)
  ·
    refine ⟨20134872058773062703751169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53692992156728167210003117 20134872058773062703751169)
    ·
      refine ⟨15101154044079797027813377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20134872058773062703751169 15101154044079797027813377)
      ·
        refine ⟨11325865533059847770860033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15101154044079797027813377 11325865533059847770860033)
        ·
          refine ⟨8494399149794885828145025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11325865533059847770860033 8494399149794885828145025)
          ·
            refine ⟨6370799362346164371108769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8494399149794885828145025 6370799362346164371108769)
            ·
              refine ⟨4778099521759623278331577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6370799362346164371108769 4778099521759623278331577)
              ·
                refine ⟨3583574641319717458748683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778099521759623278331577 3583574641319717458748683)
                ·
                  refine ⟨5375361961979576188123025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583574641319717458748683 5375361961979576188123025)
                  ·
                    refine ⟨4031521471484682141092269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375361961979576188123025 4031521471484682141092269)
                    ·
                      refine ⟨1511820551806755802909601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4031521471484682141092269 1511820551806755802909601)
                      ·
                        rfl

theorem cell23_2944260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2944260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944260 prefixEnd_2944260 := by exact prefixLift 2944260
  have htrace : WordTrace (prefixWord ++ tailWord_2944260) baseStart_2944260 baseEnd_2944260 := by
    simpa [prefixWord, tailWord_2944260, baseEnd_2944260] using wordTrace_append hprefix tailTrace_2944260
  have hstable : (prefixWord ++ tailWord_2944260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944260).length < 2 ^ (prefixWord ++ tailWord_2944260).sum := by decide
  have hdescent : baseEnd_2944260 < baseStart_2944260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944307 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 2, 1, 3]
def baseStart_2944307 : Nat := 118140960795 + 2944307 * 2 ^ 59
def prefixEnd_2944307 : Nat := 4983230072969 + 3 ^ 40 * 2944307 * 2
def baseEnd_2944307 : Nat := 1511844685397517119021885

theorem tailTrace_2944307 : CollatzResearch.WordTrace tailWord_2944307 prefixEnd_2944307 1511844685397517119021885 := by
  unfold tailWord_2944307
  simp only [CollatzResearch.WordTrace]
  refine ⟨107387698544286061446967175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71591799029524040964644783 107387698544286061446967175)
  ·
    refine ⟨161081547816429092170450763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107387698544286061446967175 161081547816429092170450763)
    ·
      refine ⟨241622321724643638255676145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161081547816429092170450763 241622321724643638255676145)
      ·
        refine ⟨181216741293482728691757109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241622321724643638255676145 181216741293482728691757109)
        ·
          refine ⟨16989069496264005814852229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181216741293482728691757109 16989069496264005814852229)
          ·
            refine ⟨3185450530549501090284793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16989069496264005814852229 3185450530549501090284793)
            ·
              refine ⟨2389087897912125817713595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185450530549501090284793 2389087897912125817713595)
              ·
                refine ⟨3583631846868188726570393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389087897912125817713595 3583631846868188726570393)
                ·
                  refine ⟨2687723885151141544927795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583631846868188726570393 2687723885151141544927795)
                  ·
                    refine ⟨4031585827726712317391693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2687723885151141544927795 4031585827726712317391693)
                    ·
                      refine ⟨1511844685397517119021885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4031585827726712317391693 1511844685397517119021885)
                      ·
                        rfl

theorem cell23_2944307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 1, 3].length) (baseStart_2944307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944307 prefixEnd_2944307 := by exact prefixLift 2944307
  have htrace : WordTrace (prefixWord ++ tailWord_2944307) baseStart_2944307 baseEnd_2944307 := by
    simpa [prefixWord, tailWord_2944307, baseEnd_2944307] using wordTrace_append hprefix tailTrace_2944307
  have hstable : (prefixWord ++ tailWord_2944307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944307).length < 2 ^ (prefixWord ++ tailWord_2944307).sum := by decide
  have hdescent : baseEnd_2944307 < baseStart_2944307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944316 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2944316 : Nat := 118140960795 + 2944316 * 2 ^ 59
def prefixEnd_2944316 : Nat := 4983230072969 + 3 ^ 40 * 2944316 * 2
def baseEnd_2944316 : Nat := 1511849306723407583809343

theorem tailTrace_2944316 : CollatzResearch.WordTrace tailWord_2944316 prefixEnd_2944316 1511849306723407583809343 := by
  unfold tailWord_2944316
  simp only [CollatzResearch.WordTrace]
  refine ⟨53694013400626727992022401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71592017867502303989363201 53694013400626727992022401)
  ·
    refine ⟨40270510050470045994016801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53694013400626727992022401 40270510050470045994016801)
    ·
      refine ⟨30202882537852534495512601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40270510050470045994016801 30202882537852534495512601)
      ·
        refine ⟨22652161903389400871634451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30202882537852534495512601 22652161903389400871634451)
        ·
          refine ⟨33978242855084101307451677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22652161903389400871634451 33978242855084101307451677)
          ·
            refine ⟨12741841070656537990294379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33978242855084101307451677 12741841070656537990294379)
            ·
              refine ⟨19112761605984806985441569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12741841070656537990294379 19112761605984806985441569)
              ·
                refine ⟨14334571204488605239081177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19112761605984806985441569 14334571204488605239081177)
                ·
                  refine ⟨10750928403366453929310883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14334571204488605239081177 10750928403366453929310883)
                  ·
                    refine ⟨16126392605049680893966325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10750928403366453929310883 16126392605049680893966325)
                    ·
                      refine ⟨1511849306723407583809343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16126392605049680893966325 1511849306723407583809343)
                      ·
                        rfl

theorem cell23_2944316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2944316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944316 prefixEnd_2944316 := by exact prefixLift 2944316
  have htrace : WordTrace (prefixWord ++ tailWord_2944316) baseStart_2944316 baseEnd_2944316 := by
    simpa [prefixWord, tailWord_2944316, baseEnd_2944316] using wordTrace_append hprefix tailTrace_2944316
  have hstable : (prefixWord ++ tailWord_2944316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944316).length < 2 ^ (prefixWord ++ tailWord_2944316).sum := by decide
  have hdescent : baseEnd_2944316 < baseStart_2944316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944317 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2944317 : Nat := 118140960795 + 2944317 * 2 ^ 59
def prefixEnd_2944317 : Nat := 4983230072969 + 3 ^ 40 * 2944317 * 2
def baseEnd_2944317 : Nat := 1511849820204062079896839

theorem tailTrace_2944317 : CollatzResearch.WordTrace tailWord_2944317 prefixEnd_2944317 1511849820204062079896839 := by
  unfold tailWord_2944317
  simp only [CollatzResearch.WordTrace]
  refine ⟨107388063274249833154831205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71592042182833222103220803 107388063274249833154831205)
  ·
    refine ⟨20135261863921843716530851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107388063274249833154831205 20135261863921843716530851)
    ·
      refine ⟨30202892795882765574796277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20135261863921843716530851 30202892795882765574796277)
      ·
        refine ⟨2831521199614009272637151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30202892795882765574796277 2831521199614009272637151)
        ·
          refine ⟨4247281799421013908955727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831521199614009272637151 4247281799421013908955727)
          ·
            refine ⟨6370922699131520863433591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247281799421013908955727 6370922699131520863433591)
            ·
              refine ⟨9556384048697281295150387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370922699131520863433591 9556384048697281295150387)
              ·
                refine ⟨14334576073045921942725581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556384048697281295150387 14334576073045921942725581)
                ·
                  refine ⟨5375466027392220728522093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14334576073045921942725581 5375466027392220728522093)
                  ·
                    refine ⟨2015799760272082773195785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5375466027392220728522093 2015799760272082773195785)
                    ·
                      refine ⟨1511849820204062079896839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015799760272082773195785 1511849820204062079896839)
                      ·
                        rfl

theorem cell23_2944317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2944317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944317 prefixEnd_2944317 := by exact prefixLift 2944317
  have htrace : WordTrace (prefixWord ++ tailWord_2944317) baseStart_2944317 baseEnd_2944317 := by
    simpa [prefixWord, tailWord_2944317, baseEnd_2944317] using wordTrace_append hprefix tailTrace_2944317
  have hstable : (prefixWord ++ tailWord_2944317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944317).length < 2 ^ (prefixWord ++ tailWord_2944317).sum := by decide
  have hdescent : baseEnd_2944317 < baseStart_2944317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944342 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2944342 : Nat := 118140960795 + 2944342 * 2 ^ 59
def prefixEnd_2944342 : Nat := 4983230072969 + 3 ^ 40 * 2944342 * 2
def baseEnd_2944342 : Nat := 1511862657220424482084225

theorem tailTrace_2944342 : CollatzResearch.WordTrace tailWord_2944342 prefixEnd_2944342 1511862657220424482084225 := by
  unfold tailWord_2944342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711810943697453901530705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71592650066106174949660853 6711810943697453901530705)
  ·
    refine ⟨5033858207773090426148029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6711810943697453901530705 5033858207773090426148029)
    ·
      refine ⟨1887696827914908909805511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5033858207773090426148029 1887696827914908909805511)
      ·
        refine ⟨2831545241872363364708267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887696827914908909805511 2831545241872363364708267)
        ·
          refine ⟨4247317862808545047062401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831545241872363364708267 4247317862808545047062401)
          ·
            refine ⟨3185488397106408785296801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4247317862808545047062401 3185488397106408785296801)
            ·
              refine ⟨2389116297829806588972601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185488397106408785296801 2389116297829806588972601)
              ·
                refine ⟨1791837223372354941729451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2389116297829806588972601 1791837223372354941729451)
                ·
                  refine ⟨2687755835058532412594177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791837223372354941729451 2687755835058532412594177)
                  ·
                    refine ⟨2015816876293899309445633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687755835058532412594177 2015816876293899309445633)
                    ·
                      refine ⟨1511862657220424482084225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015816876293899309445633 1511862657220424482084225)
                      ·
                        rfl

theorem cell23_2944342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2944342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944342 prefixEnd_2944342 := by exact prefixLift 2944342
  have htrace : WordTrace (prefixWord ++ tailWord_2944342) baseStart_2944342 baseEnd_2944342 := by
    simpa [prefixWord, tailWord_2944342, baseEnd_2944342] using wordTrace_append hprefix tailTrace_2944342
  have hstable : (prefixWord ++ tailWord_2944342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944342).length < 2 ^ (prefixWord ++ tailWord_2944342).sum := by decide
  have hdescent : baseEnd_2944342 < baseStart_2944342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944416 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2944416 : Nat := 118140960795 + 2944416 * 2 ^ 59
def prefixEnd_2944416 : Nat := 4983230072969 + 3 ^ 40 * 2944416 * 2
def baseEnd_2944416 : Nat := 1511900654788857192558883

theorem tailTrace_2944416 : CollatzResearch.WordTrace tailWord_2944416 prefixEnd_2944416 1511900654788857192558883 := by
  unfold tailWord_2944416
  simp only [CollatzResearch.WordTrace]
  refine ⟨53695837050445586531342551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71594449400594115375123401 53695837050445586531342551)
  ·
    refine ⟨80543755575668379797013827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53695837050445586531342551 80543755575668379797013827)
    ·
      refine ⟨120815633363502569695520741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80543755575668379797013827 120815633363502569695520741)
      ·
        refine ⟨22652931255656731817910139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120815633363502569695520741 22652931255656731817910139)
        ·
          refine ⟨33979396883485097726865209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22652931255656731817910139 33979396883485097726865209)
          ·
            refine ⟨25484547662613823295148907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33979396883485097726865209 25484547662613823295148907)
            ·
              refine ⟨38226821493920734942723361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25484547662613823295148907 38226821493920734942723361)
              ·
                refine ⟨28670116120440551207042521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38226821493920734942723361 28670116120440551207042521)
                ·
                  refine ⟨21502587090330413405281891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28670116120440551207042521 21502587090330413405281891)
                  ·
                    refine ⟨32253880635495620107922837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21502587090330413405281891 32253880635495620107922837)
                    ·
                      refine ⟨1511900654788857192558883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32253880635495620107922837 1511900654788857192558883)
                      ·
                        rfl

theorem cell23_2944416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2944416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944416 prefixEnd_2944416 := by exact prefixLift 2944416
  have htrace : WordTrace (prefixWord ++ tailWord_2944416) baseStart_2944416 baseEnd_2944416 := by
    simpa [prefixWord, tailWord_2944416, baseEnd_2944416] using wordTrace_append hprefix tailTrace_2944416
  have hstable : (prefixWord ++ tailWord_2944416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944416).length < 2 ^ (prefixWord ++ tailWord_2944416).sum := by decide
  have hdescent : baseEnd_2944416 < baseStart_2944416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944423 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2944423 : Nat := 118140960795 + 2944423 * 2 ^ 59
def prefixEnd_2944423 : Nat := 4983230072969 + 3 ^ 40 * 2944423 * 2
def baseEnd_2944423 : Nat := 1511904249153438665171351

theorem tailTrace_2944423 : CollatzResearch.WordTrace tailWord_2944423 prefixEnd_2944423 1511904249153438665171351 := by
  unfold tailWord_2944423
  simp only [CollatzResearch.WordTrace]
  refine ⟨107391929411865813258189923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71594619607910542172126615 107391929411865813258189923)
  ·
    refine ⟨161087894117798719887284885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107391929411865813258189923 161087894117798719887284885)
    ·
      refine ⟨7550995036771814994716479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161087894117798719887284885 7550995036771814994716479)
      ·
        refine ⟨11326492555157722492074719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550995036771814994716479 11326492555157722492074719)
        ·
          refine ⟨16989738832736583738112079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11326492555157722492074719 16989738832736583738112079)
          ·
            refine ⟨25484608249104875607168119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16989738832736583738112079 25484608249104875607168119)
            ·
              refine ⟨38226912373657313410752179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25484608249104875607168119 38226912373657313410752179)
              ·
                refine ⟨57340368560485970116128269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38226912373657313410752179 57340368560485970116128269)
                ·
                  refine ⟨21502638210182238793548101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57340368560485970116128269 21502638210182238793548101)
                  ·
                    refine ⟨4031744664409169773790269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21502638210182238793548101 4031744664409169773790269)
                    ·
                      refine ⟨1511904249153438665171351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4031744664409169773790269 1511904249153438665171351)
                      ·
                        rfl

theorem cell23_2944423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2944423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944423 prefixEnd_2944423 := by exact prefixLift 2944423
  have htrace : WordTrace (prefixWord ++ tailWord_2944423) baseStart_2944423 baseEnd_2944423 := by
    simpa [prefixWord, tailWord_2944423, baseEnd_2944423] using wordTrace_append hprefix tailTrace_2944423
  have hstable : (prefixWord ++ tailWord_2944423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944423).length < 2 ^ (prefixWord ++ tailWord_2944423).sum := by decide
  have hdescent : baseEnd_2944423 < baseStart_2944423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944477 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 6]
def baseStart_2944477 : Nat := 118140960795 + 2944477 * 2 ^ 59
def prefixEnd_2944477 : Nat := 4983230072969 + 3 ^ 40 * 2944477 * 2
def baseEnd_2944477 : Nat := 167992441900975717099567

theorem tailTrace_2944477 : CollatzResearch.WordTrace tailWord_2944477 prefixEnd_2944477 167992441900975717099567 := by
  unfold tailWord_2944477
  simp only [CollatzResearch.WordTrace]
  refine ⟨107393898953670180480655685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71595932635780120320437123 107393898953670180480655685)
  ·
    refine ⟨20136356053813158840122941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107393898953670180480655685 20136356053813158840122941)
    ·
      refine ⟨7551133520179934565046103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20136356053813158840122941 7551133520179934565046103)
      ·
        refine ⟨11326700280269901847569155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551133520179934565046103 11326700280269901847569155)
        ·
          refine ⟨16990050420404852771353733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11326700280269901847569155 16990050420404852771353733)
          ·
            refine ⟨3185634453825909894628825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16990050420404852771353733 3185634453825909894628825)
            ·
              refine ⟨2389225840369432420971619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185634453825909894628825 2389225840369432420971619)
              ·
                refine ⟨3583838760554148631457429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389225840369432420971619 3583838760554148631457429)
                ·
                  refine ⟨167992441900975717099567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3583838760554148631457429 167992441900975717099567)
                  ·
                    rfl

theorem cell23_2944477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_2944477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944477 prefixEnd_2944477 := by exact prefixLift 2944477
  have htrace : WordTrace (prefixWord ++ tailWord_2944477) baseStart_2944477 baseEnd_2944477 := by
    simpa [prefixWord, tailWord_2944477, baseEnd_2944477] using wordTrace_append hprefix tailTrace_2944477
  have hstable : (prefixWord ++ tailWord_2944477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944477).length < 2 ^ (prefixWord ++ tailWord_2944477).sum := by decide
  have hdescent : baseEnd_2944477 < baseStart_2944477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944490 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2944490 : Nat := 118140960795 + 2944490 * 2 ^ 59
def prefixEnd_2944490 : Nat := 4983230072969 + 3 ^ 40 * 2944490 * 2
def baseEnd_2944490 : Nat := 503979550785763301011181

theorem tailTrace_2944490 : CollatzResearch.WordTrace tailWord_2944490 prefixEnd_2944490 503979550785763301011181 := by
  unfold tailWord_2944490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26848593275655770925219731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71596248735082055800585949 26848593275655770925219731)
  ·
    refine ⟨40272889913483656387829597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26848593275655770925219731 40272889913483656387829597)
    ·
      refine ⟨15102333717556371145436099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40272889913483656387829597 15102333717556371145436099)
      ·
        refine ⟨22653500576334556718154149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15102333717556371145436099 22653500576334556718154149)
        ·
          refine ⟨4247531358062729384653903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22653500576334556718154149 4247531358062729384653903)
          ·
            refine ⟨6371297037094094076980855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247531358062729384653903 6371297037094094076980855)
            ·
              refine ⟨9556945555641141115471283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6371297037094094076980855 9556945555641141115471283)
              ·
                refine ⟨14335418333461711673206925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556945555641141115471283 14335418333461711673206925)
                ·
                  refine ⟨5375781875048141877452597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14335418333461711673206925 5375781875048141877452597)
                  ·
                    refine ⟨503979550785763301011181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5375781875048141877452597 503979550785763301011181)
                    ·
                      rfl

theorem cell23_2944490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2944490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944490 prefixEnd_2944490 := by exact prefixLift 2944490
  have htrace : WordTrace (prefixWord ++ tailWord_2944490) baseStart_2944490 baseEnd_2944490 := by
    simpa [prefixWord, tailWord_2944490, baseEnd_2944490] using wordTrace_append hprefix tailTrace_2944490
  have hstable : (prefixWord ++ tailWord_2944490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944490).length < 2 ^ (prefixWord ++ tailWord_2944490).sum := by decide
  have hdescent : baseEnd_2944490 < baseStart_2944490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944497 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_2944497 : Nat := 118140960795 + 2944497 * 2 ^ 59
def prefixEnd_2944497 : Nat := 4983230072969 + 3 ^ 40 * 2944497 * 2
def baseEnd_2944497 : Nat := 1511942246721871375646011

theorem tailTrace_2944497 : CollatzResearch.WordTrace tailWord_2944497 prefixEnd_2944497 1511942246721871375646011 := by
  unfold tailWord_2944497
  simp only [CollatzResearch.WordTrace]
  refine ⟨107394628413597723896383745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71596418942398482597589163 107394628413597723896383745)
  ·
    refine ⟨80545971310198292922287809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107394628413597723896383745 80545971310198292922287809)
    ·
      refine ⟨60409478482648719691715857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80545971310198292922287809 60409478482648719691715857)
      ·
        refine ⟨45307108861986539768786893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60409478482648719691715857 45307108861986539768786893)
        ·
          refine ⟨16990165823244952413295085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45307108861986539768786893 16990165823244952413295085)
          ·
            refine ⟨6371312183716857154985657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16990165823244952413295085 6371312183716857154985657)
            ·
              refine ⟨4778484137787642866239243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6371312183716857154985657 4778484137787642866239243)
              ·
                refine ⟨7167726206681464299358865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4778484137787642866239243 7167726206681464299358865)
                ·
                  refine ⟨5375794655011098224519149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7167726206681464299358865 5375794655011098224519149)
                  ·
                    refine ⟨2015922995629161834194681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5375794655011098224519149 2015922995629161834194681)
                    ·
                      refine ⟨1511942246721871375646011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015922995629161834194681 1511942246721871375646011)
                      ·
                        rfl

theorem cell23_2944497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_2944497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944497 prefixEnd_2944497 := by exact prefixLift 2944497
  have htrace : WordTrace (prefixWord ++ tailWord_2944497) baseStart_2944497 baseEnd_2944497 := by
    simpa [prefixWord, tailWord_2944497, baseEnd_2944497] using wordTrace_append hprefix tailTrace_2944497
  have hstable : (prefixWord ++ tailWord_2944497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944497).length < 2 ^ (prefixWord ++ tailWord_2944497).sum := by decide
  have hdescent : baseEnd_2944497 < baseStart_2944497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 4, 4]
def baseStart_2944503 : Nat := 118140960795 + 2944503 * 2 ^ 59
def prefixEnd_2944503 : Nat := 4983230072969 + 3 ^ 40 * 2944503 * 2
def baseEnd_2944503 : Nat := 503981775868599450723661

theorem tailTrace_2944503 : CollatzResearch.WordTrace tailWord_2944503 prefixEnd_2944503 503981775868599450723661 := by
  unfold tailWord_2944503
  simp only [CollatzResearch.WordTrace]
  refine ⟨107394847251575986921102163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71596564834383991280734775 107394847251575986921102163)
  ·
    refine ⟨161092270877363980381653245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107394847251575986921102163 161092270877363980381653245)
    ·
      refine ⟨60409601579011492643119967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161092270877363980381653245 60409601579011492643119967)
      ·
        refine ⟨90614402368517238964679951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60409601579011492643119967 90614402368517238964679951)
        ·
          refine ⟨135921603552775858447019927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90614402368517238964679951 135921603552775858447019927)
          ·
            refine ⟨203882405329163787670529891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135921603552775858447019927 203882405329163787670529891)
            ·
              refine ⟨305823607993745681505794837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203882405329163787670529891 305823607993745681505794837)
              ·
                refine ⟨14335481624706828820584133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305823607993745681505794837 14335481624706828820584133)
                ·
                  refine ⟨2687902804632530403859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14335481624706828820584133 2687902804632530403859525)
                  ·
                    refine ⟨503981775868599450723661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2687902804632530403859525 503981775868599450723661)
                    ·
                      rfl

theorem cell23_2944503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_2944503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944503 prefixEnd_2944503 := by exact prefixLift 2944503
  have htrace : WordTrace (prefixWord ++ tailWord_2944503) baseStart_2944503 baseEnd_2944503 := by
    simpa [prefixWord, tailWord_2944503, baseEnd_2944503] using wordTrace_append hprefix tailTrace_2944503
  have hstable : (prefixWord ++ tailWord_2944503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944503).length < 2 ^ (prefixWord ++ tailWord_2944503).sum := by decide
  have hdescent : baseEnd_2944503 < baseStart_2944503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944514 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2944514 : Nat := 118140960795 + 2944514 * 2 ^ 59
def prefixEnd_2944514 : Nat := 4983230072969 + 3 ^ 40 * 2944514 * 2
def baseEnd_2944514 : Nat := 1511950975892997809133433

theorem tailTrace_2944514 : CollatzResearch.WordTrace tailWord_2944514 prefixEnd_2944514 1511950975892997809133433 := by
  unfold tailWord_2944514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26848812113634033949938149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71596832303024090533168397 26848812113634033949938149)
  ·
    refine ⟨5034152271306381365613403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26848812113634033949938149 5034152271306381365613403)
    ·
      refine ⟨7551228406959572048420105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5034152271306381365613403 7551228406959572048420105)
      ·
        refine ⟨5663421305219679036315079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7551228406959572048420105 5663421305219679036315079)
        ·
          refine ⟨8495131957829518554472619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663421305219679036315079 8495131957829518554472619)
          ·
            refine ⟨12742697936744277831708929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495131957829518554472619 12742697936744277831708929)
            ·
              refine ⟨9557023452558208373781697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12742697936744277831708929 9557023452558208373781697)
              ·
                refine ⟨7167767589418656280336273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9557023452558208373781697 7167767589418656280336273)
                ·
                  refine ⟨5375825692063992210252205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7167767589418656280336273 5375825692063992210252205)
                  ·
                    refine ⟨2015934634523997078844577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5375825692063992210252205 2015934634523997078844577)
                    ·
                      refine ⟨1511950975892997809133433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015934634523997078844577 1511950975892997809133433)
                      ·
                        rfl

theorem cell23_2944514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2944514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944514 prefixEnd_2944514 := by exact prefixLift 2944514
  have htrace : WordTrace (prefixWord ++ tailWord_2944514) baseStart_2944514 baseEnd_2944514 := by
    simpa [prefixWord, tailWord_2944514, baseEnd_2944514] using wordTrace_append hprefix tailTrace_2944514
  have hstable : (prefixWord ++ tailWord_2944514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944514).length < 2 ^ (prefixWord ++ tailWord_2944514).sum := by decide
  have hdescent : baseEnd_2944514 < baseStart_2944514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944520 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_2944520 : Nat := 118140960795 + 2944520 * 2 ^ 59
def prefixEnd_2944520 : Nat := 4983230072969 + 3 ^ 40 * 2944520 * 2
def baseEnd_2944520 : Nat := 503984685592308261886135

theorem tailTrace_2944520 : CollatzResearch.WordTrace tailWord_2944520 prefixEnd_2944520 503984685592308261886135 := by
  unfold tailWord_2944520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53697733646257199412235507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71596978195009599216314009 53697733646257199412235507)
  ·
    refine ⟨80546600469385799118353261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53697733646257199412235507 80546600469385799118353261)
    ·
      refine ⟨30204975176019674669382473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80546600469385799118353261 30204975176019674669382473)
      ·
        refine ⟨22653731382014756002036855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30204975176019674669382473 22653731382014756002036855)
        ·
          refine ⟨33980597073022134003055283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22653731382014756002036855 33980597073022134003055283)
          ·
            refine ⟨50970895609533201004582925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33980597073022134003055283 50970895609533201004582925)
            ·
              refine ⟨19114085853574950376718597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50970895609533201004582925 19114085853574950376718597)
              ·
                refine ⟨3583891097545303195634737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19114085853574950376718597 3583891097545303195634737)
                ·
                  refine ⟨2687918323158977396726053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583891097545303195634737 2687918323158977396726053)
                  ·
                    refine ⟨503984685592308261886135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2687918323158977396726053 503984685592308261886135)
                    ·
                      rfl

theorem cell23_2944520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_2944520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944520 prefixEnd_2944520 := by exact prefixLift 2944520
  have htrace : WordTrace (prefixWord ++ tailWord_2944520) baseStart_2944520 baseEnd_2944520 := by
    simpa [prefixWord, tailWord_2944520, baseEnd_2944520] using wordTrace_append hprefix tailTrace_2944520
  have hstable : (prefixWord ++ tailWord_2944520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944520).length < 2 ^ (prefixWord ++ tailWord_2944520).sum := by decide
  have hdescent : baseEnd_2944520 < baseStart_2944520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944533 : List Nat := [1, 3, 2, 1, 3, 2, 3, 8]
def baseStart_2944533 : Nat := 118140960795 + 2944533 * 2 ^ 59
def prefixEnd_2944533 : Nat := 4983230072969 + 3 ^ 40 * 2944533 * 2
def baseEnd_2944533 : Nat := 55998545630571601288735

theorem tailTrace_2944533 : CollatzResearch.WordTrace tailWord_2944533 prefixEnd_2944533 55998545630571601288735 := by
  unfold tailWord_2944533
  simp only [CollatzResearch.WordTrace]
  refine ⟨107395941441467302044694253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71597294294311534696462835 107395941441467302044694253)
  ·
    refine ⟨40273478040550238266760345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107395941441467302044694253 40273478040550238266760345)
    ·
      refine ⟨30205108530412678700070259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40273478040550238266760345 30205108530412678700070259)
      ·
        refine ⟨45307662795619018050105389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30205108530412678700070259 45307662795619018050105389)
        ·
          refine ⟨16990373548357131768789521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45307662795619018050105389 16990373548357131768789521)
          ·
            refine ⟨12742780161267848826592141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16990373548357131768789521 12742780161267848826592141)
            ·
              refine ⟨4778542560475443309972053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12742780161267848826592141 4778542560475443309972053)
              ·
                refine ⟨55998545630571601288735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4778542560475443309972053 55998545630571601288735)
                ·
                  rfl

theorem cell23_2944533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 8].length) (baseStart_2944533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944533 prefixEnd_2944533 := by exact prefixLift 2944533
  have htrace : WordTrace (prefixWord ++ tailWord_2944533) baseStart_2944533 baseEnd_2944533 := by
    simpa [prefixWord, tailWord_2944533, baseEnd_2944533] using wordTrace_append hprefix tailTrace_2944533
  have hstable : (prefixWord ++ tailWord_2944533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944533).length < 2 ^ (prefixWord ++ tailWord_2944533).sum := by decide
  have hdescent : baseEnd_2944533 < baseStart_2944533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944540 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2944540 : Nat := 118140960795 + 2944540 * 2 ^ 59
def prefixEnd_2944540 : Nat := 4983230072969 + 3 ^ 40 * 2944540 * 2
def baseEnd_2944540 : Nat := 1511964326390014707408313

theorem tailTrace_2944540 : CollatzResearch.WordTrace tailWord_2944540 prefixEnd_2944540 1511964326390014707408313 := by
  unfold tailWord_2944540
  simp only [CollatzResearch.WordTrace]
  refine ⟨53698098376220971120099537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71597464501627961493466049 53698098376220971120099537)
  ·
    refine ⟨40273573782165728340074653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53698098376220971120099537 40273573782165728340074653)
    ·
      refine ⟨15102590168312148127527995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40273573782165728340074653 15102590168312148127527995)
      ·
        refine ⟨22653885252468222191291993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15102590168312148127527995 22653885252468222191291993)
        ·
          refine ⟨16990413939351166643468995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22653885252468222191291993 16990413939351166643468995)
          ·
            refine ⟨25485620909026749965203493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16990413939351166643468995 25485620909026749965203493)
            ·
              refine ⟨4778553920442515618475655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25485620909026749965203493 4778553920442515618475655)
              ·
                refine ⟨7167830880663773427713483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4778553920442515618475655 7167830880663773427713483)
                ·
                  refine ⟨10751746320995660141570225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7167830880663773427713483 10751746320995660141570225)
                  ·
                    refine ⟨8063809740746745106177669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10751746320995660141570225 8063809740746745106177669)
                    ·
                      refine ⟨1511964326390014707408313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8063809740746745106177669 1511964326390014707408313)
                      ·
                        rfl

theorem cell23_2944540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2944540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944540 prefixEnd_2944540 := by exact prefixLift 2944540
  have htrace : WordTrace (prefixWord ++ tailWord_2944540) baseStart_2944540 baseEnd_2944540 := by
    simpa [prefixWord, tailWord_2944540, baseEnd_2944540] using wordTrace_append hprefix tailTrace_2944540
  have hstable : (prefixWord ++ tailWord_2944540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944540).length < 2 ^ (prefixWord ++ tailWord_2944540).sum := by decide
  have hdescent : baseEnd_2944540 < baseStart_2944540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944544 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2944544 : Nat := 118140960795 + 2944544 * 2 ^ 59
def prefixEnd_2944544 : Nat := 4983230072969 + 3 ^ 40 * 2944544 * 2
def baseEnd_2944544 : Nat := 1511966380312632691758295

theorem tailTrace_2944544 : CollatzResearch.WordTrace tailWord_2944544 prefixEnd_2944544 1511966380312632691758295 := by
  unfold tailWord_2944544
  simp only [CollatzResearch.WordTrace]
  refine ⟨53698171322213725461672343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71597561762951633948896457 53698171322213725461672343)
  ·
    refine ⟨80547256983320588192508515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53698171322213725461672343 80547256983320588192508515)
    ·
      refine ⟨120820885474980882288762773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80547256983320588192508515 120820885474980882288762773)
      ·
        refine ⟨5663479006639728857285755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120820885474980882288762773 5663479006639728857285755)
        ·
          refine ⟨8495218509959593285928633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663479006639728857285755 8495218509959593285928633)
          ·
            refine ⟨6371413882469694964446475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8495218509959593285928633 6371413882469694964446475)
            ·
              refine ⟨9557120823704542446669713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6371413882469694964446475 9557120823704542446669713)
              ·
                refine ⟨7167840617778406835002285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9557120823704542446669713 7167840617778406835002285)
                ·
                  refine ⟨2687940231666902563125857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7167840617778406835002285 2687940231666902563125857)
                  ·
                    refine ⟨2015955173750176922344393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687940231666902563125857 2015955173750176922344393)
                    ·
                      refine ⟨1511966380312632691758295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015955173750176922344393 1511966380312632691758295)
                      ·
                        rfl

theorem cell23_2944544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2944544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944544 prefixEnd_2944544 := by exact prefixLift 2944544
  have htrace : WordTrace (prefixWord ++ tailWord_2944544) baseStart_2944544 baseEnd_2944544 := by
    simpa [prefixWord, tailWord_2944544, baseEnd_2944544] using wordTrace_append hprefix tailTrace_2944544
  have hstable : (prefixWord ++ tailWord_2944544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944544).length < 2 ^ (prefixWord ++ tailWord_2944544).sum := by decide
  have hdescent : baseEnd_2944544 < baseStart_2944544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944560 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3]
def baseStart_2944560 : Nat := 118140960795 + 2944560 * 2 ^ 59
def prefixEnd_2944560 : Nat := 4983230072969 + 3 ^ 40 * 2944560 * 2
def baseEnd_2944560 : Nat := 1511974596003104629158221

theorem tailTrace_2944560 : CollatzResearch.WordTrace tailWord_2944560 prefixEnd_2944560 1511974596003104629158221 := by
  unfold tailWord_2944560
  simp only [CollatzResearch.WordTrace]
  refine ⟨53698463106184742827963567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71597950808246323770618089 53698463106184742827963567)
  ·
    refine ⟨80547694659277114241945351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53698463106184742827963567 80547694659277114241945351)
    ·
      refine ⟨120821541988915671362918027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80547694659277114241945351 120821541988915671362918027)
      ·
        refine ⟨181232312983373507044377041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120821541988915671362918027 181232312983373507044377041)
        ·
          refine ⟨135924234737530130283282781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181232312983373507044377041 135924234737530130283282781)
          ·
            refine ⟨50971588026573798856231043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135924234737530130283282781 50971588026573798856231043)
            ·
              refine ⟨76457382039860698284346565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50971588026573798856231043 76457382039860698284346565)
              ·
                refine ⟨14335759132473880928314981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76457382039860698284346565 14335759132473880928314981)
                ·
                  refine ⟨2687954837338852674059059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14335759132473880928314981 2687954837338852674059059)
                  ·
                    refine ⟨4031932256008279011088589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2687954837338852674059059 4031932256008279011088589)
                    ·
                      refine ⟨1511974596003104629158221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4031932256008279011088589 1511974596003104629158221)
                      ·
                        rfl

theorem cell23_2944560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_2944560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944560 prefixEnd_2944560 := by exact prefixLift 2944560
  have htrace : WordTrace (prefixWord ++ tailWord_2944560) baseStart_2944560 baseEnd_2944560 := by
    simpa [prefixWord, tailWord_2944560, baseEnd_2944560] using wordTrace_append hprefix tailTrace_2944560
  have hstable : (prefixWord ++ tailWord_2944560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944560).length < 2 ^ (prefixWord ++ tailWord_2944560).sum := by decide
  have hdescent : baseEnd_2944560 < baseStart_2944560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944577 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2944577 : Nat := 118140960795 + 2944577 * 2 ^ 59
def prefixEnd_2944577 : Nat := 4983230072969 + 3 ^ 40 * 2944577 * 2
def baseEnd_2944577 : Nat := 1511983325174231062645643

theorem tailTrace_2944577 : CollatzResearch.WordTrace tailWord_2944577 prefixEnd_2944577 1511983325174231062645643 := by
  unfold tailWord_2944577
  simp only [CollatzResearch.WordTrace]
  refine ⟨107397546253307897559295985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71598364168871931706197323 107397546253307897559295985)
  ·
    refine ⟨80548159689980923169471989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107397546253307897559295985 80548159689980923169471989)
    ·
      refine ⟨7551389970935711547137999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80548159689980923169471989 7551389970935711547137999)
      ·
        refine ⟨11327084956403567320706999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551389970935711547137999 11327084956403567320706999)
        ·
          refine ⟨16990627434605350981060499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11327084956403567320706999 16990627434605350981060499)
          ·
            refine ⟨25485941151908026471590749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16990627434605350981060499 25485941151908026471590749)
            ·
              refine ⟨9557227931965509926846531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25485941151908026471590749 9557227931965509926846531)
              ·
                refine ⟨14335841897948264890269797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9557227931965509926846531 14335841897948264890269797)
                ·
                  refine ⟨2687970355865299666925587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14335841897948264890269797 2687970355865299666925587)
                  ·
                    refine ⟨4031955533797949500388381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2687970355865299666925587 4031955533797949500388381)
                    ·
                      refine ⟨1511983325174231062645643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4031955533797949500388381 1511983325174231062645643)
                      ·
                        rfl

theorem cell23_2944577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2944577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944577 prefixEnd_2944577 := by exact prefixLift 2944577
  have htrace : WordTrace (prefixWord ++ tailWord_2944577) baseStart_2944577 baseEnd_2944577 := by
    simpa [prefixWord, tailWord_2944577, baseEnd_2944577] using wordTrace_append hprefix tailTrace_2944577
  have hstable : (prefixWord ++ tailWord_2944577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944577).length < 2 ^ (prefixWord ++ tailWord_2944577).sum := by decide
  have hdescent : baseEnd_2944577 < baseStart_2944577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944593 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_2944593 : Nat := 118140960795 + 2944593 * 2 ^ 59
def prefixEnd_2944593 : Nat := 4983230072969 + 3 ^ 40 * 2944593 * 2
def baseEnd_2944593 : Nat := 503997180288234333348523

theorem tailTrace_2944593 : CollatzResearch.WordTrace tailWord_2944593 prefixEnd_2944593 503997180288234333348523 := by
  unfold tailWord_2944593
  simp only [CollatzResearch.WordTrace]
  refine ⟨107398129821249932291878433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71598753214166621527918955 107398129821249932291878433)
  ·
    refine ⟨80548597365937449218908825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107398129821249932291878433 80548597365937449218908825)
    ·
      refine ⟨60411448024453086914181619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80548597365937449218908825 60411448024453086914181619)
      ·
        refine ⟨90617172036679630371272429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60411448024453086914181619 90617172036679630371272429)
        ·
          refine ⟨33981439513754861389227161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90617172036679630371272429 33981439513754861389227161)
          ·
            refine ⟨25486079635316146041920371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33981439513754861389227161 25486079635316146041920371)
            ·
              refine ⟨38229119452974219062880557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25486079635316146041920371 38229119452974219062880557)
              ·
                refine ⟨14335919794865332148580209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38229119452974219062880557 14335919794865332148580209)
                ·
                  refine ⟨10751939846148999111435157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14335919794865332148580209 10751939846148999111435157)
                  ·
                    refine ⟨503997180288234333348523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10751939846148999111435157 503997180288234333348523)
                    ·
                      rfl

theorem cell23_2944593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_2944593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944593 prefixEnd_2944593 := by exact prefixLift 2944593
  have htrace : WordTrace (prefixWord ++ tailWord_2944593) baseStart_2944593 baseEnd_2944593 := by
    simpa [prefixWord, tailWord_2944593, baseEnd_2944593] using wordTrace_append hprefix tailTrace_2944593
  have hstable : (prefixWord ++ tailWord_2944593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944593).length < 2 ^ (prefixWord ++ tailWord_2944593).sum := by decide
  have hdescent : baseEnd_2944593 < baseStart_2944593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944598 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2944598 : Nat := 118140960795 + 2944598 * 2 ^ 59
def prefixEnd_2944598 : Nat := 4983230072969 + 3 ^ 40 * 2944598 * 2
def baseEnd_2944598 : Nat := 1511994108267975480483047

theorem tailTrace_2944598 : CollatzResearch.WordTrace tailWord_2944598 prefixEnd_2944598 1511994108267975480483047 := by
  unfold tailWord_2944598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712394511639488634113153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71598874790821212097206965 6712394511639488634113153)
  ·
    refine ⟨5034295883729616475584865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6712394511639488634113153 5034295883729616475584865)
    ·
      refine ⟨3775721912797212356688649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5034295883729616475584865 3775721912797212356688649)
      ·
        refine ⟨2831791434597909267516487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3775721912797212356688649 2831791434597909267516487)
        ·
          refine ⟨4247687151896863901274731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831791434597909267516487 4247687151896863901274731)
          ·
            refine ⟨6371530727845295851912097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247687151896863901274731 6371530727845295851912097)
            ·
              refine ⟨4778648045883971888934073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6371530727845295851912097 4778648045883971888934073)
              ·
                refine ⟨3583986034412978916700555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778648045883971888934073 3583986034412978916700555)
                ·
                  refine ⟨5375979051619468375050833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583986034412978916700555 5375979051619468375050833)
                  ·
                    refine ⟨4031984288714601281288125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5375979051619468375050833 4031984288714601281288125)
                    ·
                      refine ⟨1511994108267975480483047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4031984288714601281288125 1511994108267975480483047)
                      ·
                        rfl

theorem cell23_2944598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2944598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944598 prefixEnd_2944598 := by exact prefixLift 2944598
  have htrace : WordTrace (prefixWord ++ tailWord_2944598) baseStart_2944598 baseEnd_2944598 := by
    simpa [prefixWord, tailWord_2944598, baseEnd_2944598] using wordTrace_append hprefix tailTrace_2944598
  have hstable : (prefixWord ++ tailWord_2944598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944598).length < 2 ^ (prefixWord ++ tailWord_2944598).sum := by decide
  have hdescent : baseEnd_2944598 < baseStart_2944598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944604 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2944604 : Nat := 118140960795 + 2944604 * 2 ^ 59
def prefixEnd_2944604 : Nat := 4983230072969 + 3 ^ 40 * 2944604 * 2
def baseEnd_2944604 : Nat := 1511997189151902457008019

theorem tailTrace_2944604 : CollatzResearch.WordTrace tailWord_2944604 prefixEnd_2944604 1511997189151902457008019 := by
  unfold tailWord_2944604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53699265512105040585264433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71599020682806720780352577 53699265512105040585264433)
  ·
    refine ⟨40274449134078780438948325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53699265512105040585264433 40274449134078780438948325)
    ·
      refine ⟨7551459212639771332302811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40274449134078780438948325 7551459212639771332302811)
      ·
        refine ⟨11327188818959656998454217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551459212639771332302811 11327188818959656998454217)
        ·
          refine ⟨8495391614219742748840663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11327188818959656998454217 8495391614219742748840663)
          ·
            refine ⟨12743087421329614123260995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495391614219742748840663 12743087421329614123260995)
            ·
              refine ⟨19114631131994421184891493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12743087421329614123260995 19114631131994421184891493)
              ·
                refine ⟨3583993337248953972167155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19114631131994421184891493 3583993337248953972167155)
                ·
                  refine ⟨5375990005873430958250733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583993337248953972167155 5375990005873430958250733)
                  ·
                    refine ⟨2015996252202536609344025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5375990005873430958250733 2015996252202536609344025)
                    ·
                      refine ⟨1511997189151902457008019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2015996252202536609344025 1511997189151902457008019)
                      ·
                        rfl

theorem cell23_2944604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2944604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944604 prefixEnd_2944604 := by exact prefixLift 2944604
  have htrace : WordTrace (prefixWord ++ tailWord_2944604) baseStart_2944604 baseEnd_2944604 := by
    simpa [prefixWord, tailWord_2944604, baseEnd_2944604] using wordTrace_append hprefix tailTrace_2944604
  have hstable : (prefixWord ++ tailWord_2944604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944604).length < 2 ^ (prefixWord ++ tailWord_2944604).sum := by decide
  have hdescent : baseEnd_2944604 < baseStart_2944604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944617 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 4, 2, 2]
def baseStart_2944617 : Nat := 118140960795 + 2944617 * 2 ^ 59
def prefixEnd_2944617 : Nat := 4983230072969 + 3 ^ 40 * 2944617 * 2
def baseEnd_2944617 : Nat := 1512003864400410906145459

theorem tailTrace_2944617 : CollatzResearch.WordTrace tailWord_2944617 prefixEnd_2944617 1512003864400410906145459 := by
  unfold tailWord_2944617
  simp only [CollatzResearch.WordTrace]
  refine ⟨107399005173162984390752105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71599336782108656260501403 107399005173162984390752105)
  ·
    refine ⟨80549253879872238293064079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107399005173162984390752105 80549253879872238293064079)
    ·
      refine ⟨120823880819808357439596119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80549253879872238293064079 120823880819808357439596119)
      ·
        refine ⟨181235821229712536159394179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120823880819808357439596119 181235821229712536159394179)
        ·
          refine ⟨271853731844568804239091269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181235821229712536159394179 271853731844568804239091269)
          ·
            refine ⟨50972574720856650794829613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271853731844568804239091269 50972574720856650794829613)
            ·
              refine ⟨19114715520321244048061105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50972574720856650794829613 19114715520321244048061105)
              ·
                refine ⟨14336036640240933036045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19114715520321244048061105 14336036640240933036045829)
                ·
                  refine ⟨2688006870045174944258593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14336036640240933036045829 2688006870045174944258593)
                  ·
                    refine ⟨2016005152533881208193945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2688006870045174944258593 2016005152533881208193945)
                    ·
                      refine ⟨1512003864400410906145459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016005152533881208193945 1512003864400410906145459)
                      ·
                        rfl

theorem cell23_2944617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2, 2].length) (baseStart_2944617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944617 prefixEnd_2944617 := by exact prefixLift 2944617
  have htrace : WordTrace (prefixWord ++ tailWord_2944617) baseStart_2944617 baseEnd_2944617 := by
    simpa [prefixWord, tailWord_2944617, baseEnd_2944617] using wordTrace_append hprefix tailTrace_2944617
  have hstable : (prefixWord ++ tailWord_2944617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944617).length < 2 ^ (prefixWord ++ tailWord_2944617).sum := by decide
  have hdescent : baseEnd_2944617 < baseStart_2944617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944633 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2944633 : Nat := 118140960795 + 2944633 * 2 ^ 59
def prefixEnd_2944633 : Nat := 4983230072969 + 3 ^ 40 * 2944633 * 2
def baseEnd_2944633 : Nat := 1512012080090882843545385

theorem tailTrace_2944633 : CollatzResearch.WordTrace tailWord_2944633 prefixEnd_2944633 1512012080090882843545385 := by
  unfold tailWord_2944633
  simp only [CollatzResearch.WordTrace]
  refine ⟨107399588741105019123334553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71599725827403346082223035 107399588741105019123334553)
  ·
    refine ⟨80549691555828764342500915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107399588741105019123334553 80549691555828764342500915)
    ·
      refine ⟨120824537333743146513751373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80549691555828764342500915 120824537333743146513751373)
      ·
        refine ⟨45309201500153679942656765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120824537333743146513751373 45309201500153679942656765)
        ·
          refine ⟨16990950562557629978496287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45309201500153679942656765 16990950562557629978496287)
          ·
            refine ⟨25486425843836444967744431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16990950562557629978496287 25486425843836444967744431)
            ·
              refine ⟨38229638765754667451616647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25486425843836444967744431 38229638765754667451616647)
              ·
                refine ⟨57344458148632001177424971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38229638765754667451616647 57344458148632001177424971)
                ·
                  refine ⟨86016687222948001766137457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57344458148632001177424971 86016687222948001766137457)
                  ·
                    refine ⟨64512515417211001324603093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86016687222948001766137457 64512515417211001324603093)
                    ·
                      refine ⟨1512012080090882843545385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64512515417211001324603093 1512012080090882843545385)
                      ·
                        rfl

theorem cell23_2944633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2944633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944633 prefixEnd_2944633 := by exact prefixLift 2944633
  have htrace : WordTrace (prefixWord ++ tailWord_2944633) baseStart_2944633 baseEnd_2944633 := by
    simpa [prefixWord, tailWord_2944633, baseEnd_2944633] using wordTrace_append hprefix tailTrace_2944633
  have hstable : (prefixWord ++ tailWord_2944633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944633).length < 2 ^ (prefixWord ++ tailWord_2944633).sum := by decide
  have hdescent : baseEnd_2944633 < baseStart_2944633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944724 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2944724 : Nat := 118140960795 + 2944724 * 2 ^ 59
def prefixEnd_2944724 : Nat := 4983230072969 + 3 ^ 40 * 2944724 * 2
def baseEnd_2944724 : Nat := 1512058806830441987507467

theorem tailTrace_2944724 : CollatzResearch.WordTrace tailWord_2944724 prefixEnd_2944724 1512058806830441987507467 := by
  unfold tailWord_2944724
  simp only [CollatzResearch.WordTrace]
  refine ⟨53701453891887670832448613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71601938522516894443264817 53701453891887670832448613)
  ·
    refine ⟨10069022604728938281084115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53701453891887670832448613 10069022604728938281084115)
    ·
      refine ⟨15103533907093407421626173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10069022604728938281084115 15103533907093407421626173)
      ·
        refine ⟨5663825215160027783109815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15103533907093407421626173 5663825215160027783109815)
        ·
          refine ⟨8495737822740041674664723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663825215160027783109815 8495737822740041674664723)
          ·
            refine ⟨12743606734110062511997085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495737822740041674664723 12743606734110062511997085)
            ·
              refine ⟨4778852525291273441998907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12743606734110062511997085 4778852525291273441998907)
              ·
                refine ⟨7168278787936910162998361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4778852525291273441998907 7168278787936910162998361)
                ·
                  refine ⟨5376209090952682622248771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168278787936910162998361 5376209090952682622248771)
                  ·
                    refine ⟨8064313636429023933373157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376209090952682622248771 8064313636429023933373157)
                    ·
                      refine ⟨1512058806830441987507467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8064313636429023933373157 1512058806830441987507467)
                      ·
                        rfl

theorem cell23_2944724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2944724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944724 prefixEnd_2944724 := by exact prefixLift 2944724
  have htrace : WordTrace (prefixWord ++ tailWord_2944724) baseStart_2944724 baseEnd_2944724 := by
    simpa [prefixWord, tailWord_2944724, baseEnd_2944724] using wordTrace_append hprefix tailTrace_2944724
  have hstable : (prefixWord ++ tailWord_2944724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944724).length < 2 ^ (prefixWord ++ tailWord_2944724).sum := by decide
  have hdescent : baseEnd_2944724 < baseStart_2944724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944750 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2944750 : Nat := 118140960795 + 2944750 * 2 ^ 59
def prefixEnd_2944750 : Nat := 4983230072969 + 3 ^ 40 * 2944750 * 2
def baseEnd_2944750 : Nat := 1512072157327458885782347

theorem tailTrace_2944750 : CollatzResearch.WordTrace tailWord_2944750 prefixEnd_2944750 1512072157327458885782347 := by
  unfold tailWord_2944750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425482010210143513167963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71602570721120765403562469 13425482010210143513167963)
  ·
    refine ⟨20138223015315215269751945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13425482010210143513167963 20138223015315215269751945)
    ·
      refine ⟨15103667261486411452313959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20138223015315215269751945 15103667261486411452313959)
      ·
        refine ⟨22655500892229617178470939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15103667261486411452313959 22655500892229617178470939)
        ·
          refine ⟨33983251338344425767706409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22655500892229617178470939 33983251338344425767706409)
          ·
            refine ⟨25487438503758319325779807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33983251338344425767706409 25487438503758319325779807)
            ·
              refine ⟨38231157755637478988669711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25487438503758319325779807 38231157755637478988669711)
              ·
                refine ⟨57346736633456218483004567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38231157755637478988669711 57346736633456218483004567)
                ·
                  refine ⟨86020104950184327724506851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57346736633456218483004567 86020104950184327724506851)
                  ·
                    refine ⟨129030157425276491586760277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86020104950184327724506851 129030157425276491586760277)
                    ·
                      refine ⟨1512072157327458885782347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129030157425276491586760277 1512072157327458885782347)
                      ·
                        rfl

theorem cell23_2944750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2944750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944750 prefixEnd_2944750 := by exact prefixLift 2944750
  have htrace : WordTrace (prefixWord ++ tailWord_2944750) baseStart_2944750 baseEnd_2944750 := by
    simpa [prefixWord, tailWord_2944750, baseEnd_2944750] using wordTrace_append hprefix tailTrace_2944750
  have hstable : (prefixWord ++ tailWord_2944750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944750).length < 2 ^ (prefixWord ++ tailWord_2944750).sum := by decide
  have hdescent : baseEnd_2944750 < baseStart_2944750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944760 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_2944760 : Nat := 118140960795 + 2944760 * 2 ^ 59
def prefixEnd_2944760 : Nat := 4983230072969 + 3 ^ 40 * 2944760 * 2
def baseEnd_2944760 : Nat := 504025764044667948885767

theorem tailTrace_2944760 : CollatzResearch.WordTrace tailWord_2944760 prefixEnd_2944760 504025764044667948885767 := by
  unfold tailWord_2944760
  simp only [CollatzResearch.WordTrace]
  refine ⟨53702110405822459906603867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71602813874429946542138489 53702110405822459906603867)
  ·
    refine ⟨80553165608733689859905801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53702110405822459906603867 80553165608733689859905801)
    ·
      refine ⟨60414874206550267394929351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80553165608733689859905801 60414874206550267394929351)
      ·
        refine ⟨90622311309825401092394027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60414874206550267394929351 90622311309825401092394027)
        ·
          refine ⟨135933466964738101638591041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90622311309825401092394027 135933466964738101638591041)
          ·
            refine ⟨101950100223553576228943281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135933466964738101638591041 101950100223553576228943281)
            ·
              refine ⟨76462575167665182171707461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101950100223553576228943281 76462575167665182171707461)
              ·
                refine ⟨14336732843937221657195149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76462575167665182171707461 14336732843937221657195149)
                ·
                  refine ⟨5376274816476458121448181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14336732843937221657195149 5376274816476458121448181)
                  ·
                    refine ⟨504025764044667948885767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5376274816476458121448181 504025764044667948885767)
                    ·
                      rfl

theorem cell23_2944760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_2944760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944760 prefixEnd_2944760 := by exact prefixLift 2944760
  have htrace : WordTrace (prefixWord ++ tailWord_2944760) baseStart_2944760 baseEnd_2944760 := by
    simpa [prefixWord, tailWord_2944760, baseEnd_2944760] using wordTrace_append hprefix tailTrace_2944760
  have hstable : (prefixWord ++ tailWord_2944760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944760).length < 2 ^ (prefixWord ++ tailWord_2944760).sum := by decide
  have hdescent : baseEnd_2944760 < baseStart_2944760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944767 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 5, 2]
def baseStart_2944767 : Nat := 118140960795 + 2944767 * 2 ^ 59
def prefixEnd_2944767 : Nat := 4983230072969 + 3 ^ 40 * 2944767 * 2
def baseEnd_2944767 : Nat := 1512080886498585319269769

theorem tailTrace_2944767 : CollatzResearch.WordTrace tailWord_2944767 prefixEnd_2944767 1512080886498585319269769 := by
  unfold tailWord_2944767
  simp only [CollatzResearch.WordTrace]
  refine ⟨107404476122619560008712555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71602984081746373339141703 107404476122619560008712555)
  ·
    refine ⟨161106714183929340013068833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107404476122619560008712555 161106714183929340013068833)
    ·
      refine ⟨120830035637947005009801625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161106714183929340013068833 120830035637947005009801625)
      ·
        refine ⟨90622526728460253757351219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120830035637947005009801625 90622526728460253757351219)
        ·
          refine ⟨135933790092690380636026829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90622526728460253757351219 135933790092690380636026829)
          ·
            refine ⟨50975171284758892738510061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135933790092690380636026829 50975171284758892738510061)
            ·
              refine ⟨19115689231784584776941273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50975171284758892738510061 19115689231784584776941273)
              ·
                refine ⟨14336766923838438582705955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19115689231784584776941273 14336766923838438582705955)
                ·
                  refine ⟨21505150385757657874058933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14336766923838438582705955 21505150385757657874058933)
                  ·
                    refine ⟨2016107848664780425693025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21505150385757657874058933 2016107848664780425693025)
                    ·
                      refine ⟨1512080886498585319269769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016107848664780425693025 1512080886498585319269769)
                      ·
                        rfl

theorem cell23_2944767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_2944767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944767 prefixEnd_2944767 := by exact prefixLift 2944767
  have htrace : WordTrace (prefixWord ++ tailWord_2944767) baseStart_2944767 baseEnd_2944767 := by
    simpa [prefixWord, tailWord_2944767, baseEnd_2944767] using wordTrace_append hprefix tailTrace_2944767
  have hstable : (prefixWord ++ tailWord_2944767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944767).length < 2 ^ (prefixWord ++ tailWord_2944767).sum := by decide
  have hdescent : baseEnd_2944767 < baseStart_2944767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944817 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2944817 : Nat := 118140960795 + 2944817 * 2 ^ 59
def prefixEnd_2944817 : Nat := 4983230072969 + 3 ^ 40 * 2944817 * 2
def baseEnd_2944817 : Nat := 1512106560531310123644539

theorem tailTrace_2944817 : CollatzResearch.WordTrace tailWord_2944817 prefixEnd_2944817 1512106560531310123644539 := by
  unfold tailWord_2944817
  simp only [CollatzResearch.WordTrace]
  refine ⟨107406299772438418548032705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71604199848292279032021803 107406299772438418548032705)
  ·
    refine ⟨80554724829328813911024529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107406299772438418548032705 80554724829328813911024529)
    ·
      refine ⟨60416043621996610433268397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80554724829328813911024529 60416043621996610433268397)
      ·
        refine ⟨22656016358248728912475649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60416043621996610433268397 22656016358248728912475649)
        ·
          refine ⟨16992012268686546684356737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22656016358248728912475649 16992012268686546684356737)
          ·
            refine ⟨12744009201514910013267553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16992012268686546684356737 12744009201514910013267553)
            ·
              refine ⟨9558006901136182509950665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12744009201514910013267553 9558006901136182509950665)
              ·
                refine ⟨7168505175852136882462999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9558006901136182509950665 7168505175852136882462999)
                ·
                  refine ⟨10752757763778205323694499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168505175852136882462999 10752757763778205323694499)
                  ·
                    refine ⟨16129136645667307985541749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10752757763778205323694499 16129136645667307985541749)
                    ·
                      refine ⟨1512106560531310123644539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16129136645667307985541749 1512106560531310123644539)
                      ·
                        rfl

theorem cell23_2944817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2944817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944817 prefixEnd_2944817 := by exact prefixLift 2944817
  have htrace : WordTrace (prefixWord ++ tailWord_2944817) baseStart_2944817 baseEnd_2944817 := by
    simpa [prefixWord, tailWord_2944817, baseEnd_2944817] using wordTrace_append hprefix tailTrace_2944817
  have hstable : (prefixWord ++ tailWord_2944817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944817).length < 2 ^ (prefixWord ++ tailWord_2944817).sum := by decide
  have hdescent : baseEnd_2944817 < baseStart_2944817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944824 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_2944824 : Nat := 118140960795 + 2944824 * 2 ^ 59
def prefixEnd_2944824 : Nat := 4983230072969 + 3 ^ 40 * 2944824 * 2
def baseEnd_2944824 : Nat := 504036718298630532085669

theorem tailTrace_2944824 : CollatzResearch.WordTrace tailWord_2944824 prefixEnd_2944824 504036718298630532085669 := by
  unfold tailWord_2944824
  simp only [CollatzResearch.WordTrace]
  refine ⟨53703277541706529371768763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71604370055608705829025017 53703277541706529371768763)
  ·
    refine ⟨80554916312559794057653145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53703277541706529371768763 80554916312559794057653145)
    ·
      refine ⟨60416187234419845543239859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80554916312559794057653145 60416187234419845543239859)
      ·
        refine ⟨90624280851629768314859789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60416187234419845543239859 90624280851629768314859789)
        ·
          refine ⟨33984105319361163118072421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90624280851629768314859789 33984105319361163118072421)
          ·
            refine ⟨6372019747380218084638579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33984105319361163118072421 6372019747380218084638579)
            ·
              refine ⟨9558029621070327126957869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6372019747380218084638579 9558029621070327126957869)
              ·
                refine ⟨3584261107901372672609201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9558029621070327126957869 3584261107901372672609201)
                ·
                  refine ⟨2688195830926029504456901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584261107901372672609201 2688195830926029504456901)
                  ·
                    refine ⟨504036718298630532085669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688195830926029504456901 504036718298630532085669)
                    ·
                      rfl

theorem cell23_2944824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_2944824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944824 prefixEnd_2944824 := by exact prefixLift 2944824
  have htrace : WordTrace (prefixWord ++ tailWord_2944824) baseStart_2944824 baseEnd_2944824 := by
    simpa [prefixWord, tailWord_2944824, baseEnd_2944824] using wordTrace_append hprefix tailTrace_2944824
  have hstable : (prefixWord ++ tailWord_2944824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944824).length < 2 ^ (prefixWord ++ tailWord_2944824).sum := by decide
  have hdescent : baseEnd_2944824 < baseStart_2944824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944831 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_2944831 : Nat := 118140960795 + 2944831 * 2 ^ 59
def prefixEnd_2944831 : Nat := 4983230072969 + 3 ^ 40 * 2944831 * 2
def baseEnd_2944831 : Nat := 1512113749260473068869475

theorem tailTrace_2944831 : CollatzResearch.WordTrace tailWord_2944831 prefixEnd_2944831 1512113749260473068869475 := by
  unfold tailWord_2944831
  simp only [CollatzResearch.WordTrace]
  refine ⟨107406810394387698939042347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71604540262925132626028231 107406810394387698939042347)
  ·
    refine ⟨161110215591581548408563521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107406810394387698939042347 161110215591581548408563521)
    ·
      refine ⟨120832661693686161306422641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161110215591581548408563521 120832661693686161306422641)
      ·
        refine ⟨90624496270264620979816981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120832661693686161306422641 90624496270264620979816981)
        ·
          refine ⟨4248023262668654108428921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90624496270264620979816981 4248023262668654108428921)
          ·
            refine ⟨3186017447001490581321691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248023262668654108428921 3186017447001490581321691)
            ·
              refine ⟨4779026170502235871982537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186017447001490581321691 4779026170502235871982537)
              ·
                refine ⟨3584269627876676903986903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4779026170502235871982537 3584269627876676903986903)
                ·
                  refine ⟨5376404441815015355980355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584269627876676903986903 5376404441815015355980355)
                  ·
                    refine ⟨8064606662722523033970533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5376404441815015355980355 8064606662722523033970533)
                    ·
                      refine ⟨1512113749260473068869475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8064606662722523033970533 1512113749260473068869475)
                      ·
                        rfl

theorem cell23_2944831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_2944831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944831 prefixEnd_2944831 := by exact prefixLift 2944831
  have htrace : WordTrace (prefixWord ++ tailWord_2944831) baseStart_2944831 baseEnd_2944831 := by
    simpa [prefixWord, tailWord_2944831, baseEnd_2944831] using wordTrace_append hprefix tailTrace_2944831
  have hstable : (prefixWord ++ tailWord_2944831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944831).length < 2 ^ (prefixWord ++ tailWord_2944831).sum := by decide
  have hdescent : baseEnd_2944831 < baseStart_2944831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944844 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2944844 : Nat := 118140960795 + 2944844 * 2 ^ 59
def prefixEnd_2944844 : Nat := 4983230072969 + 3 ^ 40 * 2944844 * 2
def baseEnd_2944844 : Nat := 1512120424508981518006915

theorem tailTrace_2944844 : CollatzResearch.WordTrace tailWord_2944844 prefixEnd_2944844 1512120424508981518006915 := by
  unfold tailWord_2944844
  simp only [CollatzResearch.WordTrace]
  refine ⟨53703642271670301079632793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71604856362227068106177057 53703642271670301079632793)
  ·
    refine ⟨40277731703752725809724595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53703642271670301079632793 40277731703752725809724595)
    ·
      refine ⟨60416597555629088714586893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40277731703752725809724595 60416597555629088714586893)
      ·
        refine ⟨22656224083360908267970085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60416597555629088714586893 22656224083360908267970085)
        ·
          refine ⟨4248042015630170300244391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22656224083360908267970085 4248042015630170300244391)
          ·
            refine ⟨6372063023445255450366587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248042015630170300244391 6372063023445255450366587)
            ·
              refine ⟨9558094535167883175549881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6372063023445255450366587 9558094535167883175549881)
              ·
                refine ⟨7168570901375912381662411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9558094535167883175549881 7168570901375912381662411)
                ·
                  refine ⟨10752856352063868572493617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7168570901375912381662411 10752856352063868572493617)
                  ·
                    refine ⟨8064642264047901429370213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10752856352063868572493617 8064642264047901429370213)
                    ·
                      refine ⟨1512120424508981518006915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8064642264047901429370213 1512120424508981518006915)
                      ·
                        rfl

theorem cell23_2944844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2944844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944844 prefixEnd_2944844 := by exact prefixLift 2944844
  have htrace : WordTrace (prefixWord ++ tailWord_2944844) baseStart_2944844 baseEnd_2944844 := by
    simpa [prefixWord, tailWord_2944844, baseEnd_2944844] using wordTrace_append hprefix tailTrace_2944844
  have hstable : (prefixWord ++ tailWord_2944844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944844).length < 2 ^ (prefixWord ++ tailWord_2944844).sum := by decide
  have hdescent : baseEnd_2944844 < baseStart_2944844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944914 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2944914 : Nat := 118140960795 + 2944914 * 2 ^ 59
def prefixEnd_2944914 : Nat := 4983230072969 + 3 ^ 40 * 2944914 * 2
def baseEnd_2944914 : Nat := 504052122718265414710531

theorem tailTrace_2944914 : CollatzResearch.WordTrace tailWord_2944914 prefixEnd_2944914 504052122718265414710531 := by
  unfold tailWord_2944914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852459413271751028578449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71606558435391336076209197 26852459413271751028578449)
  ·
    refine ⟨20139344559953813271433837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26852459413271751028578449 20139344559953813271433837)
    ·
      refine ⟨7552254209982679976787689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20139344559953813271433837 7552254209982679976787689)
      ·
        refine ⟨5664190657487009982590767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7552254209982679976787689 5664190657487009982590767)
        ·
          refine ⟨8496285986230514973886151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5664190657487009982590767 8496285986230514973886151)
          ·
            refine ⟨12744428979345772460829227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496285986230514973886151 12744428979345772460829227)
            ·
              refine ⟨19116643469018658691243841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744428979345772460829227 19116643469018658691243841)
              ·
                refine ⟨14337482601763994018432881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19116643469018658691243841 14337482601763994018432881)
                ·
                  refine ⟨10753111951322995513824661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14337482601763994018432881 10753111951322995513824661)
                  ·
                    refine ⟨504052122718265414710531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10753111951322995513824661 504052122718265414710531)
                    ·
                      rfl

theorem cell23_2944914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2944914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944914 prefixEnd_2944914 := by exact prefixLift 2944914
  have htrace : WordTrace (prefixWord ++ tailWord_2944914) baseStart_2944914 baseEnd_2944914 := by
    simpa [prefixWord, tailWord_2944914, baseEnd_2944914] using wordTrace_append hprefix tailTrace_2944914
  have hstable : (prefixWord ++ tailWord_2944914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944914).length < 2 ^ (prefixWord ++ tailWord_2944914).sum := by decide
  have hdescent : baseEnd_2944914 < baseStart_2944914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944917 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2944917 : Nat := 118140960795 + 2944917 * 2 ^ 59
def prefixEnd_2944917 : Nat := 4983230072969 + 3 ^ 40 * 2944917 * 2
def baseEnd_2944917 : Nat := 1512157908596759732394079

theorem tailTrace_2944917 : CollatzResearch.WordTrace tailWord_2944917 prefixEnd_2944917 1512157908596759732394079 := by
  unfold tailWord_2944917
  simp only [CollatzResearch.WordTrace]
  refine ⟨107409947072076135626673005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71606631381384090417782003 107409947072076135626673005)
  ·
    refine ⟨40278730152028550860002377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107409947072076135626673005 40278730152028550860002377)
    ·
      refine ⟨30209047614021413145001783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40278730152028550860002377 30209047614021413145001783)
      ·
        refine ⟨45313571421032119717502675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30209047614021413145001783 45313571421032119717502675)
        ·
          refine ⟨67970357131548179576254013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45313571421032119717502675 67970357131548179576254013)
          ·
            refine ⟨25488883924330567341095255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67970357131548179576254013 25488883924330567341095255)
            ·
              refine ⟨38233325886495851011642883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25488883924330567341095255 38233325886495851011642883)
              ·
                refine ⟨57349988829743776517464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38233325886495851011642883 57349988829743776517464325)
                ·
                  refine ⟨10753122905576958097024561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57349988829743776517464325 10753122905576958097024561)
                  ·
                    refine ⟨8064842179182718572768421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10753122905576958097024561 8064842179182718572768421)
                    ·
                      refine ⟨1512157908596759732394079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8064842179182718572768421 1512157908596759732394079)
                      ·
                        rfl

theorem cell23_2944917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2944917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944917 prefixEnd_2944917 := by exact prefixLift 2944917
  have htrace : WordTrace (prefixWord ++ tailWord_2944917) baseStart_2944917 baseEnd_2944917 := by
    simpa [prefixWord, tailWord_2944917, baseEnd_2944917] using wordTrace_append hprefix tailTrace_2944917
  have hstable : (prefixWord ++ tailWord_2944917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944917).length < 2 ^ (prefixWord ++ tailWord_2944917).sum := by decide
  have hdescent : baseEnd_2944917 < baseStart_2944917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944937 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_2944937 : Nat := 118140960795 + 2944937 * 2 ^ 59
def prefixEnd_2944937 : Nat := 4983230072969 + 3 ^ 40 * 2944937 * 2
def baseEnd_2944937 : Nat := 1512168178209849654143987

theorem tailTrace_2944937 : CollatzResearch.WordTrace tailWord_2944937 prefixEnd_2944937 1512168178209849654143987 := by
  unfold tailWord_2944937
  simp only [CollatzResearch.WordTrace]
  refine ⟨107410676532003679042401065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71607117688002452694934043 107410676532003679042401065)
  ·
    refine ⟨80558007399002759281800799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107410676532003679042401065 80558007399002759281800799)
    ·
      refine ⟨120837011098504138922701199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80558007399002759281800799 120837011098504138922701199)
      ·
        refine ⟨181255516647756208384051799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120837011098504138922701199 181255516647756208384051799)
        ·
          refine ⟨271883274971634312576077699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181255516647756208384051799 271883274971634312576077699)
          ·
            refine ⟨407824912457451468864116549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271883274971634312576077699 407824912457451468864116549)
            ·
              refine ⟨76467171085772150412021853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 407824912457451468864116549 76467171085772150412021853)
              ·
                refine ⟨28675189157164556404508195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76467171085772150412021853 28675189157164556404508195)
                ·
                  refine ⟨43012783735746834606762293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28675189157164556404508195 43012783735746834606762293)
                  ·
                    refine ⟨4032448475226265744383965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43012783735746834606762293 4032448475226265744383965)
                    ·
                      refine ⟨1512168178209849654143987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4032448475226265744383965 1512168178209849654143987)
                      ·
                        rfl

theorem cell23_2944937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_2944937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944937 prefixEnd_2944937 := by exact prefixLift 2944937
  have htrace : WordTrace (prefixWord ++ tailWord_2944937) baseStart_2944937 baseEnd_2944937 := by
    simpa [prefixWord, tailWord_2944937, baseEnd_2944937] using wordTrace_append hprefix tailTrace_2944937
  have hstable : (prefixWord ++ tailWord_2944937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944937).length < 2 ^ (prefixWord ++ tailWord_2944937).sum := by decide
  have hdescent : baseEnd_2944937 < baseStart_2944937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944967 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2944967 : Nat := 118140960795 + 2944967 * 2 ^ 59
def prefixEnd_2944967 : Nat := 4983230072969 + 3 ^ 40 * 2944967 * 2
def baseEnd_2944967 : Nat := 1512183582629484536768849

theorem tailTrace_2944967 : CollatzResearch.WordTrace tailWord_2944967 prefixEnd_2944967 1512183582629484536768849 := by
  unfold tailWord_2944967
  simp only [CollatzResearch.WordTrace]
  refine ⟨107411770721894994165993155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71607847147929996110662103 107411770721894994165993155)
  ·
    refine ⟨161117656082842491248989733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107411770721894994165993155 161117656082842491248989733)
    ·
      refine ⟨30209560515532967109185575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161117656082842491248989733 30209560515532967109185575)
      ·
        refine ⟨45314340773299450663778363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30209560515532967109185575 45314340773299450663778363)
        ·
          refine ⟨67971511159949175995667545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45314340773299450663778363 67971511159949175995667545)
          ·
            refine ⟨50978633369961881996750659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67971511159949175995667545 50978633369961881996750659)
            ·
              refine ⟨76467950054942822995125989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50978633369961881996750659 76467950054942822995125989)
              ·
                refine ⟨14337740635301779311586123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76467950054942822995125989 14337740635301779311586123)
                ·
                  refine ⟨21506610952952668967379185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14337740635301779311586123 21506610952952668967379185)
                  ·
                    refine ⟨16129958214714501725534389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21506610952952668967379185 16129958214714501725534389)
                    ·
                      refine ⟨1512183582629484536768849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16129958214714501725534389 1512183582629484536768849)
                      ·
                        rfl

theorem cell23_2944967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2944967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944967 prefixEnd_2944967 := by exact prefixLift 2944967
  have htrace : WordTrace (prefixWord ++ tailWord_2944967) baseStart_2944967 baseEnd_2944967 := by
    simpa [prefixWord, tailWord_2944967, baseEnd_2944967] using wordTrace_append hprefix tailTrace_2944967
  have hstable : (prefixWord ++ tailWord_2944967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944967).length < 2 ^ (prefixWord ++ tailWord_2944967).sum := by decide
  have hdescent : baseEnd_2944967 < baseStart_2944967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944974 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2944974 : Nat := 118140960795 + 2944974 * 2 ^ 59
def prefixEnd_2944974 : Nat := 4983230072969 + 3 ^ 40 * 2944974 * 2
def baseEnd_2944974 : Nat := 504062392331355336460439

theorem tailTrace_2944974 : CollatzResearch.WordTrace tailWord_2944974 prefixEnd_2944974 504062392331355336460439 := by
  unfold tailWord_2944974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426503254108704295187247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71608017355246422907665317 13426503254108704295187247)
  ·
    refine ⟨20139754881163056442780871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13426503254108704295187247 20139754881163056442780871)
    ·
      refine ⟨30209632321744584664171307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20139754881163056442780871 30209632321744584664171307)
      ·
        refine ⟨45314448482616876996256961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30209632321744584664171307 45314448482616876996256961)
        ·
          refine ⟨33985836361962657747192721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45314448482616876996256961 33985836361962657747192721)
          ·
            refine ⟨25489377271471993310394541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33985836361962657747192721 25489377271471993310394541)
            ·
              refine ⟨9558516476801997491397953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25489377271471993310394541 9558516476801997491397953)
              ·
                refine ⟨7168887357601498118548465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9558516476801997491397953 7168887357601498118548465)
                ·
                  refine ⟨5376665518201123588911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168887357601498118548465 5376665518201123588911349)
                  ·
                    refine ⟨504062392331355336460439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5376665518201123588911349 504062392331355336460439)
                    ·
                      rfl

theorem cell23_2944974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2944974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944974 prefixEnd_2944974 := by exact prefixLift 2944974
  have htrace : WordTrace (prefixWord ++ tailWord_2944974) baseStart_2944974 baseEnd_2944974 := by
    simpa [prefixWord, tailWord_2944974, baseEnd_2944974] using wordTrace_append hprefix tailTrace_2944974
  have hstable : (prefixWord ++ tailWord_2944974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944974).length < 2 ^ (prefixWord ++ tailWord_2944974).sum := by decide
  have hdescent : baseEnd_2944974 < baseStart_2944974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944977 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2944977 : Nat := 118140960795 + 2944977 * 2 ^ 59
def prefixEnd_2944977 : Nat := 4983230072969 + 3 ^ 40 * 2944977 * 2
def baseEnd_2944977 : Nat := 1512188717436029497643803

theorem tailTrace_2944977 : CollatzResearch.WordTrace tailWord_2944977 prefixEnd_2944977 1512188717436029497643803 := by
  unfold tailWord_2944977
  simp only [CollatzResearch.WordTrace]
  refine ⟨107412135451858765873857185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71608090301239177249238123 107412135451858765873857185)
  ·
    refine ⟨80559101588894074405392889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107412135451858765873857185 80559101588894074405392889)
    ·
      refine ⟨60419326191670555804044667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80559101588894074405392889 60419326191670555804044667)
      ·
        refine ⟨90628989287505833706067001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60419326191670555804044667 90628989287505833706067001)
        ·
          refine ⟨67971741965629375279550251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90628989287505833706067001 67971741965629375279550251)
          ·
            refine ⟨101957612948444062919325377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67971741965629375279550251 101957612948444062919325377)
            ·
              refine ⟨76468209711333047189494033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101957612948444062919325377 76468209711333047189494033)
              ·
                refine ⟨57351157283499785392120525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76468209711333047189494033 57351157283499785392120525)
                ·
                  refine ⟨21506683981312419522045197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57351157283499785392120525 21506683981312419522045197)
                  ·
                    refine ⟨8065006492992157320766949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21506683981312419522045197 8065006492992157320766949)
                    ·
                      refine ⟨1512188717436029497643803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8065006492992157320766949 1512188717436029497643803)
                      ·
                        rfl

theorem cell23_2944977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2944977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944977 prefixEnd_2944977 := by exact prefixLift 2944977
  have htrace : WordTrace (prefixWord ++ tailWord_2944977) baseStart_2944977 baseEnd_2944977 := by
    simpa [prefixWord, tailWord_2944977, baseEnd_2944977] using wordTrace_append hprefix tailTrace_2944977
  have hstable : (prefixWord ++ tailWord_2944977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944977).length < 2 ^ (prefixWord ++ tailWord_2944977).sum := by decide
  have hdescent : baseEnd_2944977 < baseStart_2944977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944978 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_2944978 : Nat := 118140960795 + 2944978 * 2 ^ 59
def prefixEnd_2944978 : Nat := 4983230072969 + 3 ^ 40 * 2944978 * 2
def baseEnd_2944978 : Nat := 168021025657409332636811

theorem tailTrace_2944978 : CollatzResearch.WordTrace tailWord_2944978 prefixEnd_2944978 168021025657409332636811 := by
  unfold tailWord_2944978
  simp only [CollatzResearch.WordTrace]
  refine ⟨26853042981213785761160897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71608114616570095363095725 26853042981213785761160897)
  ·
    refine ⟨20139782235910339320870673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26853042981213785761160897 20139782235910339320870673)
    ·
      refine ⟨15104836676932754490653005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20139782235910339320870673 15104836676932754490653005)
      ·
        refine ⟨5664313753849782933994877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15104836676932754490653005 5664313753849782933994877)
        ·
          refine ⟨2124117657693668600248079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5664313753849782933994877 2124117657693668600248079)
          ·
            refine ⟨3186176486540502900372119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124117657693668600248079 3186176486540502900372119)
            ·
              refine ⟨4779264729810754350558179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186176486540502900372119 4779264729810754350558179)
              ·
                refine ⟨7168897094716131525837269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779264729810754350558179 7168897094716131525837269)
                ·
                  refine ⟨168021025657409332636811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7168897094716131525837269 168021025657409332636811)
                  ·
                    rfl

theorem cell23_2944978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_2944978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944978 prefixEnd_2944978 := by exact prefixLift 2944978
  have htrace : WordTrace (prefixWord ++ tailWord_2944978) baseStart_2944978 baseEnd_2944978 := by
    simpa [prefixWord, tailWord_2944978, baseEnd_2944978] using wordTrace_append hprefix tailTrace_2944978
  have hstable : (prefixWord ++ tailWord_2944978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944978).length < 2 ^ (prefixWord ++ tailWord_2944978).sum := by decide
  have hdescent : baseEnd_2944978 < baseStart_2944978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944989 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2944989 : Nat := 118140960795 + 2944989 * 2 ^ 59
def prefixEnd_2944989 : Nat := 4983230072969 + 3 ^ 40 * 2944989 * 2
def baseEnd_2944989 : Nat := 1512194879203883450693749

theorem tailTrace_2944989 : CollatzResearch.WordTrace tailWord_2944989 prefixEnd_2944989 1512194879203883450693749 := by
  unfold tailWord_2944989
  simp only [CollatzResearch.WordTrace]
  refine ⟨107412573127815291923294021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71608382085210194615529347 107412573127815291923294021)
  ·
    refine ⟨20139857461465367235617629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107412573127815291923294021 20139857461465367235617629)
    ·
      refine ⟨7552446548049512713356611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20139857461465367235617629 7552446548049512713356611)
      ·
        refine ⟨11328669822074269070034917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7552446548049512713356611 11328669822074269070034917)
        ·
          refine ⟨2124125591638925450631547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11328669822074269070034917 2124125591638925450631547)
          ·
            refine ⟨3186188387458388175947321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124125591638925450631547 3186188387458388175947321)
            ·
              refine ⟨2389641290593791131960491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186188387458388175947321 2389641290593791131960491)
              ·
                refine ⟨3584461935890686697940737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389641290593791131960491 3584461935890686697940737)
                ·
                  refine ⟨2688346451918015023455553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584461935890686697940737 2688346451918015023455553)
                  ·
                    refine ⟨2016259838938511267591665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2688346451918015023455553 2016259838938511267591665)
                    ·
                      refine ⟨1512194879203883450693749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016259838938511267591665 1512194879203883450693749)
                      ·
                        rfl

theorem cell23_2944989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2944989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2944989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2944989 prefixEnd_2944989 := by exact prefixLift 2944989
  have htrace : WordTrace (prefixWord ++ tailWord_2944989) baseStart_2944989 baseEnd_2944989 := by
    simpa [prefixWord, tailWord_2944989, baseEnd_2944989] using wordTrace_append hprefix tailTrace_2944989
  have hstable : (prefixWord ++ tailWord_2944989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944989).length < 2 ^ (prefixWord ++ tailWord_2944989).sum := by decide
  have hdescent : baseEnd_2944989 < baseStart_2944989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945004 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_2945004 : Nat := 118140960795 + 2945004 * 2 ^ 59
def prefixEnd_2945004 : Nat := 4983230072969 + 3 ^ 40 * 2945004 * 2
def baseEnd_2945004 : Nat := 504067527137900297335393

theorem tailTrace_2945004 : CollatzResearch.WordTrace tailWord_2945004 prefixEnd_2945004 504067527137900297335393 := by
  unfold tailWord_2945004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53706560111380474742545033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71608746815173966323393377 53706560111380474742545033)
  ·
    refine ⟨40279920083535356056908775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53706560111380474742545033 40279920083535356056908775)
    ·
      refine ⟨60419880125303034085363163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40279920083535356056908775 60419880125303034085363163)
      ·
        refine ⟨90629820187954551128044745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60419880125303034085363163 90629820187954551128044745)
        ·
          refine ⟨67972365140965913346033559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90629820187954551128044745 67972365140965913346033559)
          ·
            refine ⟨101958547711448870019050339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67972365140965913346033559 101958547711448870019050339)
            ·
              refine ⟨152937821567173305028575509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101958547711448870019050339 152937821567173305028575509)
              ·
                refine ⟨7168960385961248673214477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152937821567173305028575509 7168960385961248673214477)
                ·
                  refine ⟨2688360144735468252455429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7168960385961248673214477 2688360144735468252455429)
                  ·
                    refine ⟨504067527137900297335393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688360144735468252455429 504067527137900297335393)
                    ·
                      rfl

theorem cell23_2945004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_2945004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945004 prefixEnd_2945004 := by exact prefixLift 2945004
  have htrace : WordTrace (prefixWord ++ tailWord_2945004) baseStart_2945004 baseEnd_2945004 := by
    simpa [prefixWord, tailWord_2945004, baseEnd_2945004] using wordTrace_append hprefix tailTrace_2945004
  have hstable : (prefixWord ++ tailWord_2945004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945004).length < 2 ^ (prefixWord ++ tailWord_2945004).sum := by decide
  have hdescent : baseEnd_2945004 < baseStart_2945004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945031 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2945031 : Nat := 118140960795 + 2945031 * 2 ^ 59
def prefixEnd_2945031 : Nat := 4983230072969 + 3 ^ 40 * 2945031 * 2
def baseEnd_2945031 : Nat := 1512216445391372286368555

theorem tailTrace_2945031 : CollatzResearch.WordTrace tailWord_2945031 prefixEnd_2945031 1512216445391372286368555 := by
  unfold tailWord_2945031
  simp only [CollatzResearch.WordTrace]
  refine ⟨107414104993663133096322947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71609403329108755397548631 107414104993663133096322947)
  ·
    refine ⟨161121157490494699644484421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107414104993663133096322947 161121157490494699644484421)
    ·
      refine ⟨30210217029467756183340829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161121157490494699644484421 30210217029467756183340829)
      ·
        refine ⟨11328831386050408568752811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30210217029467756183340829 11328831386050408568752811)
        ·
          refine ⟨16993247079075612853129217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11328831386050408568752811 16993247079075612853129217)
          ·
            refine ⟨12744935309306709639846913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16993247079075612853129217 12744935309306709639846913)
            ·
              refine ⟨9558701481980032229885185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12744935309306709639846913 9558701481980032229885185)
              ·
                refine ⟨7169026111485024172413889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9558701481980032229885185 7169026111485024172413889)
                ·
                  refine ⟨5376769583613768129310417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169026111485024172413889 5376769583613768129310417)
                  ·
                    refine ⟨4032577187710326096982813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5376769583613768129310417 4032577187710326096982813)
                    ·
                      refine ⟨1512216445391372286368555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4032577187710326096982813 1512216445391372286368555)
                      ·
                        rfl

theorem cell23_2945031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2945031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945031 prefixEnd_2945031 := by exact prefixLift 2945031
  have htrace : WordTrace (prefixWord ++ tailWord_2945031) baseStart_2945031 baseEnd_2945031 := by
    simpa [prefixWord, tailWord_2945031, baseEnd_2945031] using wordTrace_append hprefix tailTrace_2945031
  have hstable : (prefixWord ++ tailWord_2945031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945031).length < 2 ^ (prefixWord ++ tailWord_2945031).sum := by decide
  have hdescent : baseEnd_2945031 < baseStart_2945031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945038 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_2945038 : Nat := 118140960795 + 2945038 * 2 ^ 59
def prefixEnd_2945038 : Nat := 4983230072969 + 3 ^ 40 * 2945038 * 2
def baseEnd_2945038 : Nat := 504073346585317919660341

theorem tailTrace_2945038 : CollatzResearch.WordTrace tailWord_2945038 prefixEnd_2945038 504073346585317919660341 := by
  unfold tailWord_2945038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426795038079721661478471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71609573536425182194551845 13426795038079721661478471)
  ·
    refine ⟨20140192557119582492217707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13426795038079721661478471 20140192557119582492217707)
    ·
      refine ⟨30210288835679373738326561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20140192557119582492217707 30210288835679373738326561)
      ·
        refine ⟨22657716626759530303744921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30210288835679373738326561 22657716626759530303744921)
        ·
          refine ⟨16993287470069647727808691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22657716626759530303744921 16993287470069647727808691)
          ·
            refine ⟨25489931205104471591713037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16993287470069647727808691 25489931205104471591713037)
            ·
              refine ⟨9558724201914176846892389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25489931205104471591713037 9558724201914176846892389)
              ·
                refine ⟨1792260787858908158792323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9558724201914176846892389 1792260787858908158792323)
                ·
                  refine ⟨2688391181788362238188485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792260787858908158792323 2688391181788362238188485)
                  ·
                    refine ⟨504073346585317919660341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688391181788362238188485 504073346585317919660341)
                    ·
                      rfl

theorem cell23_2945038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_2945038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945038 prefixEnd_2945038 := by exact prefixLift 2945038
  have htrace : WordTrace (prefixWord ++ tailWord_2945038) baseStart_2945038 baseEnd_2945038 := by
    simpa [prefixWord, tailWord_2945038, baseEnd_2945038] using wordTrace_append hprefix tailTrace_2945038
  have hstable : (prefixWord ++ tailWord_2945038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945038).length < 2 ^ (prefixWord ++ tailWord_2945038).sum := by decide
  have hdescent : baseEnd_2945038 < baseStart_2945038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945061 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_2945061 : Nat := 118140960795 + 2945061 * 2 ^ 59
def prefixEnd_2945061 : Nat := 4983230072969 + 3 ^ 40 * 2945061 * 2
def baseEnd_2945061 : Nat := 1512231849811007168993417

theorem tailTrace_2945061 : CollatzResearch.WordTrace tailWord_2945061 prefixEnd_2945061 1512231849811007168993417 := by
  unfold tailWord_2945061
  simp only [CollatzResearch.WordTrace]
  refine ⟨107415199183554448219915037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71610132789036298813276691 107415199183554448219915037)
  ·
    refine ⟨40280699693832918082468139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107415199183554448219915037 40280699693832918082468139)
    ·
      refine ⟨60421049540749377123702209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40280699693832918082468139 60421049540749377123702209)
      ·
        refine ⟨45315787155562032842776657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60421049540749377123702209 45315787155562032842776657)
        ·
          refine ⟨33986840366671524632082493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45315787155562032842776657 33986840366671524632082493)
          ·
            refine ⟨12745065137501821737030935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33986840366671524632082493 12745065137501821737030935)
            ·
              refine ⟨19117597706252732605546403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12745065137501821737030935 19117597706252732605546403)
              ·
                refine ⟨28676396559379098908319605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19117597706252732605546403 28676396559379098908319605)
                ·
                  refine ⟨2688412177441790522654963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28676396559379098908319605 2688412177441790522654963)
                  ·
                    refine ⟨4032618266162685783982445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2688412177441790522654963 4032618266162685783982445)
                    ·
                      refine ⟨1512231849811007168993417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4032618266162685783982445 1512231849811007168993417)
                      ·
                        rfl

theorem cell23_2945061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_2945061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945061 prefixEnd_2945061 := by exact prefixLift 2945061
  have htrace : WordTrace (prefixWord ++ tailWord_2945061) baseStart_2945061 baseEnd_2945061 := by
    simpa [prefixWord, tailWord_2945061, baseEnd_2945061] using wordTrace_append hprefix tailTrace_2945061
  have hstable : (prefixWord ++ tailWord_2945061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945061).length < 2 ^ (prefixWord ++ tailWord_2945061).sum := by decide
  have hdescent : baseEnd_2945061 < baseStart_2945061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945071 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 2, 3, 2]
def baseStart_2945071 : Nat := 118140960795 + 2945071 * 2 ^ 59
def prefixEnd_2945071 : Nat := 4983230072969 + 3 ^ 40 * 2945071 * 2
def baseEnd_2945071 : Nat := 1512236984617552129868371

theorem tailTrace_2945071 : CollatzResearch.WordTrace tailWord_2945071 prefixEnd_2945071 1512236984617552129868371 := by
  unfold tailWord_2945071
  simp only [CollatzResearch.WordTrace]
  refine ⟨107415563913518219927779067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71610375942345479951852711 107415563913518219927779067)
  ·
    refine ⟨161123345870277329891668601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107415563913518219927779067 161123345870277329891668601)
    ·
      refine ⟨120842509402707997418751451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161123345870277329891668601 120842509402707997418751451)
      ·
        refine ⟨181263764104061996128127177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120842509402707997418751451 181263764104061996128127177)
        ·
          refine ⟨135947823078046497096095383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181263764104061996128127177 135947823078046497096095383)
          ·
            refine ⟨203921734617069745644143075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135947823078046497096095383 203921734617069745644143075)
            ·
              refine ⟨305882601925604618466214613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203921734617069745644143075 305882601925604618466214613)
              ·
                refine ⟨7169123482631358245301905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 305882601925604618466214613 7169123482631358245301905)
                ·
                  refine ⟨5376842611973518683976429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169123482631358245301905 5376842611973518683976429)
                  ·
                    refine ⟨2016315979490069506491161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5376842611973518683976429 2016315979490069506491161)
                    ·
                      refine ⟨1512236984617552129868371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016315979490069506491161 1512236984617552129868371)
                      ·
                        rfl

theorem cell23_2945071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3, 2].length) (baseStart_2945071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945071 prefixEnd_2945071 := by exact prefixLift 2945071
  have htrace : WordTrace (prefixWord ++ tailWord_2945071) baseStart_2945071 baseEnd_2945071 := by
    simpa [prefixWord, tailWord_2945071, baseEnd_2945071] using wordTrace_append hprefix tailTrace_2945071
  have hstable : (prefixWord ++ tailWord_2945071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945071).length < 2 ^ (prefixWord ++ tailWord_2945071).sum := by decide
  have hdescent : baseEnd_2945071 < baseStart_2945071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945078 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2945078 : Nat := 118140960795 + 2945078 * 2 ^ 59
def prefixEnd_2945078 : Nat := 4983230072969 + 3 ^ 40 * 2945078 * 2
def baseEnd_2945078 : Nat := 1512240578982133602480839

theorem tailTrace_2945078 : CollatzResearch.WordTrace tailWord_2945078 prefixEnd_2945078 1512240578982133602480839 := by
  unfold tailWord_2945078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713488701530803757705243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71610546149661906748855925 6713488701530803757705243)
  ·
    refine ⟨10070233052296205636557865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713488701530803757705243 10070233052296205636557865)
    ·
      refine ⟨7552674789222154227418399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10070233052296205636557865 7552674789222154227418399)
      ·
        refine ⟨11329012183833231341127599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7552674789222154227418399 11329012183833231341127599)
        ·
          refine ⟨16993518275749847011691399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11329012183833231341127599 16993518275749847011691399)
          ·
            refine ⟨25490277413624770517537099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16993518275749847011691399 25490277413624770517537099)
            ·
              refine ⟨38235416120437155776305649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25490277413624770517537099 38235416120437155776305649)
              ·
                refine ⟨28676562090327866832229237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38235416120437155776305649 28676562090327866832229237)
                ·
                  refine ⟨2688427695968237515521491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28676562090327866832229237 2688427695968237515521491)
                  ·
                    refine ⟨4032641543952356273282237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2688427695968237515521491 4032641543952356273282237)
                    ·
                      refine ⟨1512240578982133602480839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4032641543952356273282237 1512240578982133602480839)
                      ·
                        rfl

theorem cell23_2945078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2945078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945078 prefixEnd_2945078 := by exact prefixLift 2945078
  have htrace : WordTrace (prefixWord ++ tailWord_2945078) baseStart_2945078 baseEnd_2945078 := by
    simpa [prefixWord, tailWord_2945078, baseEnd_2945078] using wordTrace_append hprefix tailTrace_2945078
  have hstable : (prefixWord ++ tailWord_2945078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945078).length < 2 ^ (prefixWord ++ tailWord_2945078).sum := by decide
  have hdescent : baseEnd_2945078 < baseStart_2945078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945111 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 2, 4]
def baseStart_2945111 : Nat := 118140960795 + 2945111 * 2 ^ 59
def prefixEnd_2945111 : Nat := 4983230072969 + 3 ^ 40 * 2945111 * 2
def baseEnd_2945111 : Nat := 504085841281243991122729

theorem tailTrace_2945111 : CollatzResearch.WordTrace tailWord_2945111 prefixEnd_2945111 504085841281243991122729 := by
  unfold tailWord_2945111
  simp only [CollatzResearch.WordTrace]
  refine ⟨107417022833373306759235187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71611348555582204506156791 107417022833373306759235187)
  ·
    refine ⟨161125534250059960138852781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107417022833373306759235187 161125534250059960138852781)
    ·
      refine ⟨60422075343772485052069793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161125534250059960138852781 60422075343772485052069793)
      ·
        refine ⟨45316556507829363789052345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60422075343772485052069793 45316556507829363789052345)
        ·
          refine ⟨33987417380872022841789259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45316556507829363789052345 33987417380872022841789259)
          ·
            refine ⟨50981126071308034262683889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33987417380872022841789259 50981126071308034262683889)
            ·
              refine ⟨38235844553481025697012917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50981126071308034262683889 38235844553481025697012917)
              ·
                refine ⟨3584610426888846159094961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38235844553481025697012917 3584610426888846159094961)
                ·
                  refine ⟨2688457820166634619321221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584610426888846159094961 2688457820166634619321221)
                  ·
                    refine ⟨504085841281243991122729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688457820166634619321221 504085841281243991122729)
                    ·
                      rfl

theorem cell23_2945111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_2945111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945111 prefixEnd_2945111 := by exact prefixLift 2945111
  have htrace : WordTrace (prefixWord ++ tailWord_2945111) baseStart_2945111 baseEnd_2945111 := by
    simpa [prefixWord, tailWord_2945111, baseEnd_2945111] using wordTrace_append hprefix tailTrace_2945111
  have hstable : (prefixWord ++ tailWord_2945111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945111).length < 2 ^ (prefixWord ++ tailWord_2945111).sum := by decide
  have hdescent : baseEnd_2945111 < baseStart_2945111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945114 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2945114 : Nat := 118140960795 + 2945114 * 2 ^ 59
def prefixEnd_2945114 : Nat := 4983230072969 + 3 ^ 40 * 2945114 * 2
def baseEnd_2945114 : Nat := 1512259064285695461630673

theorem tailTrace_2945114 : CollatzResearch.WordTrace tailWord_2945114 prefixEnd_2945114 1512259064285695461630673 := by
  unfold tailWord_2945114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26854283063090609567898599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71611421501574958847729597 26854283063090609567898599)
  ·
    refine ⟨40281424594635914351847899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26854283063090609567898599 40281424594635914351847899)
    ·
      refine ⟨60422136891953871527771849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40281424594635914351847899 60422136891953871527771849)
      ·
        refine ⟨45316602668965403645828887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60422136891953871527771849 45316602668965403645828887)
        ·
          refine ⟨67974904003448105468743331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45316602668965403645828887 67974904003448105468743331)
          ·
            refine ⟨101962356005172158203114997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67974904003448105468743331 101962356005172158203114997)
            ·
              refine ⟨9558970875484889831542031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101962356005172158203114997 9558970875484889831542031)
              ·
                refine ⟨14338456313227334747313047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9558970875484889831542031 14338456313227334747313047)
                ·
                  refine ⟨21507684469841002120969571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14338456313227334747313047 21507684469841002120969571)
                  ·
                    refine ⟨32261526704761503181454357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21507684469841002120969571 32261526704761503181454357)
                    ·
                      refine ⟨1512259064285695461630673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32261526704761503181454357 1512259064285695461630673)
                      ·
                        rfl

theorem cell23_2945114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2945114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945114 prefixEnd_2945114 := by exact prefixLift 2945114
  have htrace : WordTrace (prefixWord ++ tailWord_2945114) baseStart_2945114 baseEnd_2945114 := by
    simpa [prefixWord, tailWord_2945114, baseEnd_2945114] using wordTrace_append hprefix tailTrace_2945114
  have hstable : (prefixWord ++ tailWord_2945114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945114).length < 2 ^ (prefixWord ++ tailWord_2945114).sum := by decide
  have hdescent : baseEnd_2945114 < baseStart_2945114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945138 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2945138 : Nat := 118140960795 + 2945138 * 2 ^ 59
def prefixEnd_2945138 : Nat := 4983230072969 + 3 ^ 40 * 2945138 * 2
def baseEnd_2945138 : Nat := 1512271387821403367730563

theorem tailTrace_2945138 : CollatzResearch.WordTrace tailWord_2945138 prefixEnd_2945138 1512271387821403367730563 := by
  unfold tailWord_2945138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26854501901068872592617017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71612005069516993580312045 26854501901068872592617017)
  ·
    refine ⟨20140876425801654444462763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26854501901068872592617017 20140876425801654444462763)
    ·
      refine ⟨30211314638702481666694145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20140876425801654444462763 30211314638702481666694145)
      ·
        refine ⟨22658485979026861250020609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30211314638702481666694145 22658485979026861250020609)
        ·
          refine ⟨16993864484270145937515457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22658485979026861250020609 16993864484270145937515457)
          ·
            refine ⟨12745398363202609453136593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16993864484270145937515457 12745398363202609453136593)
            ·
              refine ⟨9559048772401957089852445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12745398363202609453136593 9559048772401957089852445)
              ·
                refine ⟨3584643289650733908694667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9559048772401957089852445 3584643289650733908694667)
                ·
                  refine ⟨5376964934476100863042001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584643289650733908694667 5376964934476100863042001)
                  ·
                    refine ⟨4032723700857075647281501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5376964934476100863042001 4032723700857075647281501)
                    ·
                      refine ⟨1512271387821403367730563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4032723700857075647281501 1512271387821403367730563)
                      ·
                        rfl

theorem cell23_2945138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2945138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945138 prefixEnd_2945138 := by exact prefixLift 2945138
  have htrace : WordTrace (prefixWord ++ tailWord_2945138) baseStart_2945138 baseEnd_2945138 := by
    simpa [prefixWord, tailWord_2945138, baseEnd_2945138] using wordTrace_append hprefix tailTrace_2945138
  have hstable : (prefixWord ++ tailWord_2945138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945138).length < 2 ^ (prefixWord ++ tailWord_2945138).sum := by decide
  have hdescent : baseEnd_2945138 < baseStart_2945138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945168 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3]
def baseStart_2945168 : Nat := 118140960795 + 2945168 * 2 ^ 59
def prefixEnd_2945168 : Nat := 4983230072969 + 3 ^ 40 * 2945168 * 2
def baseEnd_2945168 : Nat := 1512286792241038250355425

theorem tailTrace_2945168 : CollatzResearch.WordTrace tailWord_2945168 prefixEnd_2945168 1512286792241038250355425 := by
  unfold tailWord_2945168
  simp only [CollatzResearch.WordTrace]
  refine ⟨53709550897083402747030079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71612734529444536996040105 53709550897083402747030079)
  ·
    refine ⟨80564326345625104120545119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53709550897083402747030079 80564326345625104120545119)
    ·
      refine ⟨120846489518437656180817679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80564326345625104120545119 120846489518437656180817679)
      ·
        refine ⟨181269734277656484271226519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120846489518437656180817679 181269734277656484271226519)
        ·
          refine ⟨271904601416484726406839779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181269734277656484271226519 271904601416484726406839779)
          ·
            refine ⟨407856902124727089610259669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271904601416484726406839779 407856902124727089610259669)
            ·
              refine ⟨9559146143548291162740461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 407856902124727089610259669 9559146143548291162740461)
              ·
                refine ⟨3584679803830609186027673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9559146143548291162740461 3584679803830609186027673)
                ·
                  refine ⟨2688509852872956889520755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584679803830609186027673 2688509852872956889520755)
                  ·
                    refine ⟨4032764779309435334281133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2688509852872956889520755 4032764779309435334281133)
                    ·
                      refine ⟨1512286792241038250355425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4032764779309435334281133 1512286792241038250355425)
                      ·
                        rfl

theorem cell23_2945168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_2945168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945168 prefixEnd_2945168 := by exact prefixLift 2945168
  have htrace : WordTrace (prefixWord ++ tailWord_2945168) baseStart_2945168 baseEnd_2945168 := by
    simpa [prefixWord, tailWord_2945168, baseEnd_2945168] using wordTrace_append hprefix tailTrace_2945168
  have hstable : (prefixWord ++ tailWord_2945168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945168).length < 2 ^ (prefixWord ++ tailWord_2945168).sum := by decide
  have hdescent : baseEnd_2945168 < baseStart_2945168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945248 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 5]
def baseStart_2945248 : Nat := 118140960795 + 2945248 * 2 ^ 59
def prefixEnd_2945248 : Nat := 4983230072969 + 3 ^ 40 * 2945248 * 2
def baseEnd_2945248 : Nat := 168036430077044215261673

theorem tailTrace_2945248 : CollatzResearch.WordTrace tailWord_2945248 prefixEnd_2945248 168036430077044215261673 := by
  unfold tailWord_2945248
  simp only [CollatzResearch.WordTrace]
  refine ⟨53711009816938489578486199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71614679755917986104648265 53711009816938489578486199)
  ·
    refine ⟨80566514725407734367729299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53711009816938489578486199 80566514725407734367729299)
    ·
      refine ⟨120849772088111601551593949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80566514725407734367729299 120849772088111601551593949)
      ·
        refine ⟨45318664533041850581847731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120849772088111601551593949 45318664533041850581847731)
        ·
          refine ⟨67977996799562775872771597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45318664533041850581847731 67977996799562775872771597)
          ·
            refine ⟨25491748799836040952289349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67977996799562775872771597 25491748799836040952289349)
            ·
              refine ⟨4779702899969257678554253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25491748799836040952289349 4779702899969257678554253)
              ·
                refine ⟨1792388587488471629457845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4779702899969257678554253 1792388587488471629457845)
                ·
                  refine ⟨168036430077044215261673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792388587488471629457845 168036430077044215261673)
                  ·
                    rfl

theorem cell23_2945248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 5].length) (baseStart_2945248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945248 prefixEnd_2945248 := by exact prefixLift 2945248
  have htrace : WordTrace (prefixWord ++ tailWord_2945248) baseStart_2945248 baseEnd_2945248 := by
    simpa [prefixWord, tailWord_2945248, baseEnd_2945248] using wordTrace_append hprefix tailTrace_2945248
  have hstable : (prefixWord ++ tailWord_2945248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945248).length < 2 ^ (prefixWord ++ tailWord_2945248).sum := by decide
  have hdescent : baseEnd_2945248 < baseStart_2945248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945281 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2945281 : Nat := 118140960795 + 2945281 * 2 ^ 59
def prefixEnd_2945281 : Nat := 4983230072969 + 3 ^ 40 * 2945281 * 2
def baseEnd_2945281 : Nat := 1512344815554996308242405

theorem tailTrace_2945281 : CollatzResearch.WordTrace tailWord_2945281 prefixEnd_2945281 1512344815554996308242405 := by
  unfold tailWord_2945281
  simp only [CollatzResearch.WordTrace]
  refine ⟨107423223242757425792923697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71615482161838283861949131 107423223242757425792923697)
  ·
    refine ⟨80567417432068069344692773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107423223242757425792923697 80567417432068069344692773)
    ·
      refine ⟨15106390768512763002129895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80567417432068069344692773 15106390768512763002129895)
      ·
        refine ⟨22659586152769144503194843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106390768512763002129895 22659586152769144503194843)
        ·
          refine ⟨33989379229153716754792265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659586152769144503194843 33989379229153716754792265)
          ·
            refine ⟨25492034421865287566094199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33989379229153716754792265 25492034421865287566094199)
            ·
              refine ⟨38238051632797931349141299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25492034421865287566094199 38238051632797931349141299)
              ·
                refine ⟨57357077449196897023711949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38238051632797931349141299 57357077449196897023711949)
                ·
                  refine ⟨21508904043448836383891981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57357077449196897023711949 21508904043448836383891981)
                  ·
                    refine ⟨8065839016293313643959493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21508904043448836383891981 8065839016293313643959493)
                    ·
                      refine ⟨1512344815554996308242405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8065839016293313643959493 1512344815554996308242405)
                      ·
                        rfl

theorem cell23_2945281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2945281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945281 prefixEnd_2945281 := by exact prefixLift 2945281
  have htrace : WordTrace (prefixWord ++ tailWord_2945281) baseStart_2945281 baseEnd_2945281 := by
    simpa [prefixWord, tailWord_2945281, baseEnd_2945281] using wordTrace_append hprefix tailTrace_2945281
  have hstable : (prefixWord ++ tailWord_2945281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945281).length < 2 ^ (prefixWord ++ tailWord_2945281).sum := by decide
  have hdescent : baseEnd_2945281 < baseStart_2945281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945338 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_2945338 : Nat := 118140960795 + 2945338 * 2 ^ 59
def prefixEnd_2945338 : Nat := 4983230072969 + 3 ^ 40 * 2945338 * 2
def baseEnd_2945338 : Nat := 168041564883589176136627

theorem tailTrace_2945338 : CollatzResearch.WordTrace tailWord_2945338 prefixEnd_2945338 168041564883589176136627 := by
  unfold tailWord_2945338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26856325550887731131937167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71616868135700616351832445 26856325550887731131937167)
  ·
    refine ⟨40284488326331596697905751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26856325550887731131937167 40284488326331596697905751)
    ·
      refine ⟨60426732489497395046858627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40284488326331596697905751 60426732489497395046858627)
      ·
        refine ⟨90640098734246092570287941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60426732489497395046858627 90640098734246092570287941)
        ·
          refine ⟨16995018512671142356928989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90640098734246092570287941 16995018512671142356928989)
          ·
            refine ⟨6373131942251678383848371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16995018512671142356928989 6373131942251678383848371)
            ·
              refine ⟨9559697913377517575772557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373131942251678383848371 9559697913377517575772557)
              ·
                refine ⟨3584886717516569090914709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9559697913377517575772557 3584886717516569090914709)
                ·
                  refine ⟨168041564883589176136627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3584886717516569090914709 168041564883589176136627)
                  ·
                    rfl

theorem cell23_2945338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_2945338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945338 prefixEnd_2945338 := by exact prefixLift 2945338
  have htrace : WordTrace (prefixWord ++ tailWord_2945338) baseStart_2945338 baseEnd_2945338 := by
    simpa [prefixWord, tailWord_2945338, baseEnd_2945338] using wordTrace_append hprefix tailTrace_2945338
  have hstable : (prefixWord ++ tailWord_2945338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945338).length < 2 ^ (prefixWord ++ tailWord_2945338).sum := by decide
  have hdescent : baseEnd_2945338 < baseStart_2945338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945372 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 6]
def baseStart_2945372 : Nat := 118140960795 + 2945372 * 2 ^ 59
def prefixEnd_2945372 : Nat := 4983230072969 + 3 ^ 40 * 2945372 * 2
def baseEnd_2945372 : Nat := 168043504699395050244943

theorem tailTrace_2945372 : CollatzResearch.WordTrace tailWord_2945372 prefixEnd_2945372 168043504699395050244943 := by
  unfold tailWord_2945372
  simp only [CollatzResearch.WordTrace]
  refine ⟨53713271142713874167243185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71617694856951832222990913 53713271142713874167243185)
  ·
    refine ⟨40284953357035405625432389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53713271142713874167243185 40284953357035405625432389)
    ·
      refine ⟨7553428754444138554768573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40284953357035405625432389 7553428754444138554768573)
      ·
        refine ⟨2832535782916551958038215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7553428754444138554768573 2832535782916551958038215)
        ·
          refine ⟨4248803674374827937057323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832535782916551958038215 4248803674374827937057323)
          ·
            refine ⟨6373205511562241905585985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248803674374827937057323 6373205511562241905585985)
            ·
              refine ⟨4779904133671681429189489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6373205511562241905585985 4779904133671681429189489)
              ·
                refine ⟨3584928100253761071892117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4779904133671681429189489 3584928100253761071892117)
                ·
                  refine ⟨168043504699395050244943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3584928100253761071892117 168043504699395050244943)
                  ·
                    rfl

theorem cell23_2945372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_2945372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945372 prefixEnd_2945372 := by exact prefixLift 2945372
  have htrace : WordTrace (prefixWord ++ tailWord_2945372) baseStart_2945372 baseEnd_2945372 := by
    simpa [prefixWord, tailWord_2945372, baseEnd_2945372] using wordTrace_append hprefix tailTrace_2945372
  have hstable : (prefixWord ++ tailWord_2945372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945372).length < 2 ^ (prefixWord ++ tailWord_2945372).sum := by decide
  have hdescent : baseEnd_2945372 < baseStart_2945372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945375 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 2, 3, 2]
def baseStart_2945375 : Nat := 118140960795 + 2945375 * 2 ^ 59
def prefixEnd_2945375 : Nat := 4983230072969 + 3 ^ 40 * 2945375 * 2
def baseEnd_2945375 : Nat := 1512393082736518940466973

theorem tailTrace_2945375 : CollatzResearch.WordTrace tailWord_2945375 prefixEnd_2945375 1512393082736518940466973 := by
  unfold tailWord_2945375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107426651704416879846845579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71617767802944586564563719 107426651704416879846845579)
  ·
    refine ⟨161139977556625319770268369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107426651704416879846845579 161139977556625319770268369)
    ·
      refine ⟨120854983167468989827701277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161139977556625319770268369 120854983167468989827701277)
      ·
        refine ⟨45320618687800871185387979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120854983167468989827701277 45320618687800871185387979)
        ·
          refine ⟨67980928031701306778081969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45320618687800871185387979 67980928031701306778081969)
          ·
            refine ⟨50985696023775980083561477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67980928031701306778081969 50985696023775980083561477)
            ·
              refine ⟨9559818004457996265667777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50985696023775980083561477 9559818004457996265667777)
              ·
                refine ⟨7169863503343497199250833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9559818004457996265667777 7169863503343497199250833)
                ·
                  refine ⟨5377397627507622899438125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169863503343497199250833 5377397627507622899438125)
                  ·
                    refine ⟨2016524110315358587289297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5377397627507622899438125 2016524110315358587289297)
                    ·
                      refine ⟨1512393082736518940466973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016524110315358587289297 1512393082736518940466973)
                      ·
                        rfl

theorem cell23_2945375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_2945375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945375 prefixEnd_2945375 := by exact prefixLift 2945375
  have htrace : WordTrace (prefixWord ++ tailWord_2945375) baseStart_2945375 baseEnd_2945375 := by
    simpa [prefixWord, tailWord_2945375, baseEnd_2945375] using wordTrace_append hprefix tailTrace_2945375
  have hstable : (prefixWord ++ tailWord_2945375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945375).length < 2 ^ (prefixWord ++ tailWord_2945375).sum := by decide
  have hdescent : baseEnd_2945375 < baseStart_2945375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945376 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 1, 4]
def baseStart_2945376 : Nat := 118140960795 + 2945376 * 2 ^ 59
def prefixEnd_2945376 : Nat := 4983230072969 + 3 ^ 40 * 2945376 * 2
def baseEnd_2945376 : Nat := 504131198739057812184823

theorem tailTrace_2945376 : CollatzResearch.WordTrace tailWord_2945376 prefixEnd_2945376 504131198739057812184823 := by
  unfold tailWord_2945376
  simp only [CollatzResearch.WordTrace]
  refine ⟨53713344088706628508815991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71617792118275504678421321 53713344088706628508815991)
  ·
    refine ⟨80570016133059942763223987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53713344088706628508815991 80570016133059942763223987)
    ·
      refine ⟨120855024199589914144835981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80570016133059942763223987 120855024199589914144835981)
      ·
        refine ⟨45320634074846217804313493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120855024199589914144835981 45320634074846217804313493)
        ·
          refine ⟨2124404722258416459577195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45320634074846217804313493 2124404722258416459577195)
          ·
            refine ⟨3186607083387624689365793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124404722258416459577195 3186607083387624689365793)
            ·
              refine ⟨2389955312540718517024345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186607083387624689365793 2389955312540718517024345)
              ·
                refine ⟨1792466484405538887768259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2389955312540718517024345 1792466484405538887768259)
                ·
                  refine ⟨2688699726608308331652389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792466484405538887768259 2688699726608308331652389)
                  ·
                    refine ⟨504131198739057812184823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688699726608308331652389 504131198739057812184823)
                    ·
                      rfl

theorem cell23_2945376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 4].length) (baseStart_2945376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945376 prefixEnd_2945376 := by exact prefixLift 2945376
  have htrace : WordTrace (prefixWord ++ tailWord_2945376) baseStart_2945376 baseEnd_2945376 := by
    simpa [prefixWord, tailWord_2945376, baseEnd_2945376] using wordTrace_append hprefix tailTrace_2945376
  have hstable : (prefixWord ++ tailWord_2945376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945376).length < 2 ^ (prefixWord ++ tailWord_2945376).sum := by decide
  have hdescent : baseEnd_2945376 < baseStart_2945376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945409 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2945409 : Nat := 118140960795 + 2945409 * 2 ^ 59
def prefixEnd_2945409 : Nat := 4983230072969 + 3 ^ 40 * 2945409 * 2
def baseEnd_2945409 : Nat := 1512410541078771807441817

theorem tailTrace_2945409 : CollatzResearch.WordTrace tailWord_2945409 prefixEnd_2945409 1512410541078771807441817 := by
  unfold tailWord_2945409
  simp only [CollatzResearch.WordTrace]
  refine ⟨107427891786293703653583281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71618594524195802435722187 107427891786293703653583281)
  ·
    refine ⟨80570918839720277740187461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107427891786293703653583281 80570918839720277740187461)
    ·
      refine ⟨15107047282447552076285149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80570918839720277740187461 15107047282447552076285149)
      ·
        refine ⟨5665142730917832028606931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15107047282447552076285149 5665142730917832028606931)
        ·
          refine ⟨8497714096376748042910397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665142730917832028606931 8497714096376748042910397)
          ·
            refine ⟨3186642786141280516091399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8497714096376748042910397 3186642786141280516091399)
            ·
              refine ⟨4779964179211920774137099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186642786141280516091399 4779964179211920774137099)
              ·
                refine ⟨7169946268817881161205649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779964179211920774137099 7169946268817881161205649)
                ·
                  refine ⟨5377459701613410870904237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7169946268817881161205649 5377459701613410870904237)
                  ·
                    refine ⟨2016547388105029076589089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5377459701613410870904237 2016547388105029076589089)
                    ·
                      refine ⟨1512410541078771807441817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016547388105029076589089 1512410541078771807441817)
                      ·
                        rfl

theorem cell23_2945409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2945409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945409 prefixEnd_2945409 := by exact prefixLift 2945409
  have htrace : WordTrace (prefixWord ++ tailWord_2945409) baseStart_2945409 baseEnd_2945409 := by
    simpa [prefixWord, tailWord_2945409, baseEnd_2945409] using wordTrace_append hprefix tailTrace_2945409
  have hstable : (prefixWord ++ tailWord_2945409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945409).length < 2 ^ (prefixWord ++ tailWord_2945409).sum := by decide
  have hdescent : baseEnd_2945409 < baseStart_2945409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945422 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2945422 : Nat := 118140960795 + 2945422 * 2 ^ 59
def prefixEnd_2945422 : Nat := 4983230072969 + 3 ^ 40 * 2945422 * 2
def baseEnd_2945422 : Nat := 1512417216327280256579257

theorem tailTrace_2945422 : CollatzResearch.WordTrace tailWord_2945422 prefixEnd_2945422 1512417216327280256579257 := by
  unfold tailWord_2945422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13428545741905825859225815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71618910623497737915871013 13428545741905825859225815)
  ·
    refine ⟨20142818612858738788838723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13428545741905825859225815 20142818612858738788838723)
    ·
      refine ⟨30214227919288108183258085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20142818612858738788838723 30214227919288108183258085)
      ·
        refine ⟨5665167734866520284360891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30214227919288108183258085 5665167734866520284360891)
        ·
          refine ⟨8497751602299780426541337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665167734866520284360891 8497751602299780426541337)
          ·
            refine ⟨6373313701724835319906003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8497751602299780426541337 6373313701724835319906003)
            ·
              refine ⟨9559970552587252979859005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373313701724835319906003 9559970552587252979859005)
              ·
                refine ⟨3584988957220219867447127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9559970552587252979859005 3584988957220219867447127)
                ·
                  refine ⟨5377483435830329801170691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584988957220219867447127 5377483435830329801170691)
                  ·
                    refine ⟨8066225153745494701756037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5377483435830329801170691 8066225153745494701756037)
                    ·
                      refine ⟨1512417216327280256579257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8066225153745494701756037 1512417216327280256579257)
                      ·
                        rfl

theorem cell23_2945422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2945422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945422 prefixEnd_2945422 := by exact prefixLift 2945422
  have htrace : WordTrace (prefixWord ++ tailWord_2945422) baseStart_2945422 baseEnd_2945422 := by
    simpa [prefixWord, tailWord_2945422, baseEnd_2945422] using wordTrace_append hprefix tailTrace_2945422
  have hstable : (prefixWord ++ tailWord_2945422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945422).length < 2 ^ (prefixWord ++ tailWord_2945422).sum := by decide
  have hdescent : baseEnd_2945422 < baseStart_2945422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945432 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_2945432 : Nat := 118140960795 + 2945432 * 2 ^ 59
def prefixEnd_2945432 : Nat := 4983230072969 + 3 ^ 40 * 2945432 * 2
def baseEnd_2945432 : Nat := 504140783711275072484737

theorem tailTrace_2945432 : CollatzResearch.WordTrace tailWord_2945432 prefixEnd_2945432 504140783711275072484737 := by
  unfold tailWord_2945432
  simp only [CollatzResearch.WordTrace]
  refine ⟨53714365332605189290835275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71619153776806919054447033 53714365332605189290835275)
  ·
    refine ⟨80571547998907783936252913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53714365332605189290835275 80571547998907783936252913)
    ·
      refine ⟨60428660999180837952189685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80571547998907783936252913 60428660999180837952189685)
      ·
        refine ⟨5665186968673203558017783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60428660999180837952189685 5665186968673203558017783)
        ·
          refine ⟨8497780453009805337026675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665186968673203558017783 8497780453009805337026675)
          ·
            refine ⟨12746670679514708005540013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8497780453009805337026675 12746670679514708005540013)
            ·
              refine ⟨4780001504818015502077505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12746670679514708005540013 4780001504818015502077505)
              ·
                refine ⟨3585001128613511626558129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780001504818015502077505 3585001128613511626558129)
                ·
                  refine ⟨2688750846460133719918597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3585001128613511626558129 2688750846460133719918597)
                  ·
                    refine ⟨504140783711275072484737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688750846460133719918597 504140783711275072484737)
                    ·
                      rfl

theorem cell23_2945432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_2945432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945432 prefixEnd_2945432 := by exact prefixLift 2945432
  have htrace : WordTrace (prefixWord ++ tailWord_2945432) baseStart_2945432 baseEnd_2945432 := by
    simpa [prefixWord, tailWord_2945432, baseEnd_2945432] using wordTrace_append hprefix tailTrace_2945432
  have hstable : (prefixWord ++ tailWord_2945432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945432).length < 2 ^ (prefixWord ++ tailWord_2945432).sum := by decide
  have hdescent : baseEnd_2945432 < baseStart_2945432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
