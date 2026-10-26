import V185TrunkScan23Chunk1014

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6010040 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_6010040 : Nat := 118140960795 + 6010040 * 2 ^ 59
def prefixEnd_6010040 : Nat := 4983230072969 + 3 ^ 40 * 6010040 * 2
def baseEnd_6010040 : Nat := 3086039272747770924560335

theorem tailTrace_6010040 : CollatzResearch.WordTrace tailWord_6010040 prefixEnd_6010040 3086039272747770924560335 := by
  unfold tailWord_6010040
  simp only [CollatzResearch.WordTrace]
  refine ⟨109602083573329493979297787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146136111431105991972397049 109602083573329493979297787)
  ·
    refine ⟨164403125359994240968946681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109602083573329493979297787 164403125359994240968946681)
    ·
      refine ⟨123302344019995680726710011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164403125359994240968946681 123302344019995680726710011)
      ·
        refine ⟨184953516029993521090065017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123302344019995680726710011 184953516029993521090065017)
        ·
          refine ⟨138715137022495140817548763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184953516029993521090065017 138715137022495140817548763)
          ·
            refine ⟨208072705533742711226323145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138715137022495140817548763 208072705533742711226323145)
            ·
              refine ⟨156054529150307033419742359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208072705533742711226323145 156054529150307033419742359)
              ·
                refine ⟨234081793725460550129613539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156054529150307033419742359 234081793725460550129613539)
                ·
                  refine ⟨351122690588190825194420309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234081793725460550129613539 351122690588190825194420309)
                  ·
                    refine ⟨4114719030330361232747113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 351122690588190825194420309 4114719030330361232747113)
                    ·
                      refine ⟨3086039272747770924560335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114719030330361232747113 3086039272747770924560335)
                      ·
                        rfl

theorem cell23_6010040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_6010040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010040 prefixEnd_6010040 := by exact prefixLift 6010040
  have htrace : WordTrace (prefixWord ++ tailWord_6010040) baseStart_6010040 baseEnd_6010040 := by
    simpa [prefixWord, tailWord_6010040, baseEnd_6010040] using wordTrace_append hprefix tailTrace_6010040
  have hstable : (prefixWord ++ tailWord_6010040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010040).length < 2 ^ (prefixWord ++ tailWord_6010040).sum := by decide
  have hdescent : baseEnd_6010040 < baseStart_6010040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010043 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_6010043 : Nat := 118140960795 + 6010043 * 2 ^ 59
def prefixEnd_6010043 : Nat := 4983230072969 + 3 ^ 40 * 6010043 * 2
def baseEnd_6010043 : Nat := 3086040813189734412822821

theorem tailTrace_6010043 : CollatzResearch.WordTrace tailWord_6010043 prefixEnd_6010043 3086040813189734412822821 := by
  unfold tailWord_6010043
  simp only [CollatzResearch.WordTrace]
  refine ⟨219204276565648119470954783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146136184377098746313969855 219204276565648119470954783)
  ·
    refine ⟨328806414848472179206432175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219204276565648119470954783 328806414848472179206432175)
    ·
      refine ⟨493209622272708268809648263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328806414848472179206432175 493209622272708268809648263)
      ·
        refine ⟨739814433409062403214472395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493209622272708268809648263 739814433409062403214472395)
        ·
          refine ⟨1109721650113593604821708593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739814433409062403214472395 1109721650113593604821708593)
          ·
            refine ⟨832291237585195203616281445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109721650113593604821708593 832291237585195203616281445)
            ·
              refine ⟨156054607047224100678052771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 832291237585195203616281445 156054607047224100678052771)
              ·
                refine ⟨234081910570836151017079157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156054607047224100678052771 234081910570836151017079157)
                ·
                  refine ⟨21945179116015889157851171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234081910570836151017079157 21945179116015889157851171)
                  ·
                    refine ⟨32917768674023833736776757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21945179116015889157851171 32917768674023833736776757)
                    ·
                      refine ⟨3086040813189734412822821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32917768674023833736776757 3086040813189734412822821)
                      ·
                        rfl

theorem cell23_6010043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_6010043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010043 prefixEnd_6010043 := by exact prefixLift 6010043
  have htrace : WordTrace (prefixWord ++ tailWord_6010043) baseStart_6010043 baseEnd_6010043 := by
    simpa [prefixWord, tailWord_6010043, baseEnd_6010043] using wordTrace_append hprefix tailTrace_6010043
  have hstable : (prefixWord ++ tailWord_6010043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010043).length < 2 ^ (prefixWord ++ tailWord_6010043).sum := by decide
  have hdescent : baseEnd_6010043 < baseStart_6010043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010044 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_6010044 : Nat := 118140960795 + 6010044 * 2 ^ 59
def prefixEnd_6010044 : Nat := 4983230072969 + 3 ^ 40 * 6010044 * 2
def baseEnd_6010044 : Nat := 3086041326670388908910317

theorem tailTrace_6010044 : CollatzResearch.WordTrace tailWord_6010044 prefixEnd_6010044 3086041326670388908910317 := by
  unfold tailWord_6010044
  simp only [CollatzResearch.WordTrace]
  refine ⟨109602156519322248320870593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146136208692429664427827457 109602156519322248320870593)
  ·
    refine ⟨82201617389491686240652945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109602156519322248320870593 82201617389491686240652945)
    ·
      refine ⟨61651213042118764680489709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82201617389491686240652945 61651213042118764680489709)
      ·
        refine ⟨23119204890794536755183641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61651213042118764680489709 23119204890794536755183641)
        ·
          refine ⟨17339403668095902566387731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23119204890794536755183641 17339403668095902566387731)
          ·
            refine ⟨26009105502143853849581597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339403668095902566387731 26009105502143853849581597)
            ·
              refine ⟨9753414563303945193593099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26009105502143853849581597 9753414563303945193593099)
              ·
                refine ⟨14630121844955917790389649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9753414563303945193593099 14630121844955917790389649)
                ·
                  refine ⟨10972591383716938342792237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14630121844955917790389649 10972591383716938342792237)
                  ·
                    refine ⟨4114721768893851878547089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10972591383716938342792237 4114721768893851878547089)
                    ·
                      refine ⟨3086041326670388908910317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114721768893851878547089 3086041326670388908910317)
                      ·
                        rfl

theorem cell23_6010044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_6010044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010044 prefixEnd_6010044 := by exact prefixLift 6010044
  have htrace : WordTrace (prefixWord ++ tailWord_6010044) baseStart_6010044 baseEnd_6010044 := by
    simpa [prefixWord, tailWord_6010044, baseEnd_6010044] using wordTrace_append hprefix tailTrace_6010044
  have hstable : (prefixWord ++ tailWord_6010044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010044).length < 2 ^ (prefixWord ++ tailWord_6010044).sum := by decide
  have hdescent : baseEnd_6010044 < baseStart_6010044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010053 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_6010053 : Nat := 118140960795 + 6010053 * 2 ^ 59
def prefixEnd_6010053 : Nat := 4983230072969 + 3 ^ 40 * 6010053 * 2
def baseEnd_6010053 : Nat := 3086045947996279373697775

theorem tailTrace_6010053 : CollatzResearch.WordTrace tailWord_6010053 prefixEnd_6010053 3086045947996279373697775 := by
  unfold tailWord_6010053
  simp only [CollatzResearch.WordTrace]
  refine ⟨219204641295611891178818813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146136427530407927452545875 219204641295611891178818813)
  ·
    refine ⟨82201740485854459192057055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219204641295611891178818813 82201740485854459192057055)
    ·
      refine ⟨123302610728781688788085583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82201740485854459192057055 123302610728781688788085583)
      ·
        refine ⟨184953916093172533182128375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123302610728781688788085583 184953916093172533182128375)
        ·
          refine ⟨277430874139758799773192563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184953916093172533182128375 277430874139758799773192563)
          ·
            refine ⟨416146311209638199659788845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277430874139758799773192563 416146311209638199659788845)
            ·
              refine ⟨156054866703614324872420817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416146311209638199659788845 156054866703614324872420817)
              ·
                refine ⟨117041150027710743654315613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156054866703614324872420817 117041150027710743654315613)
                ·
                  refine ⟨43890431260391528870368355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117041150027710743654315613 43890431260391528870368355)
                  ·
                    refine ⟨65835646890587293305552533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43890431260391528870368355 65835646890587293305552533)
                    ·
                      refine ⟨3086045947996279373697775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65835646890587293305552533 3086045947996279373697775)
                      ·
                        rfl

theorem cell23_6010053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_6010053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010053 prefixEnd_6010053 := by exact prefixLift 6010053
  have htrace : WordTrace (prefixWord ++ tailWord_6010053) baseStart_6010053 baseEnd_6010053 := by
    simpa [prefixWord, tailWord_6010053, baseEnd_6010053] using wordTrace_append hprefix tailTrace_6010053
  have hstable : (prefixWord ++ tailWord_6010053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010053).length < 2 ^ (prefixWord ++ tailWord_6010053).sum := by decide
  have hdescent : baseEnd_6010053 < baseStart_6010053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010073 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_6010073 : Nat := 118140960795 + 6010073 * 2 ^ 59
def prefixEnd_6010073 : Nat := 4983230072969 + 3 ^ 40 * 6010073 * 2
def baseEnd_6010073 : Nat := 3086056217609369295447683

theorem tailTrace_6010073 : CollatzResearch.WordTrace tailWord_6010073 prefixEnd_6010073 3086056217609369295447683 := by
  unfold tailWord_6010073
  simp only [CollatzResearch.WordTrace]
  refine ⟨219205370755539434594546873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146136913837026289729697915 219205370755539434594546873)
  ·
    refine ⟨164404028066654575945910155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219205370755539434594546873 164404028066654575945910155)
    ·
      refine ⟨246606042099981863918865233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164404028066654575945910155 246606042099981863918865233)
      ·
        refine ⟨184954531574986397939148925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246606042099981863918865233 184954531574986397939148925)
        ·
          refine ⟨69357949340619899227180847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184954531574986397939148925 69357949340619899227180847)
          ·
            refine ⟨104036924010929848840771271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69357949340619899227180847 104036924010929848840771271)
            ·
              refine ⟨156055386016394773261156907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104036924010929848840771271 156055386016394773261156907)
              ·
                refine ⟨234083079024592159891735361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156055386016394773261156907 234083079024592159891735361)
                ·
                  refine ⟨175562309268444119918801521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234083079024592159891735361 175562309268444119918801521)
                  ·
                    refine ⟨131671731951333089939101141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175562309268444119918801521 131671731951333089939101141)
                    ·
                      refine ⟨3086056217609369295447683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131671731951333089939101141 3086056217609369295447683)
                      ·
                        rfl

theorem cell23_6010073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_6010073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010073 prefixEnd_6010073 := by exact prefixLift 6010073
  have htrace : WordTrace (prefixWord ++ tailWord_6010073) baseStart_6010073 baseEnd_6010073 := by
    simpa [prefixWord, tailWord_6010073, baseEnd_6010073] using wordTrace_append hprefix tailTrace_6010073
  have hstable : (prefixWord ++ tailWord_6010073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010073).length < 2 ^ (prefixWord ++ tailWord_6010073).sum := by decide
  have hdescent : baseEnd_6010073 < baseStart_6010073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010087 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6010087 : Nat := 118140960795 + 6010087 * 2 ^ 59
def prefixEnd_6010087 : Nat := 4983230072969 + 3 ^ 40 * 6010087 * 2
def baseEnd_6010087 : Nat := 3086063406338532240672619

theorem tailTrace_6010087 : CollatzResearch.WordTrace tailWord_6010087 prefixEnd_6010087 3086063406338532240672619 := by
  unfold tailWord_6010087
  simp only [CollatzResearch.WordTrace]
  refine ⟨219205881377488714985556515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146137254251659143323704343 219205881377488714985556515)
  ·
    refine ⟨328808822066233072478334773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219205881377488714985556515 328808822066233072478334773)
    ·
      refine ⟨30825827068709350544843885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328808822066233072478334773 30825827068709350544843885)
      ·
        refine ⟨11559685150766006454316457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30825827068709350544843885 11559685150766006454316457)
        ·
          refine ⟨8669763863074504840737343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11559685150766006454316457 8669763863074504840737343)
          ·
            refine ⟨13004645794611757261106015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669763863074504840737343 13004645794611757261106015)
            ·
              refine ⟨19506968691917635891659023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13004645794611757261106015 19506968691917635891659023)
              ·
                refine ⟨29260453037876453837488535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19506968691917635891659023 29260453037876453837488535)
                ·
                  refine ⟨43890679556814680756232803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29260453037876453837488535 43890679556814680756232803)
                  ·
                    refine ⟨65836019335222021134349205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43890679556814680756232803 65836019335222021134349205)
                    ·
                      refine ⟨3086063406338532240672619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65836019335222021134349205 3086063406338532240672619)
                      ·
                        rfl

theorem cell23_6010087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6010087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010087 prefixEnd_6010087 := by exact prefixLift 6010087
  have htrace : WordTrace (prefixWord ++ tailWord_6010087) baseStart_6010087 baseEnd_6010087 := by
    simpa [prefixWord, tailWord_6010087, baseEnd_6010087] using wordTrace_append hprefix tailTrace_6010087
  have hstable : (prefixWord ++ tailWord_6010087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010087).length < 2 ^ (prefixWord ++ tailWord_6010087).sum := by decide
  have hdescent : baseEnd_6010087 < baseStart_6010087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010114 : List Nat := [3, 4, 1, 1, 4, 1, 9]
def baseStart_6010114 : Nat := 118140960795 + 6010114 * 2 ^ 59
def prefixEnd_6010114 : Nat := 4983230072969 + 3 ^ 40 * 6010114 * 2
def baseEnd_6010114 : Nat := 38099719386619797963395

theorem tailTrace_6010114 : CollatzResearch.WordTrace tailWord_6010114 prefixEnd_6010114 38099719386619797963395 := by
  unfold tailWord_6010114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54801716537097724649197349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146137910765593932397859597 54801716537097724649197349)
  ·
    refine ⟨10275321850705823371724503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54801716537097724649197349 10275321850705823371724503)
    ·
      refine ⟨15412982776058735057586755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10275321850705823371724503 15412982776058735057586755)
      ·
        refine ⟨23119474164088102586380133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15412982776058735057586755 23119474164088102586380133)
        ·
          refine ⟨4334901405766519234946275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23119474164088102586380133 4334901405766519234946275)
          ·
            refine ⟨6502352108649778852419413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334901405766519234946275 6502352108649778852419413)
            ·
              refine ⟨38099719386619797963395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6502352108649778852419413 38099719386619797963395)
              ·
                rfl

theorem cell23_6010114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 9].length) (baseStart_6010114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010114 prefixEnd_6010114 := by exact prefixLift 6010114
  have htrace : WordTrace (prefixWord ++ tailWord_6010114) baseStart_6010114 baseEnd_6010114 := by
    simpa [prefixWord, tailWord_6010114, baseEnd_6010114] using wordTrace_append hprefix tailTrace_6010114
  have hstable : (prefixWord ++ tailWord_6010114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010114).length < 2 ^ (prefixWord ++ tailWord_6010114).sum := by decide
  have hdescent : baseEnd_6010114 < baseStart_6010114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010140 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6010140 : Nat := 118140960795 + 6010140 * 2 ^ 59
def prefixEnd_6010140 : Nat := 4983230072969 + 3 ^ 40 * 6010140 * 2
def baseEnd_6010140 : Nat := 1028696873604406844436625

theorem tailTrace_6010140 : CollatzResearch.WordTrace tailWord_6010140 prefixEnd_6010140 1028696873604406844436625 := by
  unfold tailWord_6010140
  simp only [CollatzResearch.WordTrace]
  refine ⟨109603907223148352518617937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146138542964197803358157249 109603907223148352518617937)
  ·
    refine ⟨82202930417361264388963453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109603907223148352518617937 82202930417361264388963453)
    ·
      refine ⟨30826098906510474145861295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82202930417361264388963453 30826098906510474145861295)
      ·
        refine ⟨46239148359765711218791943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30826098906510474145861295 46239148359765711218791943)
        ·
          refine ⟨69358722539648566828187915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46239148359765711218791943 69358722539648566828187915)
          ·
            refine ⟨104038083809472850242281873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69358722539648566828187915 104038083809472850242281873)
            ·
              refine ⟨78028562857104637681711405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104038083809472850242281873 78028562857104637681711405)
              ·
                refine ⟨29260711071414239130641777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78028562857104637681711405 29260711071414239130641777)
                ·
                  refine ⟨21945533303560679347981333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29260711071414239130641777 21945533303560679347981333)
                  ·
                    refine ⟨1028696873604406844436625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21945533303560679347981333 1028696873604406844436625)
                    ·
                      rfl

theorem cell23_6010140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6010140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010140 prefixEnd_6010140 := by exact prefixLift 6010140
  have htrace : WordTrace (prefixWord ++ tailWord_6010140) baseStart_6010140 baseEnd_6010140 := by
    simpa [prefixWord, tailWord_6010140, baseEnd_6010140] using wordTrace_append hprefix tailTrace_6010140
  have hstable : (prefixWord ++ tailWord_6010140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010140).length < 2 ^ (prefixWord ++ tailWord_6010140).sum := by decide
  have hdescent : baseEnd_6010140 < baseStart_6010140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010141 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6010141 : Nat := 118140960795 + 6010141 * 2 ^ 59
def prefixEnd_6010141 : Nat := 4983230072969 + 3 ^ 40 * 6010141 * 2
def baseEnd_6010141 : Nat := 3086091134293875029397371

theorem tailTrace_6010141 : CollatzResearch.WordTrace tailWord_6010141 prefixEnd_6010141 3086091134293875029397371 := by
  unfold tailWord_6010141
  simp only [CollatzResearch.WordTrace]
  refine ⟨219207850919293082208022277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146138567279528721472014851 219207850919293082208022277)
  ·
    refine ⟨41101472047367452914004177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219207850919293082208022277 41101472047367452914004177)
    ·
      refine ⟨30826104035525589685503133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41101472047367452914004177 30826104035525589685503133)
      ·
        refine ⟨11559789013322096132063675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30826104035525589685503133 11559789013322096132063675)
        ·
          refine ⟨17339683519983144198095513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11559789013322096132063675 17339683519983144198095513)
          ·
            refine ⟨13004762639987358148571635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17339683519983144198095513 13004762639987358148571635)
            ·
              refine ⟨19507143959981037222857453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13004762639987358148571635 19507143959981037222857453)
              ·
                refine ⟨7315178984992888958571545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19507143959981037222857453 7315178984992888958571545)
                ·
                  refine ⟨5486384238744666718928659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7315178984992888958571545 5486384238744666718928659)
                  ·
                    refine ⟨8229576358117000078392989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486384238744666718928659 8229576358117000078392989)
                    ·
                      refine ⟨3086091134293875029397371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229576358117000078392989 3086091134293875029397371)
                      ·
                        rfl

theorem cell23_6010141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6010141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010141 prefixEnd_6010141 := by exact prefixLift 6010141
  have htrace : WordTrace (prefixWord ++ tailWord_6010141) baseStart_6010141 baseEnd_6010141 := by
    simpa [prefixWord, tailWord_6010141, baseEnd_6010141] using wordTrace_append hprefix tailTrace_6010141
  have hstable : (prefixWord ++ tailWord_6010141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010141).length < 2 ^ (prefixWord ++ tailWord_6010141).sum := by decide
  have hdescent : baseEnd_6010141 < baseStart_6010141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010197 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_6010197 : Nat := 118140960795 + 6010197 * 2 ^ 59
def prefixEnd_6010197 : Nat := 4983230072969 + 3 ^ 40 * 6010197 * 2
def baseEnd_6010197 : Nat := 3086119889210526810297113

theorem tailTrace_6010197 : CollatzResearch.WordTrace tailWord_6010197 prefixEnd_6010197 3086119889210526810297113 := by
  unfold tailWord_6010197
  simp only [CollatzResearch.WordTrace]
  refine ⟨219209893407090203772060845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146139928938060135848040563 219209893407090203772060845)
  ·
    refine ⟨82203710027658826414522817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219209893407090203772060845 82203710027658826414522817)
    ·
      refine ⟨61652782520744119810892113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82203710027658826414522817 61652782520744119810892113)
      ·
        refine ⟨46239586890558089858169085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61652782520744119810892113 46239586890558089858169085)
        ·
          refine ⟨17339845083959283696813407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46239586890558089858169085 17339845083959283696813407)
          ·
            refine ⟨26009767625938925545220111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339845083959283696813407 26009767625938925545220111)
            ·
              refine ⟨39014651438908388317830167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26009767625938925545220111 39014651438908388317830167)
              ·
                refine ⟨58521977158362582476745251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39014651438908388317830167 58521977158362582476745251)
                ·
                  refine ⟨87782965737543873715117877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58521977158362582476745251 87782965737543873715117877)
                  ·
                    refine ⟨8229653037894738160792301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87782965737543873715117877 8229653037894738160792301)
                    ·
                      refine ⟨3086119889210526810297113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229653037894738160792301 3086119889210526810297113)
                      ·
                        rfl

theorem cell23_6010197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_6010197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010197 prefixEnd_6010197 := by exact prefixLift 6010197
  have htrace : WordTrace (prefixWord ++ tailWord_6010197) baseStart_6010197 baseEnd_6010197 := by
    simpa [prefixWord, tailWord_6010197, baseEnd_6010197] using wordTrace_append hprefix tailTrace_6010197
  have hstable : (prefixWord ++ tailWord_6010197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010197).length < 2 ^ (prefixWord ++ tailWord_6010197).sum := by decide
  have hdescent : baseEnd_6010197 < baseStart_6010197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010200 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_6010200 : Nat := 118140960795 + 6010200 * 2 ^ 59
def prefixEnd_6010200 : Nat := 4983230072969 + 3 ^ 40 * 6010200 * 2
def baseEnd_6010200 : Nat := 1028707143217496766186533

theorem tailTrace_6010200 : CollatzResearch.WordTrace tailWord_6010200 prefixEnd_6010200 1028707143217496766186533 := by
  unfold tailWord_6010200
  simp only [CollatzResearch.WordTrace]
  refine ⟨109605001413039667642210027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146140001884052890189613369 109605001413039667642210027)
  ·
    refine ⟨164407502119559501463315041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109605001413039667642210027 164407502119559501463315041)
    ·
      refine ⟨123305626589669626097486281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164407502119559501463315041 123305626589669626097486281)
      ·
        refine ⟨92479219942252219573114711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123305626589669626097486281 92479219942252219573114711)
        ·
          refine ⟨138718829913378329359672067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92479219942252219573114711 138718829913378329359672067)
          ·
            refine ⟨208078244870067494039508101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138718829913378329359672067 208078244870067494039508101)
            ·
              refine ⟨39014670913137655132407769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208078244870067494039508101 39014670913137655132407769)
              ·
                refine ⟨29261003184853241349305827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39014670913137655132407769 29261003184853241349305827)
                ·
                  refine ⟨43891504777279862023958741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29261003184853241349305827 43891504777279862023958741)
                  ·
                    refine ⟨1028707143217496766186533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43891504777279862023958741 1028707143217496766186533)
                    ·
                      rfl

theorem cell23_6010200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_6010200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010200 prefixEnd_6010200 := by exact prefixLift 6010200
  have htrace : WordTrace (prefixWord ++ tailWord_6010200) baseStart_6010200 baseEnd_6010200 := by
    simpa [prefixWord, tailWord_6010200, baseEnd_6010200] using wordTrace_append hprefix tailTrace_6010200
  have hstable : (prefixWord ++ tailWord_6010200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010200).length < 2 ^ (prefixWord ++ tailWord_6010200).sum := by decide
  have hdescent : baseEnd_6010200 < baseStart_6010200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010207 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 5, 2]
def baseStart_6010207 : Nat := 118140960795 + 6010207 * 2 ^ 59
def prefixEnd_6010207 : Nat := 4983230072969 + 3 ^ 40 * 6010207 * 2
def baseEnd_6010207 : Nat := 3086125024017071771172067

theorem tailTrace_6010207 : CollatzResearch.WordTrace tailWord_6010207 prefixEnd_6010207 3086125024017071771172067 := by
  unfold tailWord_6010207
  simp only [CollatzResearch.WordTrace]
  refine ⟨219210258137053975479924875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146140172091369316986616583 219210258137053975479924875)
  ·
    refine ⟨328815387205580963219887313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219210258137053975479924875 328815387205580963219887313)
    ·
      refine ⟨246611540404185722414915485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328815387205580963219887313 246611540404185722414915485)
      ·
        refine ⟨92479327651569645905593307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246611540404185722414915485 92479327651569645905593307)
        ·
          refine ⟨138718991477354468858389961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92479327651569645905593307 138718991477354468858389961)
          ·
            refine ⟨104039243608015851643792471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138718991477354468858389961 104039243608015851643792471)
            ·
              refine ⟨156058865412023777465688707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104039243608015851643792471 156058865412023777465688707)
              ·
                refine ⟨234088298118035666198533061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156058865412023777465688707 234088298118035666198533061)
                ·
                  refine ⟨43891555897131687412224949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234088298118035666198533061 43891555897131687412224949)
                  ·
                    refine ⟨4114833365356095694896089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43891555897131687412224949 4114833365356095694896089)
                    ·
                      refine ⟨3086125024017071771172067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114833365356095694896089 3086125024017071771172067)
                      ·
                        rfl

theorem cell23_6010207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_6010207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010207 prefixEnd_6010207 := by exact prefixLift 6010207
  have htrace : WordTrace (prefixWord ++ tailWord_6010207) baseStart_6010207 baseEnd_6010207 := by
    simpa [prefixWord, tailWord_6010207, baseEnd_6010207] using wordTrace_append hprefix tailTrace_6010207
  have hstable : (prefixWord ++ tailWord_6010207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010207).length < 2 ^ (prefixWord ++ tailWord_6010207).sum := by decide
  have hdescent : baseEnd_6010207 < baseStart_6010207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010237 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_6010237 : Nat := 118140960795 + 6010237 * 2 ^ 59
def prefixEnd_6010237 : Nat := 4983230072969 + 3 ^ 40 * 6010237 * 2
def baseEnd_6010237 : Nat := 3086140428436706653796929

theorem tailTrace_6010237 : CollatzResearch.WordTrace tailWord_6010237 prefixEnd_6010237 3086140428436706653796929 := by
  unfold tailWord_6010237
  simp only [CollatzResearch.WordTrace]
  refine ⟨219211352326945290603516965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146140901551296860402344643 219211352326945290603516965)
  ·
    refine ⟨41102128561302241988159431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219211352326945290603516965 41102128561302241988159431)
    ·
      refine ⟨61653192841953362982239147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41102128561302241988159431 61653192841953362982239147)
      ·
        refine ⟨92479789262930044473358721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61653192841953362982239147 92479789262930044473358721)
        ·
          refine ⟨69359841947197533355019041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92479789262930044473358721 69359841947197533355019041)
          ·
            refine ⟨52019881460398150016264281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69359841947197533355019041 52019881460398150016264281)
            ·
              refine ⟨39014911095298612512198211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52019881460398150016264281 39014911095298612512198211)
              ·
                refine ⟨58522366642947918768297317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39014911095298612512198211 58522366642947918768297317)
                ·
                  refine ⟨10972943745552734769055747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58522366642947918768297317 10972943745552734769055747)
                  ·
                    refine ⟨16459415618329102153583621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10972943745552734769055747 16459415618329102153583621)
                    ·
                      refine ⟨3086140428436706653796929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16459415618329102153583621 3086140428436706653796929)
                      ·
                        rfl

theorem cell23_6010237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_6010237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010237 prefixEnd_6010237 := by exact prefixLift 6010237
  have htrace : WordTrace (prefixWord ++ tailWord_6010237) baseStart_6010237 baseEnd_6010237 := by
    simpa [prefixWord, tailWord_6010237, baseEnd_6010237] using wordTrace_append hprefix tailTrace_6010237
  have hstable : (prefixWord ++ tailWord_6010237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010237).length < 2 ^ (prefixWord ++ tailWord_6010237).sum := by decide
  have hdescent : baseEnd_6010237 < baseStart_6010237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010240 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_6010240 : Nat := 118140960795 + 6010240 * 2 ^ 59
def prefixEnd_6010240 : Nat := 4983230072969 + 3 ^ 40 * 6010240 * 2
def baseEnd_6010240 : Nat := 3086141968878670142059415

theorem tailTrace_6010240 : CollatzResearch.WordTrace tailWord_6010240 prefixEnd_6010240 3086141968878670142059415 := by
  unfold tailWord_6010240
  simp only [CollatzResearch.WordTrace]
  refine ⟨109605730872967211057938087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146140974497289614743917449 109605730872967211057938087)
  ·
    refine ⟨164408596309450816586907131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109605730872967211057938087 164408596309450816586907131)
    ·
      refine ⟨246612894464176224880360697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164408596309450816586907131 246612894464176224880360697)
      ·
        refine ⟨184959670848132168660270523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246612894464176224880360697 184959670848132168660270523)
        ·
          refine ⟨277439506272198252990405785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184959670848132168660270523 277439506272198252990405785)
          ·
            refine ⟨208079629704148689742804339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277439506272198252990405785 208079629704148689742804339)
            ·
              refine ⟨312119444556223034614206509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208079629704148689742804339 312119444556223034614206509)
              ·
                refine ⟨117044791708583637980327441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312119444556223034614206509 117044791708583637980327441)
                ·
                  refine ⟨87783593781437728485245581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117044791708583637980327441 87783593781437728485245581)
                  ·
                    refine ⟨32918847668039148181967093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87783593781437728485245581 32918847668039148181967093)
                    ·
                      refine ⟨3086141968878670142059415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32918847668039148181967093 3086141968878670142059415)
                      ·
                        rfl

theorem cell23_6010240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_6010240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010240 prefixEnd_6010240 := by exact prefixLift 6010240
  have htrace : WordTrace (prefixWord ++ tailWord_6010240) baseStart_6010240 baseEnd_6010240 := by
    simpa [prefixWord, tailWord_6010240, baseEnd_6010240] using wordTrace_append hprefix tailTrace_6010240
  have hstable : (prefixWord ++ tailWord_6010240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010240).length < 2 ^ (prefixWord ++ tailWord_6010240).sum := by decide
  have hdescent : baseEnd_6010240 < baseStart_6010240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010257 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_6010257 : Nat := 118140960795 + 6010257 * 2 ^ 59
def prefixEnd_6010257 : Nat := 4983230072969 + 3 ^ 40 * 6010257 * 2
def baseEnd_6010257 : Nat := 3086150698049796575546837

theorem tailTrace_6010257 : CollatzResearch.WordTrace tailWord_6010257 prefixEnd_6010257 3086150698049796575546837 := by
  unfold tailWord_6010257
  simp only [CollatzResearch.WordTrace]
  refine ⟨219212081786872834019245025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146141387857915222679496683 219212081786872834019245025)
  ·
    refine ⟨164409061340154625514433769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219212081786872834019245025 164409061340154625514433769)
    ·
      refine ⟨123306796005115969135825327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164409061340154625514433769 123306796005115969135825327)
      ·
        refine ⟨184960194007673953703737991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123306796005115969135825327 184960194007673953703737991)
        ·
          refine ⟨277440291011510930555606987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184960194007673953703737991 277440291011510930555606987)
          ·
            refine ⟨416160436517266395833410481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277440291011510930555606987 416160436517266395833410481)
            ·
              refine ⟨312120327387949796875057861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416160436517266395833410481 312120327387949796875057861)
              ·
                refine ⟨58522561385240586914073349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312120327387949796875057861 58522561385240586914073349)
                ·
                  refine ⟨10972980259732610046388753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58522561385240586914073349 10972980259732610046388753)
                  ·
                    refine ⟨8229735194799457534791565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10972980259732610046388753 8229735194799457534791565)
                    ·
                      refine ⟨3086150698049796575546837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229735194799457534791565 3086150698049796575546837)
                      ·
                        rfl

theorem cell23_6010257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_6010257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010257 prefixEnd_6010257 := by exact prefixLift 6010257
  have htrace : WordTrace (prefixWord ++ tailWord_6010257) baseStart_6010257 baseEnd_6010257 := by
    simpa [prefixWord, tailWord_6010257, baseEnd_6010257] using wordTrace_append hprefix tailTrace_6010257
  have hstable : (prefixWord ++ tailWord_6010257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010257).length < 2 ^ (prefixWord ++ tailWord_6010257).sum := by decide
  have hdescent : baseEnd_6010257 < baseStart_6010257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010274 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_6010274 : Nat := 118140960795 + 6010274 * 2 ^ 59
def prefixEnd_6010274 : Nat := 4983230072969 + 3 ^ 40 * 6010274 * 2
def baseEnd_6010274 : Nat := 3086159427220923009034259

theorem tailTrace_6010274 : CollatzResearch.WordTrace tailWord_6010274 prefixEnd_6010274 3086159427220923009034259 := by
  unfold tailWord_6010274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54803175456952811480653469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146141801218540830615075917 54803175456952811480653469)
  ·
    refine ⟨20551190796357304305245051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54803175456952811480653469 20551190796357304305245051)
    ·
      refine ⟨30826786194535956457867577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20551190796357304305245051 30826786194535956457867577)
      ·
        refine ⟨23120089645901967343400683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30826786194535956457867577 23120089645901967343400683)
        ·
          refine ⟨34680134468852951015101025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23120089645901967343400683 34680134468852951015101025)
          ·
            refine ⟨26010100851639713261325769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34680134468852951015101025 26010100851639713261325769)
            ·
              refine ⟨19507575638729784945994327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26010100851639713261325769 19507575638729784945994327)
              ·
                refine ⟨29261363458094677418991491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19507575638729784945994327 29261363458094677418991491)
                ·
                  refine ⟨43892045187142016128487237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29261363458094677418991491 43892045187142016128487237)
                  ·
                    refine ⟨8229758472589128024091357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43892045187142016128487237 8229758472589128024091357)
                    ·
                      refine ⟨3086159427220923009034259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229758472589128024091357 3086159427220923009034259)
                      ·
                        rfl

theorem cell23_6010274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_6010274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010274 prefixEnd_6010274 := by exact prefixLift 6010274
  have htrace : WordTrace (prefixWord ++ tailWord_6010274) baseStart_6010274 baseEnd_6010274 := by
    simpa [prefixWord, tailWord_6010274, baseEnd_6010274] using wordTrace_append hprefix tailTrace_6010274
  have hstable : (prefixWord ++ tailWord_6010274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010274).length < 2 ^ (prefixWord ++ tailWord_6010274).sum := by decide
  have hdescent : baseEnd_6010274 < baseStart_6010274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010337 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_6010337 : Nat := 118140960795 + 6010337 * 2 ^ 59
def prefixEnd_6010337 : Nat := 4983230072969 + 3 ^ 40 * 6010337 * 2
def baseEnd_6010337 : Nat := 1028730592167385420848823

theorem tailTrace_6010337 : CollatzResearch.WordTrace tailWord_6010337 prefixEnd_6010337 1028730592167385420848823 := by
  unfold tailWord_6010337
  simp only [CollatzResearch.WordTrace]
  refine ⟨219214999626583007682157265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146143333084388671788104843 219214999626583007682157265)
  ·
    refine ⟨164411249719937255761617949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219214999626583007682157265 164411249719937255761617949)
    ·
      refine ⟨61654218644976470910606731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164411249719937255761617949 61654218644976470910606731)
      ·
        refine ⟨92481327967464706365910097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61654218644976470910606731 92481327967464706365910097)
        ·
          refine ⟨69360995975598529774432573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92481327967464706365910097 69360995975598529774432573)
          ·
            refine ⟨26010373490849448665412215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69360995975598529774432573 26010373490849448665412215)
            ·
              refine ⟨39015560236274172998118323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26010373490849448665412215 39015560236274172998118323)
              ·
                refine ⟨58523340354411259497177485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39015560236274172998118323 58523340354411259497177485)
                ·
                  refine ⟨21946252632904222311441557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58523340354411259497177485 21946252632904222311441557)
                  ·
                    refine ⟨1028730592167385420848823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21946252632904222311441557 1028730592167385420848823)
                    ·
                      rfl

theorem cell23_6010337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_6010337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010337 prefixEnd_6010337 := by exact prefixLift 6010337
  have htrace : WordTrace (prefixWord ++ tailWord_6010337) baseStart_6010337 baseEnd_6010337 := by
    simpa [prefixWord, tailWord_6010337, baseEnd_6010337] using wordTrace_append hprefix tailTrace_6010337
  have hstable : (prefixWord ++ tailWord_6010337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010337).length < 2 ^ (prefixWord ++ tailWord_6010337).sum := by decide
  have hdescent : baseEnd_6010337 < baseStart_6010337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010347 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5]
def baseStart_6010347 : Nat := 118140960795 + 6010347 * 2 ^ 59
def prefixEnd_6010347 : Nat := 4983230072969 + 3 ^ 40 * 6010347 * 2
def baseEnd_6010347 : Nat := 3086196911308701223421423

theorem tailTrace_6010347 : CollatzResearch.WordTrace tailWord_6010347 prefixEnd_6010347 3086196911308701223421423 := by
  unfold tailWord_6010347
  simp only [CollatzResearch.WordTrace]
  refine ⟨219215364356546779390021295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146143576237697852926680863 219215364356546779390021295)
  ·
    refine ⟨328823046534820169085031943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219215364356546779390021295 328823046534820169085031943)
    ·
      refine ⟨493234569802230253627547915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328823046534820169085031943 493234569802230253627547915)
      ·
        refine ⟨739851854703345380441321873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493234569802230253627547915 739851854703345380441321873)
        ·
          refine ⟨554888891027509035330991405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739851854703345380441321873 554888891027509035330991405)
          ·
            refine ⟨208083334135315888249121777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554888891027509035330991405 208083334135315888249121777)
            ·
              refine ⟨156062500601486916186841333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208083334135315888249121777 156062500601486916186841333)
              ·
                refine ⟨14630859431389398392516375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156062500601486916186841333 14630859431389398392516375)
                ·
                  refine ⟨21946289147084097588774563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14630859431389398392516375 21946289147084097588774563)
                  ·
                    refine ⟨32919433720626146383161845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21946289147084097588774563 32919433720626146383161845)
                    ·
                      refine ⟨3086196911308701223421423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32919433720626146383161845 3086196911308701223421423)
                      ·
                        rfl

theorem cell23_6010347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_6010347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010347 prefixEnd_6010347 := by exact prefixLift 6010347
  have htrace : WordTrace (prefixWord ++ tailWord_6010347) baseStart_6010347 baseEnd_6010347 := by
    simpa [prefixWord, tailWord_6010347, baseEnd_6010347] using wordTrace_append hprefix tailTrace_6010347
  have hstable : (prefixWord ++ tailWord_6010347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010347).length < 2 ^ (prefixWord ++ tailWord_6010347).sum := by decide
  have hdescent : baseEnd_6010347 < baseStart_6010347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010361 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 3, 2, 2]
def baseStart_6010361 : Nat := 118140960795 + 6010361 * 2 ^ 59
def prefixEnd_6010361 : Nat := 4983230072969 + 3 ^ 40 * 6010361 * 2
def baseEnd_6010361 : Nat := 3086204100037864168646359

theorem tailTrace_6010361 : CollatzResearch.WordTrace tailWord_6010361 prefixEnd_6010361 3086204100037864168646359 := by
  unfold tailWord_6010361
  simp only [CollatzResearch.WordTrace]
  refine ⟨219215874978496059781030937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146143916652330706520687291 219215874978496059781030937)
  ·
    refine ⟨164411906233872044835773203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219215874978496059781030937 164411906233872044835773203)
    ·
      refine ⟨246617859350808067253659805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164411906233872044835773203 246617859350808067253659805)
      ·
        refine ⟨92481697256553025220122427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246617859350808067253659805 92481697256553025220122427)
        ·
          refine ⟨138722545884829537830183641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92481697256553025220122427 138722545884829537830183641)
          ·
            refine ⟨104041909413622153372637731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138722545884829537830183641 104041909413622153372637731)
            ·
              refine ⟨156062864120433230058956597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104041909413622153372637731 156062864120433230058956597)
              ·
                refine ⟨14630893511290615318027181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156062864120433230058956597 14630893511290615318027181)
                ·
                  refine ⟨5486585066733980744260193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14630893511290615318027181 5486585066733980744260193)
                  ·
                    refine ⟨4114938800050485558195145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5486585066733980744260193 4114938800050485558195145)
                    ·
                      refine ⟨3086204100037864168646359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114938800050485558195145 3086204100037864168646359)
                      ·
                        rfl

theorem cell23_6010361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_6010361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010361 prefixEnd_6010361 := by exact prefixLift 6010361
  have htrace : WordTrace (prefixWord ++ tailWord_6010361) baseStart_6010361 baseEnd_6010361 := by
    simpa [prefixWord, tailWord_6010361, baseEnd_6010361] using wordTrace_append hprefix tailTrace_6010361
  have hstable : (prefixWord ++ tailWord_6010361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010361).length < 2 ^ (prefixWord ++ tailWord_6010361).sum := by decide
  have hdescent : baseEnd_6010361 < baseStart_6010361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010364 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_6010364 : Nat := 118140960795 + 6010364 * 2 ^ 59
def prefixEnd_6010364 : Nat := 4983230072969 + 3 ^ 40 * 6010364 * 2
def baseEnd_6010364 : Nat := 3086205640479827656908845

theorem tailTrace_6010364 : CollatzResearch.WordTrace tailWord_6010364 prefixEnd_6010364 3086205640479827656908845 := by
  unfold tailWord_6010364
  simp only [CollatzResearch.WordTrace]
  refine ⟨109607992198742595646695073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146143989598323460862260097 109607992198742595646695073)
  ·
    refine ⟨82205994149056946735021305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109607992198742595646695073 82205994149056946735021305)
    ·
      refine ⟨61654495611792710051265979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82205994149056946735021305 61654495611792710051265979)
      ·
        refine ⟨92481743417689065076898969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61654495611792710051265979 92481743417689065076898969)
        ·
          refine ⟨69361307563266798807674227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92481743417689065076898969 69361307563266798807674227)
          ·
            refine ⟨104041961344900198211511341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69361307563266798807674227 104041961344900198211511341)
            ·
              refine ⟨39015735504337574329316753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104041961344900198211511341 39015735504337574329316753)
              ·
                refine ⟨29261801628253180746987565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39015735504337574329316753 29261801628253180746987565)
                ·
                  refine ⟨10973175610594942780120337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29261801628253180746987565 10973175610594942780120337)
                  ·
                    refine ⟨8229881707946207085090253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10973175610594942780120337 8229881707946207085090253)
                    ·
                      refine ⟨3086205640479827656908845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229881707946207085090253 3086205640479827656908845)
                      ·
                        rfl

theorem cell23_6010364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_6010364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010364 prefixEnd_6010364 := by exact prefixLift 6010364
  have htrace : WordTrace (prefixWord ++ tailWord_6010364) baseStart_6010364 baseEnd_6010364 := by
    simpa [prefixWord, tailWord_6010364, baseEnd_6010364] using wordTrace_append hprefix tailTrace_6010364
  have hstable : (prefixWord ++ tailWord_6010364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010364).length < 2 ^ (prefixWord ++ tailWord_6010364).sum := by decide
  have hdescent : baseEnd_6010364 < baseStart_6010364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010378 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_6010378 : Nat := 118140960795 + 6010378 * 2 ^ 59
def prefixEnd_6010378 : Nat := 4983230072969 + 3 ^ 40 * 6010378 * 2
def baseEnd_6010378 : Nat := 3086212829208990602133781

theorem tailTrace_6010378 : CollatzResearch.WordTrace tailWord_6010378 prefixEnd_6010378 3086212829208990602133781 := by
  unfold tailWord_6010378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54804123754858617921099947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146144330012956314456266525 54804123754858617921099947)
  ·
    refine ⟨82206185632287926881649921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54804123754858617921099947 82206185632287926881649921)
    ·
      refine ⟨61654639224215945161237441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82206185632287926881649921 61654639224215945161237441)
      ·
        refine ⟨46240979418161958870928081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61654639224215945161237441 46240979418161958870928081)
        ·
          refine ⟨34680734563621469153196061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46240979418161958870928081 34680734563621469153196061)
          ·
            refine ⟨13005275461358050932448523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34680734563621469153196061 13005275461358050932448523)
            ·
              refine ⟨19507913192037076398672785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13005275461358050932448523 19507913192037076398672785)
              ·
                refine ⟨14630934894027807299004589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19507913192037076398672785 14630934894027807299004589)
                ·
                  refine ⟨5486600585260427737126721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14630934894027807299004589 5486600585260427737126721)
                  ·
                    refine ⟨4114950438945320802845041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5486600585260427737126721 4114950438945320802845041)
                    ·
                      refine ⟨3086212829208990602133781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4114950438945320802845041 3086212829208990602133781)
                      ·
                        rfl

theorem cell23_6010378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_6010378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010378 prefixEnd_6010378 := by exact prefixLift 6010378
  have htrace : WordTrace (prefixWord ++ tailWord_6010378) baseStart_6010378 baseEnd_6010378 := by
    simpa [prefixWord, tailWord_6010378, baseEnd_6010378] using wordTrace_append hprefix tailTrace_6010378
  have hstable : (prefixWord ++ tailWord_6010378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010378).length < 2 ^ (prefixWord ++ tailWord_6010378).sum := by decide
  have hdescent : baseEnd_6010378 < baseStart_6010378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010428 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_6010428 : Nat := 118140960795 + 6010428 * 2 ^ 59
def prefixEnd_6010428 : Nat := 4983230072969 + 3 ^ 40 * 6010428 * 2
def baseEnd_6010428 : Nat := 3086238503241715406508551

theorem tailTrace_6010428 : CollatzResearch.WordTrace tailWord_6010428 prefixEnd_6010428 3086238503241715406508551 := by
  unfold tailWord_6010428
  simp only [CollatzResearch.WordTrace]
  refine ⟨109609159334626665111859969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146145545779502220149146625 109609159334626665111859969)
  ·
    refine ⟨82206869500969998833894977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109609159334626665111859969 82206869500969998833894977)
    ·
      refine ⟨61655152125727499125421233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82206869500969998833894977 61655152125727499125421233)
      ·
        refine ⟨46241364094295624344065925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61655152125727499125421233 46241364094295624344065925)
        ·
          refine ⟨8670255767680429564512361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46241364094295624344065925 8670255767680429564512361)
          ·
            refine ⟨6502691825760322173384271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8670255767680429564512361 6502691825760322173384271)
            ·
              refine ⟨9754037738640483260076407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502691825760322173384271 9754037738640483260076407)
              ·
                refine ⟨14631056607960724890114611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754037738640483260076407 14631056607960724890114611)
                ·
                  refine ⟨21946584911941087335171917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14631056607960724890114611 21946584911941087335171917)
                  ·
                    refine ⟨8229969341977907750689469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21946584911941087335171917 8229969341977907750689469)
                    ·
                      refine ⟨3086238503241715406508551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8229969341977907750689469 3086238503241715406508551)
                      ·
                        rfl

theorem cell23_6010428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_6010428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010428 prefixEnd_6010428 := by exact prefixLift 6010428
  have htrace : WordTrace (prefixWord ++ tailWord_6010428) baseStart_6010428 baseEnd_6010428 := by
    simpa [prefixWord, tailWord_6010428, baseEnd_6010428] using wordTrace_append hprefix tailTrace_6010428
  have hstable : (prefixWord ++ tailWord_6010428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010428).length < 2 ^ (prefixWord ++ tailWord_6010428).sum := by decide
  have hdescent : baseEnd_6010428 < baseStart_6010428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010457 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 9]
def baseStart_6010457 : Nat := 118140960795 + 6010457 * 2 ^ 59
def prefixEnd_6010457 : Nat := 4983230072969 + 3 ^ 40 * 6010457 * 2
def baseEnd_6010457 : Nat := 342917043797855088116213

theorem tailTrace_6010457 : CollatzResearch.WordTrace tailWord_6010457 prefixEnd_6010457 342917043797855088116213 := by
  unfold tailWord_6010457
  simp only [CollatzResearch.WordTrace]
  refine ⟨219219376386148268176525625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146146250924098845451017083 219219376386148268176525625)
  ·
    refine ⟨164414532289611201132394219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219219376386148268176525625 164414532289611201132394219)
    ·
      refine ⟨246621798434416801698591329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164414532289611201132394219 246621798434416801698591329)
      ·
        refine ⟨184966348825812601273943497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246621798434416801698591329 184966348825812601273943497)
        ·
          refine ⟨138724761619359450955457623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184966348825812601273943497 138724761619359450955457623)
          ·
            refine ⟨208087142429039176433186435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138724761619359450955457623 208087142429039176433186435)
            ·
              refine ⟨312130713643558764649779653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208087142429039176433186435 312130713643558764649779653)
              ·
                refine ⟨58524508808167268371833685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312130713643558764649779653 58524508808167268371833685)
                ·
                  refine ⟨342917043797855088116213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58524508808167268371833685 342917043797855088116213)
                  ·
                    rfl

theorem cell23_6010457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_6010457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010457 prefixEnd_6010457 := by exact prefixLift 6010457
  have htrace : WordTrace (prefixWord ++ tailWord_6010457) baseStart_6010457 baseEnd_6010457 := by
    simpa [prefixWord, tailWord_6010457, baseEnd_6010457] using wordTrace_append hprefix tailTrace_6010457
  have hstable : (prefixWord ++ tailWord_6010457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010457).length < 2 ^ (prefixWord ++ tailWord_6010457).sum := by decide
  have hdescent : baseEnd_6010457 < baseStart_6010457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010468 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_6010468 : Nat := 118140960795 + 6010468 * 2 ^ 59
def prefixEnd_6010468 : Nat := 4983230072969 + 3 ^ 40 * 6010468 * 2
def baseEnd_6010468 : Nat := 3086259042467895250008367

theorem tailTrace_6010468 : CollatzResearch.WordTrace tailWord_6010468 prefixEnd_6010468 3086259042467895250008367 := by
  unfold tailWord_6010468
  simp only [CollatzResearch.WordTrace]
  refine ⟨109609888794554208527588029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146146518392738944703450705 109609888794554208527588029)
  ·
    refine ⟨41103708297957828197845511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109609888794554208527588029 41103708297957828197845511)
    ·
      refine ⟨61655562446936742296768267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41103708297957828197845511 61655562446936742296768267)
      ·
        refine ⟨92483343670405113445152401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61655562446936742296768267 92483343670405113445152401)
        ·
          refine ⟨69362507752803835083864301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92483343670405113445152401 69362507752803835083864301)
          ·
            refine ⟨26010940407301438156449113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69362507752803835083864301 26010940407301438156449113)
            ·
              refine ⟨19508205305476078617336835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26010940407301438156449113 19508205305476078617336835)
              ·
                refine ⟨29262307958214117926005253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19508205305476078617336835 29262307958214117926005253)
                ·
                  refine ⟨5486682742165147111125985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29262307958214117926005253 5486682742165147111125985)
                  ·
                    refine ⟨4115012056623860333344489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5486682742165147111125985 4115012056623860333344489)
                    ·
                      refine ⟨3086259042467895250008367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115012056623860333344489 3086259042467895250008367)
                      ·
                        rfl

theorem cell23_6010468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_6010468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010468 prefixEnd_6010468 := by exact prefixLift 6010468
  have htrace : WordTrace (prefixWord ++ tailWord_6010468) baseStart_6010468 baseEnd_6010468 := by
    simpa [prefixWord, tailWord_6010468, baseEnd_6010468] using wordTrace_append hprefix tailTrace_6010468
  have hstable : (prefixWord ++ tailWord_6010468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010468).length < 2 ^ (prefixWord ++ tailWord_6010468).sum := by decide
  have hdescent : baseEnd_6010468 < baseStart_6010468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010541 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6010541 : Nat := 118140960795 + 6010541 * 2 ^ 59
def prefixEnd_6010541 : Nat := 4983230072969 + 3 ^ 40 * 6010541 * 2
def baseEnd_6010541 : Nat := 3086296526555673464395531

theorem tailTrace_6010541 : CollatzResearch.WordTrace tailWord_6010541 prefixEnd_6010541 3086296526555673464395531 := by
  unfold tailWord_6010541
  simp only [CollatzResearch.WordTrace]
  refine ⟨219222440117843950522583477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146148293411895967015055651 219222440117843950522583477)
  ·
    refine ⟨20552103761047870361492201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219222440117843950522583477 20552103761047870361492201)
    ·
      refine ⟨15414077820785902771119151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20552103761047870361492201 15414077820785902771119151)
      ·
        refine ⟨23121116731178854156678727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15414077820785902771119151 23121116731178854156678727)
        ·
          refine ⟨34681675096768281235018091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23121116731178854156678727 34681675096768281235018091)
          ·
            refine ⟨52022512645152421852527137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34681675096768281235018091 52022512645152421852527137)
            ·
              refine ⟨39016884483864316389395353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52022512645152421852527137 39016884483864316389395353)
              ·
                refine ⟨29262663362898237292046515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39016884483864316389395353 29262663362898237292046515)
                ·
                  refine ⟨43893995044347355938069773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29262663362898237292046515 43893995044347355938069773)
                  ·
                    refine ⟨16460248141630258476776165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43893995044347355938069773 16460248141630258476776165)
                    ·
                      refine ⟨3086296526555673464395531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16460248141630258476776165 3086296526555673464395531)
                      ·
                        rfl

theorem cell23_6010541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6010541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010541 prefixEnd_6010541 := by exact prefixLift 6010541
  have htrace : WordTrace (prefixWord ++ tailWord_6010541) baseStart_6010541 baseEnd_6010541 := by
    simpa [prefixWord, tailWord_6010541, baseEnd_6010541] using wordTrace_append hprefix tailTrace_6010541
  have hstable : (prefixWord ++ tailWord_6010541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010541).length < 2 ^ (prefixWord ++ tailWord_6010541).sum := by decide
  have hdescent : baseEnd_6010541 < baseStart_6010541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010551 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 5, 4]
def baseStart_6010551 : Nat := 118140960795 + 6010551 * 2 ^ 59
def prefixEnd_6010551 : Nat := 4983230072969 + 3 ^ 40 * 6010551 * 2
def baseEnd_6010551 : Nat := 1028767220454072808423495

theorem tailTrace_6010551 : CollatzResearch.WordTrace tailWord_6010551 prefixEnd_6010551 1028767220454072808423495 := by
  unfold tailWord_6010551
  simp only [CollatzResearch.WordTrace]
  refine ⟨219222804847807722230447507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146148536565205148153631671 219222804847807722230447507)
  ·
    refine ⟨328834207271711583345671261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219222804847807722230447507 328834207271711583345671261)
    ·
      refine ⟨123312827726891843754626723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328834207271711583345671261 123312827726891843754626723)
      ·
        refine ⟨184969241590337765631940085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123312827726891843754626723 184969241590337765631940085)
        ·
          refine ⟨17340866399094165527994383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184969241590337765631940085 17340866399094165527994383)
          ·
            refine ⟨26011299598641248291991575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17340866399094165527994383 26011299598641248291991575)
            ·
              refine ⟨39016949397961872437987363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26011299598641248291991575 39016949397961872437987363)
              ·
                refine ⟨58525424096942808656981045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39016949397961872437987363 58525424096942808656981045)
                ·
                  refine ⟨5486758509088388311591973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58525424096942808656981045 5486758509088388311591973)
                  ·
                    refine ⟨1028767220454072808423495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5486758509088388311591973 1028767220454072808423495)
                    ·
                      rfl

theorem cell23_6010551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_6010551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010551 prefixEnd_6010551 := by exact prefixLift 6010551
  have htrace : WordTrace (prefixWord ++ tailWord_6010551) baseStart_6010551 baseEnd_6010551 := by
    simpa [prefixWord, tailWord_6010551, baseEnd_6010551] using wordTrace_append hprefix tailTrace_6010551
  have hstable : (prefixWord ++ tailWord_6010551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010551).length < 2 ^ (prefixWord ++ tailWord_6010551).sum := by decide
  have hdescent : baseEnd_6010551 < baseStart_6010551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010558 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_6010558 : Nat := 118140960795 + 6010558 * 2 ^ 59
def prefixEnd_6010558 : Nat := 4983230072969 + 3 ^ 40 * 6010558 * 2
def baseEnd_6010558 : Nat := 3086305255726799897882953

theorem tailTrace_6010558 : CollatzResearch.WordTrace tailWord_6010558 prefixEnd_6010558 3086305255726799897882953 := by
  unfold tailWord_6010558
  simp only [CollatzResearch.WordTrace]
  refine ⟨27402882519847795303244041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146148706772521574950634885 27402882519847795303244041)
  ·
    refine ⟨20552161889885846477433031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27402882519847795303244041 20552161889885846477433031)
    ·
      refine ⟨30828242834828769716149547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20552161889885846477433031 30828242834828769716149547)
      ·
        refine ⟨46242364252243154574224321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30828242834828769716149547 46242364252243154574224321)
        ·
          refine ⟨34681773189182365930668241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46242364252243154574224321 34681773189182365930668241)
          ·
            refine ⟨26011329891886774448001181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34681773189182365930668241 26011329891886774448001181)
            ·
              refine ⟨9754248709457540418000443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26011329891886774448001181 9754248709457540418000443)
              ·
                refine ⟨14631373064186310627000665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754248709457540418000443 14631373064186310627000665)
                ·
                  refine ⟨10973529798139732970250499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14631373064186310627000665 10973529798139732970250499)
                  ·
                    refine ⟨16460294697209599455375749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10973529798139732970250499 16460294697209599455375749)
                    ·
                      refine ⟨3086305255726799897882953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16460294697209599455375749 3086305255726799897882953)
                      ·
                        rfl

theorem cell23_6010558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_6010558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010558 prefixEnd_6010558 := by exact prefixLift 6010558
  have htrace : WordTrace (prefixWord ++ tailWord_6010558) baseStart_6010558 baseEnd_6010558 := by
    simpa [prefixWord, tailWord_6010558, baseEnd_6010558] using wordTrace_append hprefix tailTrace_6010558
  have hstable : (prefixWord ++ tailWord_6010558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010558).length < 2 ^ (prefixWord ++ tailWord_6010558).sum := by decide
  have hdescent : baseEnd_6010558 < baseStart_6010558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010584 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6010584 : Nat := 118140960795 + 6010584 * 2 ^ 59
def prefixEnd_6010584 : Nat := 4983230072969 + 3 ^ 40 * 6010584 * 2
def baseEnd_6010584 : Nat := 3086318606223816796157833

theorem tailTrace_6010584 : CollatzResearch.WordTrace tailWord_6010584 prefixEnd_6010584 3086318606223816796157833 := by
  unfold tailWord_6010584
  simp only [CollatzResearch.WordTrace]
  refine ⟨109612004228344084433199403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146149338971125445910932537 109612004228344084433199403)
  ·
    refine ⟨164418006342516126649799105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109612004228344084433199403 164418006342516126649799105)
    ·
      refine ⟨123313504756887094987349329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164418006342516126649799105 123313504756887094987349329)
      ·
        refine ⟨92485128567665321240511997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123313504756887094987349329 92485128567665321240511997)
        ·
          refine ⟨34681923212874495465191999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92485128567665321240511997 34681923212874495465191999)
          ·
            refine ⟨52022884819311743197787999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34681923212874495465191999 52022884819311743197787999)
            ·
              refine ⟨78034327228967614796681999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52022884819311743197787999 78034327228967614796681999)
              ·
                refine ⟨117051490843451422195022999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78034327228967614796681999 117051490843451422195022999)
                ·
                  refine ⟨175577236265177133292534499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117051490843451422195022999 175577236265177133292534499)
                  ·
                    refine ⟨263365854397765699938801749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175577236265177133292534499 263365854397765699938801749)
                    ·
                      refine ⟨3086318606223816796157833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263365854397765699938801749 3086318606223816796157833)
                      ·
                        rfl

theorem cell23_6010584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6010584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010584 prefixEnd_6010584 := by exact prefixLift 6010584
  have htrace : WordTrace (prefixWord ++ tailWord_6010584) baseStart_6010584 baseEnd_6010584 := by
    simpa [prefixWord, tailWord_6010584, baseEnd_6010584] using wordTrace_append hprefix tailTrace_6010584
  have hstable : (prefixWord ++ tailWord_6010584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010584).length < 2 ^ (prefixWord ++ tailWord_6010584).sum := by decide
  have hdescent : baseEnd_6010584 < baseStart_6010584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010604 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6010604 : Nat := 118140960795 + 6010604 * 2 ^ 59
def prefixEnd_6010604 : Nat := 4983230072969 + 3 ^ 40 * 6010604 * 2
def baseEnd_6010604 : Nat := 3086328875836906717907741

theorem tailTrace_6010604 : CollatzResearch.WordTrace tailWord_6010604 prefixEnd_6010604 3086328875836906717907741 := by
  unfold tailWord_6010604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109612368958307856141063433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146149825277743808188084577 109612368958307856141063433)
  ·
    refine ⟨82209276718730892105797575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109612368958307856141063433 82209276718730892105797575)
    ·
      refine ⟨123313915078096338158696363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82209276718730892105797575 123313915078096338158696363)
      ·
        refine ⟨184970872617144507238044545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123313915078096338158696363 184970872617144507238044545)
        ·
          refine ⟨138728154462858380428533409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184970872617144507238044545 138728154462858380428533409)
          ·
            refine ⟨104046115847143785321400057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138728154462858380428533409 104046115847143785321400057)
            ·
              refine ⟨78034586885357838991050043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104046115847143785321400057 78034586885357838991050043)
              ·
                refine ⟨117051880328036758486575065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78034586885357838991050043 117051880328036758486575065)
                ·
                  refine ⟨87788910246027568864931299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117051880328036758486575065 87788910246027568864931299)
                  ·
                    refine ⟨131683365369041353297396949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87788910246027568864931299 131683365369041353297396949)
                    ·
                      refine ⟨3086328875836906717907741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131683365369041353297396949 3086328875836906717907741)
                      ·
                        rfl

theorem cell23_6010604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6010604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010604 prefixEnd_6010604 := by exact prefixLift 6010604
  have htrace : WordTrace (prefixWord ++ tailWord_6010604) baseStart_6010604 baseEnd_6010604 := by
    simpa [prefixWord, tailWord_6010604, baseEnd_6010604] using wordTrace_append hprefix tailTrace_6010604
  have hstable : (prefixWord ++ tailWord_6010604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010604).length < 2 ^ (prefixWord ++ tailWord_6010604).sum := by decide
  have hdescent : baseEnd_6010604 < baseStart_6010604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010611 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 1, 5]
def baseStart_6010611 : Nat := 118140960795 + 6010611 * 2 ^ 59
def prefixEnd_6010611 : Nat := 4983230072969 + 3 ^ 40 * 6010611 * 2
def baseEnd_6010611 : Nat := 1028777490067162730173403

theorem tailTrace_6010611 : CollatzResearch.WordTrace tailWord_6010611 prefixEnd_6010611 1028777490067162730173403 := by
  unfold tailWord_6010611
  simp only [CollatzResearch.WordTrace]
  refine ⟨219224993227590352477631687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146149995485060234985087791 219224993227590352477631687)
  ·
    refine ⟨328837489841385528716447531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219224993227590352477631687 328837489841385528716447531)
    ·
      refine ⟨493256234762078293074671297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328837489841385528716447531 493256234762078293074671297)
      ·
        refine ⟨369942176071558719806003473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493256234762078293074671297 369942176071558719806003473)
        ·
          refine ⟨277456632053669039854502605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369942176071558719806003473 277456632053669039854502605)
          ·
            refine ⟨104046237020125889945438477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277456632053669039854502605 104046237020125889945438477)
            ·
              refine ⟨39017338882547208729539429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104046237020125889945438477 39017338882547208729539429)
              ·
                refine ⟨7315751040477601636788643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39017338882547208729539429 7315751040477601636788643)
                ·
                  refine ⟨10973626560716402455182965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315751040477601636788643 10973626560716402455182965)
                  ·
                    refine ⟨1028777490067162730173403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10973626560716402455182965 1028777490067162730173403)
                    ·
                      rfl

theorem cell23_6010611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 5].length) (baseStart_6010611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010611 prefixEnd_6010611 := by exact prefixLift 6010611
  have htrace : WordTrace (prefixWord ++ tailWord_6010611) baseStart_6010611 baseEnd_6010611 := by
    simpa [prefixWord, tailWord_6010611, baseEnd_6010611] using wordTrace_append hprefix tailTrace_6010611
  have hstable : (prefixWord ++ tailWord_6010611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010611).length < 2 ^ (prefixWord ++ tailWord_6010611).sum := by decide
  have hdescent : baseEnd_6010611 < baseStart_6010611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010618 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_6010618 : Nat := 118140960795 + 6010618 * 2 ^ 59
def prefixEnd_6010618 : Nat := 4983230072969 + 3 ^ 40 * 6010618 * 2
def baseEnd_6010618 : Nat := 3086336064566069663132677

theorem tailTrace_6010618 : CollatzResearch.WordTrace tailWord_6010618 prefixEnd_6010618 3086336064566069663132677 := by
  unfold tailWord_6010618
  simp only [CollatzResearch.WordTrace]
  refine ⟨54806312134641248168284127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146150165692376661782091005 54806312134641248168284127)
  ·
    refine ⟨82209468201961872252426191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54806312134641248168284127 82209468201961872252426191)
    ·
      refine ⟨123314202302942808378639287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82209468201961872252426191 123314202302942808378639287)
      ·
        refine ⟨184971303454414212567958931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123314202302942808378639287 184971303454414212567958931)
        ·
          refine ⟨277456955181621318851938397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184971303454414212567958931 277456955181621318851938397)
          ·
            refine ⟨104046358193107994569476899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277456955181621318851938397 104046358193107994569476899)
            ·
              refine ⟨156069537289661991854215349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104046358193107994569476899 156069537289661991854215349)
              ·
                refine ⟨14631519120905811736332689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156069537289661991854215349 14631519120905811736332689)
                ·
                  refine ⟨10973639340679358802249517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14631519120905811736332689 10973639340679358802249517)
                  ·
                    refine ⟨4115114752754759550843569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10973639340679358802249517 4115114752754759550843569)
                    ·
                      refine ⟨3086336064566069663132677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115114752754759550843569 3086336064566069663132677)
                      ·
                        rfl

theorem cell23_6010618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_6010618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010618 prefixEnd_6010618 := by exact prefixLift 6010618
  have htrace : WordTrace (prefixWord ++ tailWord_6010618) baseStart_6010618 baseEnd_6010618 := by
    simpa [prefixWord, tailWord_6010618, baseEnd_6010618] using wordTrace_append hprefix tailTrace_6010618
  have hstable : (prefixWord ++ tailWord_6010618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010618).length < 2 ^ (prefixWord ++ tailWord_6010618).sum := by decide
  have hdescent : baseEnd_6010618 < baseStart_6010618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010628 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_6010628 : Nat := 118140960795 + 6010628 * 2 ^ 59
def prefixEnd_6010628 : Nat := 4983230072969 + 3 ^ 40 * 6010628 * 2
def baseEnd_6010628 : Nat := 1028780399790871541335877

theorem tailTrace_6010628 : CollatzResearch.WordTrace tailWord_6010628 prefixEnd_6010628 1028780399790871541335877 := by
  unfold tailWord_6010628
  simp only [CollatzResearch.WordTrace]
  refine ⟨109612806634264382190500269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146150408845685842920667025 109612806634264382190500269)
  ·
    refine ⟨41104802487849143321437601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109612806634264382190500269 41104802487849143321437601)
    ·
      refine ⟨30828601865886857491078201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41104802487849143321437601 30828601865886857491078201)
      ·
        refine ⟨23121451399415143118308651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30828601865886857491078201 23121451399415143118308651)
        ·
          refine ⟨34682177099122714677462977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23121451399415143118308651 34682177099122714677462977)
          ·
            refine ⟨26011632824342036008097233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34682177099122714677462977 26011632824342036008097233)
            ·
              refine ⟨19508724618256527006072925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26011632824342036008097233 19508724618256527006072925)
              ·
                refine ⟨7315771731846197627277347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19508724618256527006072925 7315771731846197627277347)
                ·
                  refine ⟨10973657597769296440916021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315771731846197627277347 10973657597769296440916021)
                  ·
                    refine ⟨1028780399790871541335877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10973657597769296440916021 1028780399790871541335877)
                    ·
                      rfl

theorem cell23_6010628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_6010628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010628 prefixEnd_6010628 := by exact prefixLift 6010628
  have htrace : WordTrace (prefixWord ++ tailWord_6010628) baseStart_6010628 baseEnd_6010628 := by
    simpa [prefixWord, tailWord_6010628, baseEnd_6010628] using wordTrace_append hprefix tailTrace_6010628
  have hstable : (prefixWord ++ tailWord_6010628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010628).length < 2 ^ (prefixWord ++ tailWord_6010628).sum := by decide
  have hdescent : baseEnd_6010628 < baseStart_6010628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010642 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6010642 : Nat := 118140960795 + 6010642 * 2 ^ 59
def prefixEnd_6010642 : Nat := 4983230072969 + 3 ^ 40 * 6010642 * 2
def baseEnd_6010642 : Nat := 3086348388101777569232567

theorem tailTrace_6010642 : CollatzResearch.WordTrace tailWord_6010642 prefixEnd_6010642 3086348388101777569232567 := by
  unfold tailWord_6010642
  simp only [CollatzResearch.WordTrace]
  refine ⟨54806530972619511193002545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146150749260318696514673453 54806530972619511193002545)
  ·
    refine ⟨41104898229464633394751909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54806530972619511193002545 41104898229464633394751909)
    ·
      refine ⟨7707168418024618761515983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41104898229464633394751909 7707168418024618761515983)
      ·
        refine ⟨11560752627036928142273975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7707168418024618761515983 11560752627036928142273975)
        ·
          refine ⟨17341128940555392213410963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11560752627036928142273975 17341128940555392213410963)
          ·
            refine ⟨26011693410833088320116445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17341128940555392213410963 26011693410833088320116445)
            ·
              refine ⟨9754385029062408120043667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26011693410833088320116445 9754385029062408120043667)
              ·
                refine ⟨14631577543593612180065501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754385029062408120043667 14631577543593612180065501)
                ·
                  refine ⟨5486841578847604567524563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14631577543593612180065501 5486841578847604567524563)
                  ·
                    refine ⟨8230262368271406851286845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486841578847604567524563 8230262368271406851286845)
                    ·
                      refine ⟨3086348388101777569232567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230262368271406851286845 3086348388101777569232567)
                      ·
                        rfl

theorem cell23_6010642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6010642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010642 prefixEnd_6010642 := by exact prefixLift 6010642
  have htrace : WordTrace (prefixWord ++ tailWord_6010642) baseStart_6010642 baseEnd_6010642 := by
    simpa [prefixWord, tailWord_6010642, baseEnd_6010642] using wordTrace_append hprefix tailTrace_6010642
  have hstable : (prefixWord ++ tailWord_6010642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010642).length < 2 ^ (prefixWord ++ tailWord_6010642).sum := by decide
  have hdescent : baseEnd_6010642 < baseStart_6010642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010651 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3]
def baseStart_6010651 : Nat := 118140960795 + 6010651 * 2 ^ 59
def prefixEnd_6010651 : Nat := 4983230072969 + 3 ^ 40 * 6010651 * 2
def baseEnd_6010651 : Nat := 3086353009427668034020025

theorem tailTrace_6010651 : CollatzResearch.WordTrace tailWord_6010651 prefixEnd_6010651 3086353009427668034020025 := by
  unfold tailWord_6010651
  simp only [CollatzResearch.WordTrace]
  refine ⟨219226452147445439309087807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146150968098296959539391871 219226452147445439309087807)
  ·
    refine ⟨328839678221168158963631711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219226452147445439309087807 328839678221168158963631711)
    ·
      refine ⟨493259517331752238445447567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328839678221168158963631711 493259517331752238445447567)
      ·
        refine ⟨739889275997628357668171351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493259517331752238445447567 739889275997628357668171351)
        ·
          refine ⟨1109833913996442536502257027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739889275997628357668171351 1109833913996442536502257027)
          ·
            refine ⟨1664750870994663804753385541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109833913996442536502257027 1664750870994663804753385541)
            ·
              refine ⟨312140788311499463391259789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1664750870994663804753385541 312140788311499463391259789)
              ·
                refine ⟨117052795616812298771722421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312140788311499463391259789 117052795616812298771722421)
                ·
                  refine ⟨10973699589076153009848977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117052795616812298771722421 10973699589076153009848977)
                  ·
                    refine ⟨8230274691807114757386733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10973699589076153009848977 8230274691807114757386733)
                    ·
                      refine ⟨3086353009427668034020025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230274691807114757386733 3086353009427668034020025)
                      ·
                        rfl

theorem cell23_6010651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3].length) (baseStart_6010651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010651 prefixEnd_6010651 := by exact prefixLift 6010651
  have htrace : WordTrace (prefixWord ++ tailWord_6010651) baseStart_6010651 baseEnd_6010651 := by
    simpa [prefixWord, tailWord_6010651, baseEnd_6010651] using wordTrace_append hprefix tailTrace_6010651
  have hstable : (prefixWord ++ tailWord_6010651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010651).length < 2 ^ (prefixWord ++ tailWord_6010651).sum := by decide
  have hdescent : baseEnd_6010651 < baseStart_6010651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010661 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_6010661 : Nat := 118140960795 + 6010661 * 2 ^ 59
def prefixEnd_6010661 : Nat := 4983230072969 + 3 ^ 40 * 6010661 * 2
def baseEnd_6010661 : Nat := 3086358144234212994894979

theorem tailTrace_6010661 : CollatzResearch.WordTrace tailWord_6010661 prefixEnd_6010661 3086358144234212994894979 := by
  unfold tailWord_6010661
  simp only [CollatzResearch.WordTrace]
  refine ⟨219226816877409211016951837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146151211251606140677967891 219226816877409211016951837)
  ·
    refine ⟨82210056329028454131356939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219226816877409211016951837 82210056329028454131356939)
    ·
      refine ⟨123315084493542681197035409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82210056329028454131356939 123315084493542681197035409)
      ·
        refine ⟨92486313370157010897776557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123315084493542681197035409 92486313370157010897776557)
        ·
          refine ⟨34682367513808879086666209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92486313370157010897776557 34682367513808879086666209)
          ·
            refine ⟨26011775635356659314999657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34682367513808879086666209 26011775635356659314999657)
            ·
              refine ⟨19508831726517494486249743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26011775635356659314999657 19508831726517494486249743)
              ·
                refine ⟨29263247589776241729374615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19508831726517494486249743 29263247589776241729374615)
                ·
                  refine ⟨43894871384664362594061923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29263247589776241729374615 43894871384664362594061923)
                  ·
                    refine ⟨65842307076996543891092885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43894871384664362594061923 65842307076996543891092885)
                    ·
                      refine ⟨3086358144234212994894979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65842307076996543891092885 3086358144234212994894979)
                      ·
                        rfl

theorem cell23_6010661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_6010661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010661 prefixEnd_6010661 := by exact prefixLift 6010661
  have htrace : WordTrace (prefixWord ++ tailWord_6010661) baseStart_6010661 baseEnd_6010661 := by
    simpa [prefixWord, tailWord_6010661, baseEnd_6010661] using wordTrace_append hprefix tailTrace_6010661
  have hstable : (prefixWord ++ tailWord_6010661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010661).length < 2 ^ (prefixWord ++ tailWord_6010661).sum := by decide
  have hdescent : baseEnd_6010661 < baseStart_6010661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010668 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_6010668 : Nat := 118140960795 + 6010668 * 2 ^ 59
def prefixEnd_6010668 : Nat := 4983230072969 + 3 ^ 40 * 6010668 * 2
def baseEnd_6010668 : Nat := 3086361738598794467507447

theorem tailTrace_6010668 : CollatzResearch.WordTrace tailWord_6010668 prefixEnd_6010668 3086361738598794467507447 := by
  unfold tailWord_6010668
  simp only [CollatzResearch.WordTrace]
  refine ⟨109613536094191925606228329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146151381458922567474971105 109613536094191925606228329)
  ·
    refine ⟨82210152070643944204671247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109613536094191925606228329 82210152070643944204671247)
    ·
      refine ⟨123315228105965916307006871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82210152070643944204671247 123315228105965916307006871)
      ·
        refine ⟨184972842158948874460510307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123315228105965916307006871 184972842158948874460510307)
        ·
          refine ⟨277459263238423311690765461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184972842158948874460510307 277459263238423311690765461)
          ·
            refine ⟨13005902964301092735504631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277459263238423311690765461 13005902964301092735504631)
            ·
              refine ⟨19508854446451639103256947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13005902964301092735504631 19508854446451639103256947)
              ·
                refine ⟨29263281669677458654885421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19508854446451639103256947 29263281669677458654885421)
                ·
                  refine ⟨10973730626129046995582033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29263281669677458654885421 10973730626129046995582033)
                  ·
                    refine ⟨8230297969596785246686525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10973730626129046995582033 8230297969596785246686525)
                    ·
                      refine ⟨3086361738598794467507447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230297969596785246686525 3086361738598794467507447)
                      ·
                        rfl

theorem cell23_6010668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_6010668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010668 prefixEnd_6010668 := by exact prefixLift 6010668
  have htrace : WordTrace (prefixWord ++ tailWord_6010668) baseStart_6010668 baseEnd_6010668 := by
    simpa [prefixWord, tailWord_6010668, baseEnd_6010668] using wordTrace_append hprefix tailTrace_6010668
  have hstable : (prefixWord ++ tailWord_6010668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010668).length < 2 ^ (prefixWord ++ tailWord_6010668).sum := by decide
  have hdescent : baseEnd_6010668 < baseStart_6010668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010685 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6010685 : Nat := 118140960795 + 6010685 * 2 ^ 59
def prefixEnd_6010685 : Nat := 4983230072969 + 3 ^ 40 * 6010685 * 2
def baseEnd_6010685 : Nat := 3086370467769920900994869

theorem tailTrace_6010685 : CollatzResearch.WordTrace tailWord_6010685 prefixEnd_6010685 3086370467769920900994869 := by
  unfold tailWord_6010685
  simp only [CollatzResearch.WordTrace]
  refine ⟨219227692229322263115825509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146151794819548175410550339 219227692229322263115825509)
  ·
    refine ⟨41105192292997924334217283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219227692229322263115825509 41105192292997924334217283)
    ·
      refine ⟨61657788439496886501325925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41105192292997924334217283 61657788439496886501325925)
      ·
        refine ⟨11560835332405666218998611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61657788439496886501325925 11560835332405666218998611)
        ·
          refine ⟨17341252998608499328497917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11560835332405666218998611 17341252998608499328497917)
          ·
            refine ⟨6502969874478187248186719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17341252998608499328497917 6502969874478187248186719)
            ·
              refine ⟨9754454811717280872280079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502969874478187248186719 9754454811717280872280079)
              ·
                refine ⟨14631682217575921308420119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754454811717280872280079 14631682217575921308420119)
                ·
                  refine ⟨21947523326363881962630179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14631682217575921308420119 21947523326363881962630179)
                  ·
                    refine ⟨32921284989545822943945269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21947523326363881962630179 32921284989545822943945269)
                    ·
                      refine ⟨3086370467769920900994869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32921284989545822943945269 3086370467769920900994869)
                      ·
                        rfl

theorem cell23_6010685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6010685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010685 prefixEnd_6010685 := by exact prefixLift 6010685
  have htrace : WordTrace (prefixWord ++ tailWord_6010685) baseStart_6010685 baseEnd_6010685 := by
    simpa [prefixWord, tailWord_6010685, baseEnd_6010685] using wordTrace_append hprefix tailTrace_6010685
  have hstable : (prefixWord ++ tailWord_6010685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010685).length < 2 ^ (prefixWord ++ tailWord_6010685).sum := by decide
  have hdescent : baseEnd_6010685 < baseStart_6010685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010721 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_6010721 : Nat := 118140960795 + 6010721 * 2 ^ 59
def prefixEnd_6010721 : Nat := 4983230072969 + 3 ^ 40 * 6010721 * 2
def baseEnd_6010721 : Nat := 3086388953073482760144703

theorem tailTrace_6010721 : CollatzResearch.WordTrace tailWord_6010721 prefixEnd_6010721 3086388953073482760144703 := by
  unfold tailWord_6010721
  simp only [CollatzResearch.WordTrace]
  refine ⟨219229005257191841264136017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146152670171461227509424011 219229005257191841264136017)
  ·
    refine ⟨164421753942893880948102013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219229005257191841264136017 164421753942893880948102013)
    ·
      refine ⟨61658157728585205355538255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164421753942893880948102013 61658157728585205355538255)
      ·
        refine ⟨92487236592877808033307383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61658157728585205355538255 92487236592877808033307383)
        ·
          refine ⟨138730854889316712049961075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92487236592877808033307383 138730854889316712049961075)
          ·
            refine ⟨208096282333975068074941613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138730854889316712049961075 208096282333975068074941613)
            ·
              refine ⟨78036105875240650528103105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208096282333975068074941613 78036105875240650528103105)
              ·
                refine ⟨58527079406430487896077329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78036105875240650528103105 58527079406430487896077329)
                ·
                  refine ⟨43895309554822865922057997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58527079406430487896077329 43895309554822865922057997)
                  ·
                    refine ⟨16460741083058574720771749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43895309554822865922057997 16460741083058574720771749)
                    ·
                      refine ⟨3086388953073482760144703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16460741083058574720771749 3086388953073482760144703)
                      ·
                        rfl

theorem cell23_6010721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_6010721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010721 prefixEnd_6010721 := by exact prefixLift 6010721
  have htrace : WordTrace (prefixWord ++ tailWord_6010721) baseStart_6010721 baseEnd_6010721 := by
    simpa [prefixWord, tailWord_6010721, baseEnd_6010721] using wordTrace_append hprefix tailTrace_6010721
  have hstable : (prefixWord ++ tailWord_6010721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010721).length < 2 ^ (prefixWord ++ tailWord_6010721).sum := by decide
  have hdescent : baseEnd_6010721 < baseStart_6010721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010725 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_6010725 : Nat := 118140960795 + 6010725 * 2 ^ 59
def prefixEnd_6010725 : Nat := 4983230072969 + 3 ^ 40 * 6010725 * 2
def baseEnd_6010725 : Nat := 3086391006996100744494685

theorem tailTrace_6010725 : CollatzResearch.WordTrace tailWord_6010725 prefixEnd_6010725 3086391006996100744494685 := by
  unfold tailWord_6010725
  simp only [CollatzResearch.WordTrace]
  refine ⟨219229151149177349947281629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146152767432784899964854419 219229151149177349947281629)
  ·
    refine ⟨82210931680941506230230611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219229151149177349947281629 82210931680941506230230611)
    ·
      refine ⟨123316397521412259345345917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82210931680941506230230611 123316397521412259345345917)
      ·
        refine ⟨46243649070529597254504719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123316397521412259345345917 46243649070529597254504719)
        ·
          refine ⟨69365473605794395881757079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46243649070529597254504719 69365473605794395881757079)
          ·
            refine ⟨104048210408691593822635619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69365473605794395881757079 104048210408691593822635619)
            ·
              refine ⟨156072315613037390733953429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104048210408691593822635619 156072315613037390733953429)
              ·
                refine ⟨7315889794361127690654067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156072315613037390733953429 7315889794361127690654067)
                ·
                  refine ⟨10973834691541691535981101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315889794361127690654067 10973834691541691535981101)
                  ·
                    refine ⟨4115188009328134325992913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10973834691541691535981101 4115188009328134325992913)
                    ·
                      refine ⟨3086391006996100744494685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115188009328134325992913 3086391006996100744494685)
                      ·
                        rfl

theorem cell23_6010725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_6010725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010725 prefixEnd_6010725 := by exact prefixLift 6010725
  have htrace : WordTrace (prefixWord ++ tailWord_6010725) baseStart_6010725 baseEnd_6010725 := by
    simpa [prefixWord, tailWord_6010725, baseEnd_6010725] using wordTrace_append hprefix tailTrace_6010725
  have hstable : (prefixWord ++ tailWord_6010725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010725).length < 2 ^ (prefixWord ++ tailWord_6010725).sum := by decide
  have hdescent : baseEnd_6010725 < baseStart_6010725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010766 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6010766 : Nat := 118140960795 + 6010766 * 2 ^ 59
def prefixEnd_6010766 : Nat := 4983230072969 + 3 ^ 40 * 6010766 * 2
def baseEnd_6010766 : Nat := 3086412059702935084081997

theorem tailTrace_6010766 : CollatzResearch.WordTrace tailWord_6010766 prefixEnd_6010766 3086412059702935084081997 := by
  unfold tailWord_6010766
  simp only [CollatzResearch.WordTrace]
  refine ⟨27403830817753601743690519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146153764361352542633016101 27403830817753601743690519)
  ·
    refine ⟨41105746226630402615535779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27403830817753601743690519 41105746226630402615535779)
    ·
      refine ⟨61658619339945603923303669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41105746226630402615535779 61658619339945603923303669)
      ·
        refine ⟨5780495563119900367809719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61658619339945603923303669 5780495563119900367809719)
        ·
          refine ⟨8670743344679850551714579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780495563119900367809719 8670743344679850551714579)
          ·
            refine ⟨13006115017019775827571869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8670743344679850551714579 13006115017019775827571869)
            ·
              refine ⟨4877293131382415935339451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13006115017019775827571869 4877293131382415935339451)
              ·
                refine ⟨7315939697073623903009177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877293131382415935339451 7315939697073623903009177)
                ·
                  refine ⟨5486954772805217927256883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7315939697073623903009177 5486954772805217927256883)
                  ·
                    refine ⟨8230432159207826890885325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486954772805217927256883 8230432159207826890885325)
                    ·
                      refine ⟨3086412059702935084081997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230432159207826890885325 3086412059702935084081997)
                      ·
                        rfl

theorem cell23_6010766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6010766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010766 prefixEnd_6010766 := by exact prefixLift 6010766
  have htrace : WordTrace (prefixWord ++ tailWord_6010766) baseStart_6010766 baseEnd_6010766 := by
    simpa [prefixWord, tailWord_6010766, baseEnd_6010766] using wordTrace_append hprefix tailTrace_6010766
  have hstable : (prefixWord ++ tailWord_6010766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010766).length < 2 ^ (prefixWord ++ tailWord_6010766).sum := by decide
  have hdescent : baseEnd_6010766 < baseStart_6010766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010772 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6010772 : Nat := 118140960795 + 6010772 * 2 ^ 59
def prefixEnd_6010772 : Nat := 4983230072969 + 3 ^ 40 * 6010772 * 2
def baseEnd_6010772 : Nat := 3086415140586862060606969

theorem tailTrace_6010772 : CollatzResearch.WordTrace tailWord_6010772 prefixEnd_6010772 3086415140586862060606969 := by
  unfold tailWord_6010772
  simp only [CollatzResearch.WordTrace]
  refine ⟨109615432690003538487121285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146153910253338051316161713 109615432690003538487121285)
  ·
    refine ⟨20552893629375663466335241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109615432690003538487121285 20552893629375663466335241)
    ·
      refine ⟨15414670222031747599751431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20552893629375663466335241 15414670222031747599751431)
      ·
        refine ⟨23122005333047621399627147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15414670222031747599751431 23122005333047621399627147)
        ·
          refine ⟨34683007999571432099440721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23122005333047621399627147 34683007999571432099440721)
          ·
            refine ⟨26012255999678574074580541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34683007999571432099440721 26012255999678574074580541)
            ·
              refine ⟨9754595999879465277967703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26012255999678574074580541 9754595999879465277967703)
              ·
                refine ⟨14631893999819197916951555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754595999879465277967703 14631893999819197916951555)
                ·
                  refine ⟨21947840999728796875427333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14631893999819197916951555 21947840999728796875427333)
                  ·
                    refine ⟨4115220187449149414142625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21947840999728796875427333 4115220187449149414142625)
                    ·
                      refine ⟨3086415140586862060606969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115220187449149414142625 3086415140586862060606969)
                      ·
                        rfl

theorem cell23_6010772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6010772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010772 prefixEnd_6010772 := by exact prefixLift 6010772
  have htrace : WordTrace (prefixWord ++ tailWord_6010772) baseStart_6010772 baseEnd_6010772 := by
    simpa [prefixWord, tailWord_6010772, baseEnd_6010772] using wordTrace_append hprefix tailTrace_6010772
  have hstable : (prefixWord ++ tailWord_6010772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010772).length < 2 ^ (prefixWord ++ tailWord_6010772).sum := by decide
  have hdescent : baseEnd_6010772 < baseStart_6010772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010778 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_6010778 : Nat := 118140960795 + 6010778 * 2 ^ 59
def prefixEnd_6010778 : Nat := 4983230072969 + 3 ^ 40 * 6010778 * 2
def baseEnd_6010778 : Nat := 342935357941198781903549

theorem tailTrace_6010778 : CollatzResearch.WordTrace tailWord_6010778 prefixEnd_6010778 342935357941198781903549 := by
  unfold tailWord_6010778
  simp only [CollatzResearch.WordTrace]
  refine ⟨54807771054496334999740247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146154056145323559999307325 54807771054496334999740247)
  ·
    refine ⟨82211656581744502499610371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54807771054496334999740247 82211656581744502499610371)
    ·
      refine ⟨123317484872616753749415557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82211656581744502499610371 123317484872616753749415557)
      ·
        refine ⟨23122028413615641328015417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123317484872616753749415557 23122028413615641328015417)
        ·
          refine ⟨17341521310211730996011563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23122028413615641328015417 17341521310211730996011563)
          ·
            refine ⟨26012281965317596494017345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17341521310211730996011563 26012281965317596494017345)
            ·
              refine ⟨19509211473988197370513009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26012281965317596494017345 19509211473988197370513009)
              ·
                refine ⟨14631908605491148027884757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19509211473988197370513009 14631908605491148027884757)
                ·
                  refine ⟨342935357941198781903549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14631908605491148027884757 342935357941198781903549)
                  ·
                    rfl

theorem cell23_6010778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_6010778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010778 prefixEnd_6010778 := by exact prefixLift 6010778
  have htrace : WordTrace (prefixWord ++ tailWord_6010778) baseStart_6010778 baseEnd_6010778 := by
    simpa [prefixWord, tailWord_6010778, baseEnd_6010778] using wordTrace_append hprefix tailTrace_6010778
  have hstable : (prefixWord ++ tailWord_6010778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010778).length < 2 ^ (prefixWord ++ tailWord_6010778).sum := by decide
  have hdescent : baseEnd_6010778 < baseStart_6010778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010792 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6010792 : Nat := 118140960795 + 6010792 * 2 ^ 59
def prefixEnd_6010792 : Nat := 4983230072969 + 3 ^ 40 * 6010792 * 2
def baseEnd_6010792 : Nat := 3086425410199951982356877

theorem tailTrace_6010792 : CollatzResearch.WordTrace tailWord_6010792 prefixEnd_6010792 3086425410199951982356877 := by
  unfold tailWord_6010792
  simp only [CollatzResearch.WordTrace]
  refine ⟨109615797419967310194985315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146154396559956413593313753 109615797419967310194985315)
  ·
    refine ⟨164423696129950965292477973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109615797419967310194985315 164423696129950965292477973)
    ·
      refine ⟨7707360756091451498084905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164423696129950965292477973 7707360756091451498084905)
      ·
        refine ⟨5780520567068588623563679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7707360756091451498084905 5780520567068588623563679)
        ·
          refine ⟨8670780850602882935345519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780520567068588623563679 8670780850602882935345519)
          ·
            refine ⟨13006171275904324403018279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8670780850602882935345519 13006171275904324403018279)
            ·
              refine ⟨19509256913856486604527419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13006171275904324403018279 19509256913856486604527419)
              ·
                refine ⟨29263885370784729906791129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19509256913856486604527419 29263885370784729906791129)
                ·
                  refine ⟨21947914028088547430093347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29263885370784729906791129 21947914028088547430093347)
                  ·
                    refine ⟨32921871042132821145140021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21947914028088547430093347 32921871042132821145140021)
                    ·
                      refine ⟨3086425410199951982356877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32921871042132821145140021 3086425410199951982356877)
                      ·
                        rfl

theorem cell23_6010792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6010792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010792 prefixEnd_6010792 := by exact prefixLift 6010792
  have htrace : WordTrace (prefixWord ++ tailWord_6010792) baseStart_6010792 baseEnd_6010792 := by
    simpa [prefixWord, tailWord_6010792, baseEnd_6010792] using wordTrace_append hprefix tailTrace_6010792
  have hstable : (prefixWord ++ tailWord_6010792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010792).length < 2 ^ (prefixWord ++ tailWord_6010792).sum := by decide
  have hdescent : baseEnd_6010792 < baseStart_6010792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010808 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_6010808 : Nat := 118140960795 + 6010808 * 2 ^ 59
def prefixEnd_6010808 : Nat := 4983230072969 + 3 ^ 40 * 6010808 * 2
def baseEnd_6010808 : Nat := 1028811208630141306585601

theorem tailTrace_6010808 : CollatzResearch.WordTrace tailWord_6010808 prefixEnd_6010808 1028811208630141306585601 := by
  unfold tailWord_6010808
  simp only [CollatzResearch.WordTrace]
  refine ⟨109616089203938327561276539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146154785605251103415035385 109616089203938327561276539)
  ·
    refine ⟨164424133805907491341914809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109616089203938327561276539 164424133805907491341914809)
    ·
      refine ⟨123318100354430618506436107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164424133805907491341914809 123318100354430618506436107)
      ·
        refine ⟨184977150531645927759654161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123318100354430618506436107 184977150531645927759654161)
        ·
          refine ⟨138732862898734445819740621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184977150531645927759654161 138732862898734445819740621)
          ·
            refine ⟨52024823587025417182402733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138732862898734445819740621 52024823587025417182402733)
            ·
              refine ⟨19509308845134531443401025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52024823587025417182402733 19509308845134531443401025)
              ·
                refine ⟨14631981633850898582550769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19509308845134531443401025 14631981633850898582550769)
                ·
                  refine ⟨10973986225388173936913077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14631981633850898582550769 10973986225388173936913077)
                  ·
                    refine ⟨1028811208630141306585601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10973986225388173936913077 1028811208630141306585601)
                    ·
                      rfl

theorem cell23_6010808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_6010808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010808 prefixEnd_6010808 := by exact prefixLift 6010808
  have htrace : WordTrace (prefixWord ++ tailWord_6010808) baseStart_6010808 baseEnd_6010808 := by
    simpa [prefixWord, tailWord_6010808, baseEnd_6010808] using wordTrace_append hprefix tailTrace_6010808
  have hstable : (prefixWord ++ tailWord_6010808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010808).length < 2 ^ (prefixWord ++ tailWord_6010808).sum := by decide
  have hdescent : baseEnd_6010808 < baseStart_6010808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010812 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 7]
def baseStart_6010812 : Nat := 118140960795 + 6010812 * 2 ^ 59
def prefixEnd_6010812 : Nat := 4983230072969 + 3 ^ 40 * 6010812 * 2
def baseEnd_6010812 : Nat := 342937297757004656011865

theorem tailTrace_6010812 : CollatzResearch.WordTrace tailWord_6010812 prefixEnd_6010812 342937297757004656011865 := by
  unfold tailWord_6010812
  simp only [CollatzResearch.WordTrace]
  refine ⟨109616162149931081902849345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146154882866574775870465793 109616162149931081902849345)
  ·
    refine ⟨82212121612448311427137009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109616162149931081902849345 82212121612448311427137009)
    ·
      refine ⟨61659091209336233570352757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82212121612448311427137009 61659091209336233570352757)
      ·
        refine ⟨5780539800875271897220571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61659091209336233570352757 5780539800875271897220571)
        ·
          refine ⟨8670809701312907845830857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780539800875271897220571 8670809701312907845830857)
          ·
            refine ⟨6503107275984680884373143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8670809701312907845830857 6503107275984680884373143)
            ·
              refine ⟨9754660913977021326559715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503107275984680884373143 9754660913977021326559715)
              ·
                refine ⟨14631991370965531989839573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754660913977021326559715 14631991370965531989839573)
                ·
                  refine ⟨342937297757004656011865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14631991370965531989839573 342937297757004656011865)
                  ·
                    rfl

theorem cell23_6010812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_6010812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010812 prefixEnd_6010812 := by exact prefixLift 6010812
  have htrace : WordTrace (prefixWord ++ tailWord_6010812) baseStart_6010812 baseEnd_6010812 := by
    simpa [prefixWord, tailWord_6010812, baseEnd_6010812] using wordTrace_append hprefix tailTrace_6010812
  have hstable : (prefixWord ++ tailWord_6010812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010812).length < 2 ^ (prefixWord ++ tailWord_6010812).sum := by decide
  have hdescent : baseEnd_6010812 < baseStart_6010812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010821 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_6010821 : Nat := 118140960795 + 6010821 * 2 ^ 59
def prefixEnd_6010821 : Nat := 4983230072969 + 3 ^ 40 * 6010821 * 2
def baseEnd_6010821 : Nat := 1028813433712977456298081

theorem tailTrace_6010821 : CollatzResearch.WordTrace tailWord_6010821 prefixEnd_6010821 1028813433712977456298081 := by
  unfold tailWord_6010821
  simp only [CollatzResearch.WordTrace]
  refine ⟨219232652556829558342776317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146155101704553038895184211 219232652556829558342776317)
  ·
    refine ⟨82212244708811084378541119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219232652556829558342776317 82212244708811084378541119)
    ·
      refine ⟨123318367063216626567811679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82212244708811084378541119 123318367063216626567811679)
      ·
        refine ⟨184977550594824939851717519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123318367063216626567811679 184977550594824939851717519)
        ·
          refine ⟨277466325892237409777576279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184977550594824939851717519 277466325892237409777576279)
          ·
            refine ⟨416199488838356114666364419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277466325892237409777576279 416199488838356114666364419)
            ·
              refine ⟨624299233257534171999546629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416199488838356114666364419 624299233257534171999546629)
              ·
                refine ⟨117056106235787657249914993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624299233257534171999546629 117056106235787657249914993)
                ·
                  refine ⟨87792079676840742937436245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117056106235787657249914993 87792079676840742937436245)
                  ·
                    refine ⟨1028813433712977456298081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87792079676840742937436245 1028813433712977456298081)
                    ·
                      rfl

theorem cell23_6010821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_6010821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010821 prefixEnd_6010821 := by exact prefixLift 6010821
  have htrace : WordTrace (prefixWord ++ tailWord_6010821) baseStart_6010821 baseEnd_6010821 := by
    simpa [prefixWord, tailWord_6010821, baseEnd_6010821] using wordTrace_append hprefix tailTrace_6010821
  have hstable : (prefixWord ++ tailWord_6010821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010821).length < 2 ^ (prefixWord ++ tailWord_6010821).sum := by decide
  have hdescent : baseEnd_6010821 < baseStart_6010821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010848 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_6010848 : Nat := 118140960795 + 6010848 * 2 ^ 59
def prefixEnd_6010848 : Nat := 4983230072969 + 3 ^ 40 * 6010848 * 2
def baseEnd_6010848 : Nat := 3086454165116603763256619

theorem tailTrace_6010848 : CollatzResearch.WordTrace tailWord_6010848 prefixEnd_6010848 3086454165116603763256619 := by
  unfold tailWord_6010848
  simp only [CollatzResearch.WordTrace]
  refine ⟨109616818663865870977004599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146155758218487827969339465 109616818663865870977004599)
  ·
    refine ⟨164425227995798806465506899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109616818663865870977004599 164425227995798806465506899)
    ·
      refine ⟨246637841993698209698260349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164425227995798806465506899 246637841993698209698260349)
      ·
        refine ⟨92489190747636828636847631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246637841993698209698260349 92489190747636828636847631)
        ·
          refine ⟨138733786121455242955271447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92489190747636828636847631 138733786121455242955271447)
          ·
            refine ⟨208100679182182864432907171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138733786121455242955271447 208100679182182864432907171)
            ·
              refine ⟨312151018773274296649360757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208100679182182864432907171 312151018773274296649360757)
              ·
                refine ⟨29264158009994465310877571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312151018773274296649360757 29264158009994465310877571)
                ·
                  refine ⟨43896237014991697966316357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29264158009994465310877571 43896237014991697966316357)
                  ·
                    refine ⟨8230544440310943368684317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43896237014991697966316357 8230544440310943368684317)
                    ·
                      refine ⟨3086454165116603763256619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230544440310943368684317 3086454165116603763256619)
                      ·
                        rfl

theorem cell23_6010848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_6010848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010848 prefixEnd_6010848 := by exact prefixLift 6010848
  have htrace : WordTrace (prefixWord ++ tailWord_6010848) baseStart_6010848 baseEnd_6010848 := by
    simpa [prefixWord, tailWord_6010848, baseEnd_6010848] using wordTrace_append hprefix tailTrace_6010848
  have hstable : (prefixWord ++ tailWord_6010848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010848).length < 2 ^ (prefixWord ++ tailWord_6010848).sum := by decide
  have hdescent : baseEnd_6010848 < baseStart_6010848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010858 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6010858 : Nat := 118140960795 + 6010858 * 2 ^ 59
def prefixEnd_6010858 : Nat := 4983230072969 + 3 ^ 40 * 6010858 * 2
def baseEnd_6010858 : Nat := 3086459299923148724131573

theorem tailTrace_6010858 : CollatzResearch.WordTrace tailWord_6010858 prefixEnd_6010858 3086459299923148724131573 := by
  unfold tailWord_6010858
  simp only [CollatzResearch.WordTrace]
  refine ⟨54808500514423878415468307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146156001371797009107915485 54808500514423878415468307)
  ·
    refine ⟨82212750771635817623202461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54808500514423878415468307 82212750771635817623202461)
    ·
      refine ⟨30829781539363431608700923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82212750771635817623202461 30829781539363431608700923)
      ·
        refine ⟨46244672309045147413051385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30829781539363431608700923 46244672309045147413051385)
        ·
          refine ⟨34683504231783860559788539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46244672309045147413051385 34683504231783860559788539)
          ·
            refine ⟨52025256347675790839682809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34683504231783860559788539 52025256347675790839682809)
            ·
              refine ⟨39018942260756843129762107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52025256347675790839682809 39018942260756843129762107)
              ·
                refine ⟨58528413391135264694643161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39018942260756843129762107 58528413391135264694643161)
                ·
                  refine ⟨43896310043351448520982371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58528413391135264694643161 43896310043351448520982371)
                  ·
                    refine ⟨65844465065027172781473557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43896310043351448520982371 65844465065027172781473557)
                    ·
                      refine ⟨3086459299923148724131573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65844465065027172781473557 3086459299923148724131573)
                      ·
                        rfl

theorem cell23_6010858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6010858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010858 prefixEnd_6010858 := by exact prefixLift 6010858
  have htrace : WordTrace (prefixWord ++ tailWord_6010858) baseStart_6010858 baseEnd_6010858 := by
    simpa [prefixWord, tailWord_6010858, baseEnd_6010858] using wordTrace_append hprefix tailTrace_6010858
  have hstable : (prefixWord ++ tailWord_6010858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010858).length < 2 ^ (prefixWord ++ tailWord_6010858).sum := by decide
  have hdescent : baseEnd_6010858 < baseStart_6010858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010893 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6010893 : Nat := 118140960795 + 6010893 * 2 ^ 59
def prefixEnd_6010893 : Nat := 4983230072969 + 3 ^ 40 * 6010893 * 2
def baseEnd_6010893 : Nat := 1028825757248685362397971

theorem tailTrace_6010893 : CollatzResearch.WordTrace tailWord_6010893 prefixEnd_6010893 1028825757248685362397971 := by
  unfold tailWord_6010893
  simp only [CollatzResearch.WordTrace]
  refine ⟨219235278612568714639397333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146156852408379143092931555 219235278612568714639397333)
  ·
    refine ⟨5138326842482079249360875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 219235278612568714639397333 5138326842482079249360875)
    ·
      refine ⟨7707490263723118874041313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138326842482079249360875 7707490263723118874041313)
      ·
        refine ⟨5780617697792339155530985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7707490263723118874041313 5780617697792339155530985)
        ·
          refine ⟨4335463273344254366648239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5780617697792339155530985 4335463273344254366648239)
          ·
            refine ⟨6503194910016381549972359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335463273344254366648239 6503194910016381549972359)
            ·
              refine ⟨9754792365024572324958539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503194910016381549972359 9754792365024572324958539)
              ·
                refine ⟨14632188547536858487437809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754792365024572324958539 14632188547536858487437809)
                ·
                  refine ⟨10974141410652643865578357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14632188547536858487437809 10974141410652643865578357)
                  ·
                    refine ⟨1028825757248685362397971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10974141410652643865578357 1028825757248685362397971)
                    ·
                      rfl

theorem cell23_6010893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6010893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010893 prefixEnd_6010893 := by exact prefixLift 6010893
  have htrace : WordTrace (prefixWord ++ tailWord_6010893) baseStart_6010893 baseEnd_6010893 := by
    simpa [prefixWord, tailWord_6010893, baseEnd_6010893] using wordTrace_append hprefix tailTrace_6010893
  have hstable : (prefixWord ++ tailWord_6010893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010893).length < 2 ^ (prefixWord ++ tailWord_6010893).sum := by decide
  have hdescent : baseEnd_6010893 < baseStart_6010893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010915 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 1, 5]
def baseStart_6010915 : Nat := 118140960795 + 6010915 * 2 ^ 59
def prefixEnd_6010915 : Nat := 4983230072969 + 3 ^ 40 * 6010915 * 2
def baseEnd_6010915 : Nat := 1028829522773485000372937

theorem tailTrace_6010915 : CollatzResearch.WordTrace tailWord_6010915 prefixEnd_6010915 1028829522773485000372937 := by
  unfold tailWord_6010915
  simp only [CollatzResearch.WordTrace]
  refine ⟨219236081018489012396698199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146157387345659341597798799 219236081018489012396698199)
  ·
    refine ⟨328854121527733518595047299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219236081018489012396698199 328854121527733518595047299)
    ·
      refine ⟨493281182291600277892570949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328854121527733518595047299 493281182291600277892570949)
      ·
        refine ⟨92490221679675052104857053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 493281182291600277892570949 92490221679675052104857053)
        ·
          refine ⟨34683833129878144539321395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92490221679675052104857053 34683833129878144539321395)
          ·
            refine ⟨52025749694817216808982093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34683833129878144539321395 52025749694817216808982093)
            ·
              refine ⟨19509656135556456303368285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52025749694817216808982093 19509656135556456303368285)
              ·
                refine ⟨7316121050833671113763107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19509656135556456303368285 7316121050833671113763107)
                ·
                  refine ⟨10974181576250506670644661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316121050833671113763107 10974181576250506670644661)
                  ·
                    refine ⟨1028829522773485000372937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10974181576250506670644661 1028829522773485000372937)
                    ·
                      rfl

theorem cell23_6010915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 5].length) (baseStart_6010915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010915 prefixEnd_6010915 := by exact prefixLift 6010915
  have htrace : WordTrace (prefixWord ++ tailWord_6010915) baseStart_6010915 baseEnd_6010915 := by
    simpa [prefixWord, tailWord_6010915, baseEnd_6010915] using wordTrace_append hprefix tailTrace_6010915
  have hstable : (prefixWord ++ tailWord_6010915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010915).length < 2 ^ (prefixWord ++ tailWord_6010915).sum := by decide
  have hdescent : baseEnd_6010915 < baseStart_6010915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010919 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 6]
def baseStart_6010919 : Nat := 118140960795 + 6010919 * 2 ^ 59
def prefixEnd_6010919 : Nat := 4983230072969 + 3 ^ 40 * 6010919 * 2
def baseEnd_6010919 : Nat := 342943402471452553940977

theorem tailTrace_6010919 : CollatzResearch.WordTrace tailWord_6010919 prefixEnd_6010919 342943402471452553940977 := by
  unfold tailWord_6010919
  simp only [CollatzResearch.WordTrace]
  refine ⟨219236226910474521079843811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146157484606983014053229207 219236226910474521079843811)
  ·
    refine ⟨328854340365711781619765717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219236226910474521079843811 328854340365711781619765717)
    ·
      refine ⟨7707523602321369881713259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 328854340365711781619765717 7707523602321369881713259)
      ·
        refine ⟨11561285403482054822569889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7707523602321369881713259 11561285403482054822569889)
        ·
          refine ⟨8670964052611541116927417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11561285403482054822569889 8670964052611541116927417)
          ·
            refine ⟨6503223039458655837695563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8670964052611541116927417 6503223039458655837695563)
            ·
              refine ⟨9754834559187983756543345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503223039458655837695563 9754834559187983756543345)
              ·
                refine ⟨7316125919390987817407509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9754834559187983756543345 7316125919390987817407509)
                ·
                  refine ⟨342943402471452553940977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7316125919390987817407509 342943402471452553940977)
                  ·
                    rfl

theorem cell23_6010919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 6].length) (baseStart_6010919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010919 prefixEnd_6010919 := by exact prefixLift 6010919
  have htrace : WordTrace (prefixWord ++ tailWord_6010919) baseStart_6010919 baseEnd_6010919 := by
    simpa [prefixWord, tailWord_6010919, baseEnd_6010919] using wordTrace_append hprefix tailTrace_6010919
  have hstable : (prefixWord ++ tailWord_6010919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010919).length < 2 ^ (prefixWord ++ tailWord_6010919).sum := by decide
  have hdescent : baseEnd_6010919 < baseStart_6010919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010929 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 1, 1, 3]
def baseStart_6010929 : Nat := 118140960795 + 6010929 * 2 ^ 59
def prefixEnd_6010929 : Nat := 4983230072969 + 3 ^ 40 * 6010929 * 2
def baseEnd_6010929 : Nat := 3086495757049617946343747

theorem tailTrace_6010929 : CollatzResearch.WordTrace tailWord_6010929 prefixEnd_6010929 3086495757049617946343747 := by
  unfold tailWord_6010929
  simp only [CollatzResearch.WordTrace]
  refine ⟨219236591640438292787707841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146157727760292195191805227 219236591640438292787707841)
  ·
    refine ⟨164427443730328719590780881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219236591640438292787707841 164427443730328719590780881)
    ·
      refine ⟨123320582797746539693085661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164427443730328719590780881 123320582797746539693085661)
      ·
        refine ⟨46245218549154952384907123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123320582797746539693085661 46245218549154952384907123)
        ·
          refine ⟨69367827823732428577360685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46245218549154952384907123 69367827823732428577360685)
          ·
            refine ⟨26012935433899660716510257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69367827823732428577360685 26012935433899660716510257)
            ·
              refine ⟨19509701575424745537382693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26012935433899660716510257 19509701575424745537382693)
              ·
                refine ⟨3658069045392139788259255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19509701575424745537382693 3658069045392139788259255)
                ·
                  refine ⟨5487103568088209682388883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658069045392139788259255 5487103568088209682388883)
                  ·
                    refine ⟨8230655352132314523583325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5487103568088209682388883 8230655352132314523583325)
                    ·
                      refine ⟨3086495757049617946343747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230655352132314523583325 3086495757049617946343747)
                      ·
                        rfl

theorem cell23_6010929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_6010929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010929 prefixEnd_6010929 := by exact prefixLift 6010929
  have htrace : WordTrace (prefixWord ++ tailWord_6010929) baseStart_6010929 baseEnd_6010929 := by
    simpa [prefixWord, tailWord_6010929, baseEnd_6010929] using wordTrace_append hprefix tailTrace_6010929
  have hstable : (prefixWord ++ tailWord_6010929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010929).length < 2 ^ (prefixWord ++ tailWord_6010929).sum := by decide
  have hdescent : baseEnd_6010929 < baseStart_6010929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010952 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_6010952 : Nat := 118140960795 + 6010952 * 2 ^ 59
def prefixEnd_6010952 : Nat := 4983230072969 + 3 ^ 40 * 6010952 * 2
def baseEnd_6010952 : Nat := 3086507567104671356356141

theorem tailTrace_6010952 : CollatzResearch.WordTrace tailWord_6010952 prefixEnd_6010952 3086507567104671356356141 := by
  unfold tailWord_6010952
  simp only [CollatzResearch.WordTrace]
  refine ⟨109618715259677483857897555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146158287012903311810530073 109618715259677483857897555)
  ·
    refine ⟨164428072889516225786846333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109618715259677483857897555 164428072889516225786846333)
    ·
      refine ⟨61660527333568584670067375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164428072889516225786846333 61660527333568584670067375)
      ·
        refine ⟨92490791000352877005101063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61660527333568584670067375 92490791000352877005101063)
        ·
          refine ⟨138736186500529315507651595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92490791000352877005101063 138736186500529315507651595)
          ·
            refine ⟨208104279750793973261477393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138736186500529315507651595 208104279750793973261477393)
            ·
              refine ⟨156078209813095479946108045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208104279750793973261477393 156078209813095479946108045)
              ·
                refine ⟨58529328679910804979790517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156078209813095479946108045 58529328679910804979790517)
                ·
                  refine ⟨5487124563741637966855361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58529328679910804979790517 5487124563741637966855361)
                  ·
                    refine ⟨4115343422806228475141521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5487124563741637966855361 4115343422806228475141521)
                    ·
                      refine ⟨3086507567104671356356141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115343422806228475141521 3086507567104671356356141)
                      ·
                        rfl

theorem cell23_6010952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_6010952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010952 prefixEnd_6010952 := by exact prefixLift 6010952
  have htrace : WordTrace (prefixWord ++ tailWord_6010952) baseStart_6010952 baseEnd_6010952 := by
    simpa [prefixWord, tailWord_6010952, baseEnd_6010952] using wordTrace_append hprefix tailTrace_6010952
  have hstable : (prefixWord ++ tailWord_6010952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010952).length < 2 ^ (prefixWord ++ tailWord_6010952).sum := by decide
  have hdescent : baseEnd_6010952 < baseStart_6010952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6010972 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_6010972 : Nat := 118140960795 + 6010972 * 2 ^ 59
def prefixEnd_6010972 : Nat := 4983230072969 + 3 ^ 40 * 6010972 * 2
def baseEnd_6010972 : Nat := 3086517836717761278106049

theorem tailTrace_6010972 : CollatzResearch.WordTrace tailWord_6010972 prefixEnd_6010972 3086517836717761278106049 := by
  unfold tailWord_6010972
  simp only [CollatzResearch.WordTrace]
  refine ⟨109619079989641255565761585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146158773319521674087682113 109619079989641255565761585)
  ·
    refine ⟨82214309992230941674321189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109619079989641255565761585 82214309992230941674321189)
    ·
      refine ⟨15415183123543301563935223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82214309992230941674321189 15415183123543301563935223)
      ·
        refine ⟨23122774685314952345902835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15415183123543301563935223 23122774685314952345902835)
        ·
          refine ⟨34684162027972428518854253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23122774685314952345902835 34684162027972428518854253)
          ·
            refine ⟨13006560760489660694570345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34684162027972428518854253 13006560760489660694570345)
            ·
              refine ⟨9754920570367245520927759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13006560760489660694570345 9754920570367245520927759)
              ·
                refine ⟨14632380855550868281391639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754920570367245520927759 14632380855550868281391639)
                ·
                  refine ⟨21948571283326302422087459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14632380855550868281391639 21948571283326302422087459)
                  ·
                    refine ⟨32922856924989453633131189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21948571283326302422087459 32922856924989453633131189)
                    ·
                      refine ⟨3086517836717761278106049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32922856924989453633131189 3086517836717761278106049)
                      ·
                        rfl

theorem cell23_6010972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_6010972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6010972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6010972 prefixEnd_6010972 := by exact prefixLift 6010972
  have htrace : WordTrace (prefixWord ++ tailWord_6010972) baseStart_6010972 baseEnd_6010972 := by
    simpa [prefixWord, tailWord_6010972, baseEnd_6010972] using wordTrace_append hprefix tailTrace_6010972
  have hstable : (prefixWord ++ tailWord_6010972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6010972).length < 2 ^ (prefixWord ++ tailWord_6010972).sum := by decide
  have hdescent : baseEnd_6010972 < baseStart_6010972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6010972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011008 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_6011008 : Nat := 118140960795 + 6011008 * 2 ^ 59
def prefixEnd_6011008 : Nat := 4983230072969 + 3 ^ 40 * 6011008 * 2
def baseEnd_6011008 : Nat := 3086536322021323137255883

theorem tailTrace_6011008 : CollatzResearch.WordTrace tailWord_6011008 prefixEnd_6011008 3086536322021323137255883 := by
  unfold tailWord_6011008
  simp only [CollatzResearch.WordTrace]
  refine ⟨109619736503576044639916839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146159648671434726186555785 109619736503576044639916839)
  ·
    refine ⟨164429604755364066959875259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109619736503576044639916839 164429604755364066959875259)
    ·
      refine ⟨246644407133046100439812889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164429604755364066959875259 246644407133046100439812889)
      ·
        refine ⟨184983305349784575329859667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246644407133046100439812889 184983305349784575329859667)
        ·
          refine ⟨277474958024676862994789501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184983305349784575329859667 277474958024676862994789501)
          ·
            refine ⟨104053109259253823623046063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277474958024676862994789501 104053109259253823623046063)
            ·
              refine ⟨156079663888880735434569095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104053109259253823623046063 156079663888880735434569095)
              ·
                refine ⟨234119495833321103151853643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156079663888880735434569095 234119495833321103151853643)
                ·
                  refine ⟨351179243749981654727780465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234119495833321103151853643 351179243749981654727780465)
                  ·
                    refine ⟨263384432812486241045835349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351179243749981654727780465 263384432812486241045835349)
                    ·
                      refine ⟨3086536322021323137255883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263384432812486241045835349 3086536322021323137255883)
                      ·
                        rfl

theorem cell23_6011008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_6011008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011008 prefixEnd_6011008 := by exact prefixLift 6011008
  have htrace : WordTrace (prefixWord ++ tailWord_6011008) baseStart_6011008 baseEnd_6011008 := by
    simpa [prefixWord, tailWord_6011008, baseEnd_6011008] using wordTrace_append hprefix tailTrace_6011008
  have hstable : (prefixWord ++ tailWord_6011008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011008).length < 2 ^ (prefixWord ++ tailWord_6011008).sum := by decide
  have hdescent : baseEnd_6011008 < baseStart_6011008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011042 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6011042 : Nat := 118140960795 + 6011042 * 2 ^ 59
def prefixEnd_6011042 : Nat := 4983230072969 + 3 ^ 40 * 6011042 * 2
def baseEnd_6011042 : Nat := 3086553780363576004230727

theorem tailTrace_6011042 : CollatzResearch.WordTrace tailWord_6011042 prefixEnd_6011042 3086553780363576004230727 := by
  unfold tailWord_6011042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54810178272257228271642845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146160475392685942057714253 54810178272257228271642845)
  ·
    refine ⟨20553816852096460601866067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54810178272257228271642845 20553816852096460601866067)
    ·
      refine ⟨30830725278144690902799101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20553816852096460601866067 30830725278144690902799101)
      ·
        refine ⟨11561521979304259088549663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30830725278144690902799101 11561521979304259088549663)
        ·
          refine ⟨17342282968956388632824495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561521979304259088549663 17342282968956388632824495)
          ·
            refine ⟨26013424453434582949236743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342282968956388632824495 26013424453434582949236743)
            ·
              refine ⟨39020136680151874423855115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26013424453434582949236743 39020136680151874423855115)
              ·
                refine ⟨58530205020227811635782673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39020136680151874423855115 58530205020227811635782673)
                ·
                  refine ⟨43897653765170858726837005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58530205020227811635782673 43897653765170858726837005)
                  ·
                    refine ⟨16461620161939072022563877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43897653765170858726837005 16461620161939072022563877)
                    ·
                      refine ⟨3086553780363576004230727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16461620161939072022563877 3086553780363576004230727)
                      ·
                        rfl

theorem cell23_6011042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6011042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011042 prefixEnd_6011042 := by exact prefixLift 6011042
  have htrace : WordTrace (prefixWord ++ tailWord_6011042) baseStart_6011042 baseEnd_6011042 := by
    simpa [prefixWord, tailWord_6011042, baseEnd_6011042] using wordTrace_append hprefix tailTrace_6011042
  have hstable : (prefixWord ++ tailWord_6011042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011042).length < 2 ^ (prefixWord ++ tailWord_6011042).sum := by decide
  have hdescent : baseEnd_6011042 < baseStart_6011042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011045 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_6011045 : Nat := 118140960795 + 6011045 * 2 ^ 59
def prefixEnd_6011045 : Nat := 4983230072969 + 3 ^ 40 * 6011045 * 2
def baseEnd_6011045 : Nat := 3086555320805539492493213

theorem tailTrace_6011045 : CollatzResearch.WordTrace tailWord_6011045 prefixEnd_6011045 3086555320805539492493213 := by
  unfold tailWord_6011045
  simp only [CollatzResearch.WordTrace]
  refine ⟨219240822508018044598930589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146160548338678696399287059 219240822508018044598930589)
  ·
    refine ⟨82215308440506766724598971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219240822508018044598930589 82215308440506766724598971)
    ·
      refine ⟨123322962660760150086898457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82215308440506766724598971 123322962660760150086898457)
      ·
        refine ⟨92492221995570112565173843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123322962660760150086898457 92492221995570112565173843)
        ·
          refine ⟨138738332993355168847760765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92492221995570112565173843 138738332993355168847760765)
          ·
            refine ⟨52026874872508188317910287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138738332993355168847760765 52026874872508188317910287)
            ·
              refine ⟨78040312308762282476865431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52026874872508188317910287 78040312308762282476865431)
              ·
                refine ⟨117060468463143423715298147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78040312308762282476865431 117060468463143423715298147)
                ·
                  refine ⟨175590702694715135572947221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117060468463143423715298147 175590702694715135572947221)
                  ·
                    refine ⟨8230814188814771979981901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175590702694715135572947221 8230814188814771979981901)
                    ·
                      refine ⟨3086555320805539492493213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8230814188814771979981901 3086555320805539492493213)
                      ·
                        rfl

theorem cell23_6011045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_6011045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011045 prefixEnd_6011045 := by exact prefixLift 6011045
  have htrace : WordTrace (prefixWord ++ tailWord_6011045) baseStart_6011045 baseEnd_6011045 := by
    simpa [prefixWord, tailWord_6011045, baseEnd_6011045] using wordTrace_append hprefix tailTrace_6011045
  have hstable : (prefixWord ++ tailWord_6011045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011045).length < 2 ^ (prefixWord ++ tailWord_6011045).sum := by decide
  have hdescent : baseEnd_6011045 < baseStart_6011045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011065 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 7]
def baseStart_6011065 : Nat := 118140960795 + 6011065 * 2 ^ 59
def prefixEnd_6011065 : Nat := 4983230072969 + 3 ^ 40 * 6011065 * 2
def baseEnd_6011065 : Nat := 342951732268736601582569

theorem tailTrace_6011065 : CollatzResearch.WordTrace tailWord_6011065 prefixEnd_6011065 342951732268736601582569 := by
  unfold tailWord_6011065
  simp only [CollatzResearch.WordTrace]
  refine ⟨219241551967945588014658649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146161034645297058676439099 219241551967945588014658649)
  ·
    refine ⟨164431163975959191010993987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219241551967945588014658649 164431163975959191010993987)
    ·
      refine ⟨246646745963938786516490981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164431163975959191010993987 246646745963938786516490981)
      ·
        refine ⟨46246264868238522471842059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246646745963938786516490981 46246264868238522471842059)
        ·
          refine ⟨69369397302357783707763089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46246264868238522471842059 69369397302357783707763089)
          ·
            refine ⟨52027047976768337780822317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69369397302357783707763089 52027047976768337780822317)
            ·
              refine ⟨19510142991288126667808369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52027047976768337780822317 19510142991288126667808369)
              ·
                refine ⟨14632607243466095000856277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19510142991288126667808369 14632607243466095000856277)
                ·
                  refine ⟨342951732268736601582569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14632607243466095000856277 342951732268736601582569)
                  ·
                    rfl

theorem cell23_6011065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_6011065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011065 prefixEnd_6011065 := by exact prefixLift 6011065
  have htrace : WordTrace (prefixWord ++ tailWord_6011065) baseStart_6011065 baseEnd_6011065 := by
    simpa [prefixWord, tailWord_6011065, baseEnd_6011065] using wordTrace_append hprefix tailTrace_6011065
  have hstable : (prefixWord ++ tailWord_6011065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011065).length < 2 ^ (prefixWord ++ tailWord_6011065).sum := by decide
  have hdescent : baseEnd_6011065 < baseStart_6011065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011095 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 4, 5]
def baseStart_6011095 : Nat := 118140960795 + 6011095 * 2 ^ 59
def prefixEnd_6011095 : Nat := 4983230072969 + 3 ^ 40 * 6011095 * 2
def baseEnd_6011095 : Nat := 1028860331612754765622661

theorem tailTrace_6011095 : CollatzResearch.WordTrace tailWord_6011095 prefixEnd_6011095 1028860331612754765622661 := by
  unfold tailWord_6011095
  simp only [CollatzResearch.WordTrace]
  refine ⟨219242646157836903138250739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146161764105224602092167159 219242646157836903138250739)
  ·
    refine ⟨328863969236755354707376109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219242646157836903138250739 328863969236755354707376109)
    ·
      refine ⟨123323988463783258015266041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328863969236755354707376109 123323988463783258015266041)
      ·
        refine ⟨92492991347837443511449531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123323988463783258015266041 92492991347837443511449531)
        ·
          refine ⟨138739487021756165267174297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92492991347837443511449531 138739487021756165267174297)
          ·
            refine ⟨104054615266317123950380723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138739487021756165267174297 104054615266317123950380723)
            ·
              refine ⟨156081922899475685925571085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104054615266317123950380723 156081922899475685925571085)
              ·
                refine ⟨58530721087303382222089157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156081922899475685925571085 58530721087303382222089157)
                ·
                  refine ⟨10974510203869384166641717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58530721087303382222089157 10974510203869384166641717)
                  ·
                    refine ⟨1028860331612754765622661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10974510203869384166641717 1028860331612754765622661)
                    ·
                      rfl

theorem cell23_6011095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_6011095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011095 prefixEnd_6011095 := by exact prefixLift 6011095
  have htrace : WordTrace (prefixWord ++ tailWord_6011095) baseStart_6011095 baseEnd_6011095 := by
    simpa [prefixWord, tailWord_6011095, baseEnd_6011095] using wordTrace_append hprefix tailTrace_6011095
  have hstable : (prefixWord ++ tailWord_6011095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011095).length < 2 ^ (prefixWord ++ tailWord_6011095).sum := by decide
  have hdescent : baseEnd_6011095 < baseStart_6011095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011105 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_6011105 : Nat := 118140960795 + 6011105 * 2 ^ 59
def prefixEnd_6011105 : Nat := 4983230072969 + 3 ^ 40 * 6011105 * 2
def baseEnd_6011105 : Nat := 3086586129644809257742937

theorem tailTrace_6011105 : CollatzResearch.WordTrace tailWord_6011105 prefixEnd_6011105 3086586129644809257742937 := by
  unfold tailWord_6011105
  simp only [CollatzResearch.WordTrace]
  refine ⟨219243010887800674846114769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146162007258533783230743179 219243010887800674846114769)
  ·
    refine ⟨164432258165850506134586077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219243010887800674846114769 164432258165850506134586077)
    ·
      refine ⟨61662096812193939800469779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164432258165850506134586077 61662096812193939800469779)
      ·
        refine ⟨92493145218290909700704669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61662096812193939800469779 92493145218290909700704669)
        ·
          refine ⟨34684929456859091137764251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92493145218290909700704669 34684929456859091137764251)
          ·
            refine ⟨52027394185288636706646377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34684929456859091137764251 52027394185288636706646377)
            ·
              refine ⟨39020545638966477529984783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52027394185288636706646377 39020545638966477529984783)
              ·
                refine ⟨58530818458449716294977175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39020545638966477529984783 58530818458449716294977175)
                ·
                  refine ⟨87796227687674574442465763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58530818458449716294977175 87796227687674574442465763)
                  ·
                    refine ⟨131694341531511861663698645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87796227687674574442465763 131694341531511861663698645)
                    ·
                      refine ⟨3086586129644809257742937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131694341531511861663698645 3086586129644809257742937)
                      ·
                        rfl

theorem cell23_6011105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_6011105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011105 prefixEnd_6011105 := by exact prefixLift 6011105
  have htrace : WordTrace (prefixWord ++ tailWord_6011105) baseStart_6011105 baseEnd_6011105 := by
    simpa [prefixWord, tailWord_6011105, baseEnd_6011105] using wordTrace_append hprefix tailTrace_6011105
  have hstable : (prefixWord ++ tailWord_6011105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011105).length < 2 ^ (prefixWord ++ tailWord_6011105).sum := by decide
  have hdescent : baseEnd_6011105 < baseStart_6011105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011115 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_6011115 : Nat := 118140960795 + 6011115 * 2 ^ 59
def prefixEnd_6011115 : Nat := 4983230072969 + 3 ^ 40 * 6011115 * 2
def baseEnd_6011115 : Nat := 3086591264451354218617891

theorem tailTrace_6011115 : CollatzResearch.WordTrace tailWord_6011115 prefixEnd_6011115 3086591264451354218617891 := by
  unfold tailWord_6011115
  simp only [CollatzResearch.WordTrace]
  refine ⟨219243375617764446553978799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146162250411842964369319199 219243375617764446553978799)
  ·
    refine ⟨328865063426646669830968199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219243375617764446553978799 328865063426646669830968199)
    ·
      refine ⟨493297595139970004746452299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328865063426646669830968199 493297595139970004746452299)
      ·
        refine ⟨739946392709955007119678449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493297595139970004746452299 739946392709955007119678449)
        ·
          refine ⟨554959794532466255339758837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739946392709955007119678449 554959794532466255339758837)
          ·
            refine ⟨52027480737418711438102391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 554959794532466255339758837 52027480737418711438102391)
            ·
              refine ⟨78041221106128067157153587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52027480737418711438102391 78041221106128067157153587)
              ·
                refine ⟨117061831659192100735730381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78041221106128067157153587 117061831659192100735730381)
                ·
                  refine ⟨43898186872197037775898893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117061831659192100735730381 43898186872197037775898893)
                  ·
                    refine ⟨16461820077073889165962085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43898186872197037775898893 16461820077073889165962085)
                    ·
                      refine ⟨3086591264451354218617891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16461820077073889165962085 3086591264451354218617891)
                      ·
                        rfl

theorem cell23_6011115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_6011115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011115 prefixEnd_6011115 := by exact prefixLift 6011115
  have htrace : WordTrace (prefixWord ++ tailWord_6011115) baseStart_6011115 baseEnd_6011115 := by
    simpa [prefixWord, tailWord_6011115, baseEnd_6011115] using wordTrace_append hprefix tailTrace_6011115
  have hstable : (prefixWord ++ tailWord_6011115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011115).length < 2 ^ (prefixWord ++ tailWord_6011115).sum := by decide
  have hdescent : baseEnd_6011115 < baseStart_6011115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011132 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_6011132 : Nat := 118140960795 + 6011132 * 2 ^ 59
def prefixEnd_6011132 : Nat := 4983230072969 + 3 ^ 40 * 6011132 * 2
def baseEnd_6011132 : Nat := 3086599993622480652105313

theorem tailTrace_6011132 : CollatzResearch.WordTrace tailWord_6011132 prefixEnd_6011132 3086599993622480652105313 := by
  unfold tailWord_6011132
  simp only [CollatzResearch.WordTrace]
  refine ⟨109621997829351429228673825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146162663772468572304898433 109621997829351429228673825)
  ·
    refine ⟨82216498372013571921505369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109621997829351429228673825 82216498372013571921505369)
    ·
      refine ⟨61662373779010178941129027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82216498372013571921505369 61662373779010178941129027)
      ·
        refine ⟨92493560668515268411693541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61662373779010178941129027 92493560668515268411693541)
        ·
          refine ⟨17342542625346612827192539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92493560668515268411693541 17342542625346612827192539)
          ·
            refine ⟨26013813938019919240788809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342542625346612827192539 26013813938019919240788809)
            ·
              refine ⟨19510360453514939430591607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26013813938019919240788809 19510360453514939430591607)
              ·
                refine ⟨29265540680272409145887411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19510360453514939430591607 29265540680272409145887411)
                ·
                  refine ⟨43898311020408613718831117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29265540680272409145887411 43898311020408613718831117)
                  ·
                    refine ⟨16461866632653230144561669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43898311020408613718831117 16461866632653230144561669)
                    ·
                      refine ⟨3086599993622480652105313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16461866632653230144561669 3086599993622480652105313)
                      ·
                        rfl

theorem cell23_6011132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_6011132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011132 prefixEnd_6011132 := by exact prefixLift 6011132
  have htrace : WordTrace (prefixWord ++ tailWord_6011132) baseStart_6011132 baseEnd_6011132 := by
    simpa [prefixWord, tailWord_6011132, baseEnd_6011132] using wordTrace_append hprefix tailTrace_6011132
  have hstable : (prefixWord ++ tailWord_6011132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011132).length < 2 ^ (prefixWord ++ tailWord_6011132).sum := by decide
  have hdescent : baseEnd_6011132 < baseStart_6011132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011159 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 3, 4]
def baseStart_6011159 : Nat := 118140960795 + 6011159 * 2 ^ 59
def prefixEnd_6011159 : Nat := 4983230072969 + 3 ^ 40 * 6011159 * 2
def baseEnd_6011159 : Nat := 1028871285866717348822563

theorem tailTrace_6011159 : CollatzResearch.WordTrace tailWord_6011159 prefixEnd_6011159 1028871285866717348822563 := by
  unfold tailWord_6011159
  simp only [CollatzResearch.WordTrace]
  refine ⟨219244980429605042068580531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146163320286403361379053687 219244980429605042068580531)
  ·
    refine ⟨328867470644407563102870797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219244980429605042068580531 328867470644407563102870797)
    ·
      refine ⟨123325301491652836163576549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328867470644407563102870797 123325301491652836163576549)
      ·
        refine ⟨23123494029684906780670603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123325301491652836163576549 23123494029684906780670603)
        ·
          refine ⟨34685241044527360171005905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23123494029684906780670603 34685241044527360171005905)
          ·
            refine ⟨26013930783395520128254429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34685241044527360171005905 26013930783395520128254429)
            ·
              refine ⟨9755224043773320048095411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26013930783395520128254429 9755224043773320048095411)
              ·
                refine ⟨14632836065659980072143117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755224043773320048095411 14632836065659980072143117)
                ·
                  refine ⟨5487313524622492527053669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14632836065659980072143117 5487313524622492527053669)
                  ·
                    refine ⟨1028871285866717348822563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487313524622492527053669 1028871285866717348822563)
                    ·
                      rfl

theorem cell23_6011159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_6011159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011159 prefixEnd_6011159 := by exact prefixLift 6011159
  have htrace : WordTrace (prefixWord ++ tailWord_6011159) baseStart_6011159 baseEnd_6011159 := by
    simpa [prefixWord, tailWord_6011159, baseEnd_6011159] using wordTrace_append hprefix tailTrace_6011159
  have hstable : (prefixWord ++ tailWord_6011159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011159).length < 2 ^ (prefixWord ++ tailWord_6011159).sum := by decide
  have hdescent : baseEnd_6011159 < baseStart_6011159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011186 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_6011186 : Nat := 118140960795 + 6011186 * 2 ^ 59
def prefixEnd_6011186 : Nat := 4983230072969 + 3 ^ 40 * 6011186 * 2
def baseEnd_6011186 : Nat := 3086627721577823440830065

theorem tailTrace_6011186 : CollatzResearch.WordTrace tailWord_6011186 prefixEnd_6011186 3086627721577823440830065 := by
  unfold tailWord_6011186
  simp only [CollatzResearch.WordTrace]
  refine ⟨54811491300126806419953353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146163976800338150453208941 54811491300126806419953353)
  ·
    refine ⟨41108618475095104814965015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54811491300126806419953353 41108618475095104814965015)
    ·
      refine ⟨61662927712642657222447523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41108618475095104814965015 61662927712642657222447523)
      ·
        refine ⟨92494391568963985833671285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61662927712642657222447523 92494391568963985833671285)
        ·
          refine ⟨8671349209590373671906683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92494391568963985833671285 8671349209590373671906683)
          ·
            refine ⟨13007023814385560507860025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671349209590373671906683 13007023814385560507860025)
            ·
              refine ⟨9755267860789170380895019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007023814385560507860025 9755267860789170380895019)
              ·
                refine ⟨14632901791183755571342529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755267860789170380895019 14632901791183755571342529)
                ·
                  refine ⟨10974676343387816678506897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14632901791183755571342529 10974676343387816678506897)
                  ·
                    refine ⟨8231007257540862508880173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10974676343387816678506897 8231007257540862508880173)
                    ·
                      refine ⟨3086627721577823440830065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231007257540862508880173 3086627721577823440830065)
                      ·
                        rfl

theorem cell23_6011186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_6011186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011186 prefixEnd_6011186 := by exact prefixLift 6011186
  have htrace : WordTrace (prefixWord ++ tailWord_6011186) baseStart_6011186 baseEnd_6011186 := by
    simpa [prefixWord, tailWord_6011186, baseEnd_6011186] using wordTrace_append hprefix tailTrace_6011186
  have hstable : (prefixWord ++ tailWord_6011186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011186).length < 2 ^ (prefixWord ++ tailWord_6011186).sum := by decide
  have hdescent : baseEnd_6011186 < baseStart_6011186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011239 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_6011239 : Nat := 118140960795 + 6011239 * 2 ^ 59
def prefixEnd_6011239 : Nat := 4983230072969 + 3 ^ 40 * 6011239 * 2
def baseEnd_6011239 : Nat := 3086654936052511733467321

theorem tailTrace_6011239 : CollatzResearch.WordTrace tailWord_6011239 prefixEnd_6011239 3086654936052511733467321 := by
  unfold tailWord_6011239
  simp only [CollatzResearch.WordTrace]
  refine ⟨219247898269315215731492771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146165265512876810487661847 219247898269315215731492771)
  ·
    refine ⟨328871847403972823597239157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219247898269315215731492771 328871847403972823597239157)
    ·
      refine ⟨30831735694122452212241171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328871847403972823597239157 30831735694122452212241171)
      ·
        refine ⟨46247603541183678318361757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30831735694122452212241171 46247603541183678318361757)
        ·
          refine ⟨17342851327943879369385659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46247603541183678318361757 17342851327943879369385659)
          ·
            refine ⟨26014276991915819054078489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342851327943879369385659 26014276991915819054078489)
            ·
              refine ⟨19510707743936864290558867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26014276991915819054078489 19510707743936864290558867)
              ·
                refine ⟨29266061615905296435838301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19510707743936864290558867 29266061615905296435838301)
                ·
                  refine ⟨10974773105964486163439363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29266061615905296435838301 10974773105964486163439363)
                  ·
                    refine ⟨16462159658946729245159045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10974773105964486163439363 16462159658946729245159045)
                    ·
                      refine ⟨3086654936052511733467321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16462159658946729245159045 3086654936052511733467321)
                      ·
                        rfl

theorem cell23_6011239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_6011239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011239 prefixEnd_6011239 := by exact prefixLift 6011239
  have htrace : WordTrace (prefixWord ++ tailWord_6011239) baseStart_6011239 baseEnd_6011239 := by
    simpa [prefixWord, tailWord_6011239, baseEnd_6011239] using wordTrace_append hprefix tailTrace_6011239
  have hstable : (prefixWord ++ tailWord_6011239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011239).length < 2 ^ (prefixWord ++ tailWord_6011239).sum := by decide
  have hdescent : baseEnd_6011239 < baseStart_6011239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011253 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6011253 : Nat := 118140960795 + 6011253 * 2 ^ 59
def prefixEnd_6011253 : Nat := 4983230072969 + 3 ^ 40 * 6011253 * 2
def baseEnd_6011253 : Nat := 1028887374927224892897419

theorem tailTrace_6011253 : CollatzResearch.WordTrace tailWord_6011253 prefixEnd_6011253 1028887374927224892897419 := by
  unfold tailWord_6011253
  simp only [CollatzResearch.WordTrace]
  refine ⟨219248408891264496122502413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146165605927509664081668275 219248408891264496122502413)
  ·
    refine ⟨82218153334224186045938405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219248408891264496122502413 82218153334224186045938405)
    ·
      refine ⟨15415903750167034883613451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82218153334224186045938405 15415903750167034883613451)
      ·
        refine ⟨23123855625250552325420177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15415903750167034883613451 23123855625250552325420177)
        ·
          refine ⟨17342891718937914244065133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23123855625250552325420177 17342891718937914244065133)
          ·
            refine ⟨6503584394601717841524425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17342891718937914244065133 6503584394601717841524425)
            ·
              refine ⟨4877688295951288381143319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503584394601717841524425 4877688295951288381143319)
              ·
                refine ⟨7316532443926932571714979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877688295951288381143319 7316532443926932571714979)
                ·
                  refine ⟨10974798665890398857572469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316532443926932571714979 10974798665890398857572469)
                  ·
                    refine ⟨1028887374927224892897419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10974798665890398857572469 1028887374927224892897419)
                    ·
                      rfl

theorem cell23_6011253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6011253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011253 prefixEnd_6011253 := by exact prefixLift 6011253
  have htrace : WordTrace (prefixWord ++ tailWord_6011253) baseStart_6011253 baseEnd_6011253 := by
    simpa [prefixWord, tailWord_6011253, baseEnd_6011253] using wordTrace_append hprefix tailTrace_6011253
  have hstable : (prefixWord ++ tailWord_6011253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011253).length < 2 ^ (prefixWord ++ tailWord_6011253).sum := by decide
  have hdescent : baseEnd_6011253 < baseStart_6011253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011273 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 3, 2, 2]
def baseStart_6011273 : Nat := 118140960795 + 6011273 * 2 ^ 59
def prefixEnd_6011273 : Nat := 4983230072969 + 3 ^ 40 * 6011273 * 2
def baseEnd_6011273 : Nat := 3086672394394764600442165

theorem tailTrace_6011273 : CollatzResearch.WordTrace tailWord_6011273 prefixEnd_6011273 3086672394394764600442165 := by
  unfold tailWord_6011273
  simp only [CollatzResearch.WordTrace]
  refine ⟨219249138351192039538230473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146166092234128026358820315 219249138351192039538230473)
  ·
    refine ⟨164436853763394029653672855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219249138351192039538230473 164436853763394029653672855)
    ·
      refine ⟨246655280645091044480509283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164436853763394029653672855 246655280645091044480509283)
      ·
        refine ⟨369982920967636566720763925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246655280645091044480509283 369982920967636566720763925)
        ·
          refine ⟨17342949420357964065035809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 369982920967636566720763925 17342949420357964065035809)
          ·
            refine ⟨13007212065268473048776857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17342949420357964065035809 13007212065268473048776857)
            ·
              refine ⟨9755409048951354786582643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007212065268473048776857 9755409048951354786582643)
              ·
                refine ⟨14633113573427032179873965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755409048951354786582643 14633113573427032179873965)
                ·
                  refine ⟨5487417590035137067452737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14633113573427032179873965 5487417590035137067452737)
                  ·
                    refine ⟨4115563192526352800589553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5487417590035137067452737 4115563192526352800589553)
                    ·
                      refine ⟨3086672394394764600442165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115563192526352800589553 3086672394394764600442165)
                      ·
                        rfl

theorem cell23_6011273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2, 2].length) (baseStart_6011273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011273 prefixEnd_6011273 := by exact prefixLift 6011273
  have htrace : WordTrace (prefixWord ++ tailWord_6011273) baseStart_6011273 baseEnd_6011273 := by
    simpa [prefixWord, tailWord_6011273, baseEnd_6011273] using wordTrace_append hprefix tailTrace_6011273
  have hstable : (prefixWord ++ tailWord_6011273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011273).length < 2 ^ (prefixWord ++ tailWord_6011273).sum := by decide
  have hdescent : baseEnd_6011273 < baseStart_6011273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011293 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_6011293 : Nat := 118140960795 + 6011293 * 2 ^ 59
def prefixEnd_6011293 : Nat := 4983230072969 + 3 ^ 40 * 6011293 * 2
def baseEnd_6011293 : Nat := 3086682664007854522192073

theorem tailTrace_6011293 : CollatzResearch.WordTrace tailWord_6011293 prefixEnd_6011293 3086682664007854522192073 := by
  unfold tailWord_6011293
  simp only [CollatzResearch.WordTrace]
  refine ⟨219249867811119582953958533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146166578540746388635972355 219249867811119582953958533)
  ·
    refine ⟨41109350214584921803867225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219249867811119582953958533 41109350214584921803867225)
    ·
      refine ⟨30832012660938691352900419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41109350214584921803867225 30832012660938691352900419)
      ·
        refine ⟨46248018991408037029350629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30832012660938691352900419 46248018991408037029350629)
        ·
          refine ⟨8671503560889006943003243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46248018991408037029350629 8671503560889006943003243)
          ·
            refine ⟨13007255341333510414504865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671503560889006943003243 13007255341333510414504865)
            ·
              refine ⟨9755441506000132810878649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007255341333510414504865 9755441506000132810878649)
              ·
                refine ⟨7316581129500099608158987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755441506000132810878649 7316581129500099608158987)
                ·
                  refine ⟨10974871694250149412238481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316581129500099608158987 10974871694250149412238481)
                  ·
                    refine ⟨8231153770687612059178861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10974871694250149412238481 8231153770687612059178861)
                    ·
                      refine ⟨3086682664007854522192073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231153770687612059178861 3086682664007854522192073)
                      ·
                        rfl

theorem cell23_6011293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_6011293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011293 prefixEnd_6011293 := by exact prefixLift 6011293
  have htrace : WordTrace (prefixWord ++ tailWord_6011293) baseStart_6011293 baseEnd_6011293 := by
    simpa [prefixWord, tailWord_6011293, baseEnd_6011293] using wordTrace_append hprefix tailTrace_6011293
  have hstable : (prefixWord ++ tailWord_6011293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011293).length < 2 ^ (prefixWord ++ tailWord_6011293).sum := by decide
  have hdescent : baseEnd_6011293 < baseStart_6011293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011322 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_6011322 : Nat := 118140960795 + 6011322 * 2 ^ 59
def prefixEnd_6011322 : Nat := 4983230072969 + 3 ^ 40 * 6011322 * 2
def baseEnd_6011322 : Nat := 1028899184982278302909813

theorem tailTrace_6011322 : CollatzResearch.WordTrace tailWord_6011322 prefixEnd_6011322 1028899184982278302909813 := by
  unfold tailWord_6011322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54812731382003630226691055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146167283685343013937842813 54812731382003630226691055)
  ·
    refine ⟨82219097073005445340036583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54812731382003630226691055 82219097073005445340036583)
    ·
      refine ⟨123328645609508168010054875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82219097073005445340036583 123328645609508168010054875)
      ·
        refine ⟨184992968414262252015082313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123328645609508168010054875 184992968414262252015082313)
        ·
          refine ⟨138744726310696689011311735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184992968414262252015082313 138744726310696689011311735)
          ·
            refine ⟨208117089466045033516967603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138744726310696689011311735 208117089466045033516967603)
            ·
              refine ⟨312175634199067550275451405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208117089466045033516967603 312175634199067550275451405)
              ·
                refine ⟨117065862824650331353294277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312175634199067550275451405 117065862824650331353294277)
                ·
                  refine ⟨21949849279621937128742677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117065862824650331353294277 21949849279621937128742677)
                  ·
                    refine ⟨1028899184982278302909813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21949849279621937128742677 1028899184982278302909813)
                    ·
                      rfl

theorem cell23_6011322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_6011322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011322 prefixEnd_6011322 := by exact prefixLift 6011322
  have htrace : WordTrace (prefixWord ++ tailWord_6011322) baseStart_6011322 baseEnd_6011322 := by
    simpa [prefixWord, tailWord_6011322, baseEnd_6011322] using wordTrace_append hprefix tailTrace_6011322
  have hstable : (prefixWord ++ tailWord_6011322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011322).length < 2 ^ (prefixWord ++ tailWord_6011322).sum := by decide
  have hdescent : baseEnd_6011322 < baseStart_6011322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011349 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6011349 : Nat := 118140960795 + 6011349 * 2 ^ 59
def prefixEnd_6011349 : Nat := 4983230072969 + 3 ^ 40 * 6011349 * 2
def baseEnd_6011349 : Nat := 3086711418924506303091815

theorem tailTrace_6011349 : CollatzResearch.WordTrace tailWord_6011349 prefixEnd_6011349 3086711418924506303091815 := by
  unfold tailWord_6011349
  simp only [CollatzResearch.WordTrace]
  refine ⟨219251910298916704517997101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146167940199277803011998067 219251910298916704517997101)
  ·
    refine ⟨82219466362093764194248913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219251910298916704517997101 82219466362093764194248913)
    ·
      refine ⟨61664599771570323145686685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82219466362093764194248913 61664599771570323145686685)
      ·
        refine ⟨23124224914338871179632507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61664599771570323145686685 23124224914338871179632507)
        ·
          refine ⟨34686337371508306769448761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23124224914338871179632507 34686337371508306769448761)
          ·
            refine ⟨26014753028631230077086571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34686337371508306769448761 26014753028631230077086571)
            ·
              refine ⟨39022129542946845115629857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26014753028631230077086571 39022129542946845115629857)
              ·
                refine ⟨29266597157210133836722393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39022129542946845115629857 29266597157210133836722393)
                ·
                  refine ⟨21949947867907600377541795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29266597157210133836722393 21949947867907600377541795)
                  ·
                    refine ⟨32924921801861400566312693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21949947867907600377541795 32924921801861400566312693)
                    ·
                      refine ⟨3086711418924506303091815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32924921801861400566312693 3086711418924506303091815)
                      ·
                        rfl

theorem cell23_6011349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6011349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011349 prefixEnd_6011349 := by exact prefixLift 6011349
  have htrace : WordTrace (prefixWord ++ tailWord_6011349) baseStart_6011349 baseEnd_6011349 := by
    simpa [prefixWord, tailWord_6011349, baseEnd_6011349] using wordTrace_append hprefix tailTrace_6011349
  have hstable : (prefixWord ++ tailWord_6011349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011349).length < 2 ^ (prefixWord ++ tailWord_6011349).sum := by decide
  have hdescent : baseEnd_6011349 < baseStart_6011349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011352 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 9]
def baseStart_6011352 : Nat := 118140960795 + 6011352 * 2 ^ 59
def prefixEnd_6011352 : Nat := 4983230072969 + 3 ^ 40 * 6011352 * 2
def baseEnd_6011352 : Nat := 342968106596274421261589

theorem tailTrace_6011352 : CollatzResearch.WordTrace tailWord_6011352 prefixEnd_6011352 342968106596274421261589 := by
  unfold tailWord_6011352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109626009858952918015178155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146168013145270557353570873 109626009858952918015178155)
  ·
    refine ⟨164439014788429377022767233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109626009858952918015178155 164439014788429377022767233)
    ·
      refine ⟨123329261091322032767075425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164439014788429377022767233 123329261091322032767075425)
      ·
        refine ⟨92496945818491524575306569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123329261091322032767075425 92496945818491524575306569)
        ·
          refine ⟨69372709363868643431479927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92496945818491524575306569 69372709363868643431479927)
          ·
            refine ⟨104059064045802965147219891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69372709363868643431479927 104059064045802965147219891)
            ·
              refine ⟨156088596068704447720829837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104059064045802965147219891 156088596068704447720829837)
              ·
                refine ⟨58533223525764167895311189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156088596068704447720829837 58533223525764167895311189)
                ·
                  refine ⟨342968106596274421261589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58533223525764167895311189 342968106596274421261589)
                  ·
                    rfl

theorem cell23_6011352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_6011352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011352 prefixEnd_6011352 := by exact prefixLift 6011352
  have htrace : WordTrace (prefixWord ++ tailWord_6011352) baseStart_6011352 baseEnd_6011352 := by
    simpa [prefixWord, tailWord_6011352, baseEnd_6011352] using wordTrace_append hprefix tailTrace_6011352
  have hstable : (prefixWord ++ tailWord_6011352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011352).length < 2 ^ (prefixWord ++ tailWord_6011352).sum := by decide
  have hdescent : baseEnd_6011352 < baseStart_6011352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011363 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6011363 : Nat := 118140960795 + 6011363 * 2 ^ 59
def prefixEnd_6011363 : Nat := 4983230072969 + 3 ^ 40 * 6011363 * 2
def baseEnd_6011363 : Nat := 3086718607653669248316751

theorem tailTrace_6011363 : CollatzResearch.WordTrace tailWord_6011363 prefixEnd_6011363 3086718607653669248316751 := by
  unfold tailWord_6011363
  simp only [CollatzResearch.WordTrace]
  refine ⟨219252420920865984909006743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146168280613910656606004495 219252420920865984909006743)
  ·
    refine ⟨328878631381298977363510115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219252420920865984909006743 328878631381298977363510115)
    ·
      refine ⟨493317947071948466045265173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328878631381298977363510115 493317947071948466045265173)
      ·
        refine ⟨23124278768997584345871805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 493317947071948466045265173 23124278768997584345871805)
        ·
          refine ⟨8671604538374094129701927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23124278768997584345871805 8671604538374094129701927)
          ·
            refine ⟨13007406807561141194552891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671604538374094129701927 13007406807561141194552891)
            ·
              refine ⟨19511110211341711791829337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13007406807561141194552891 19511110211341711791829337)
              ·
                refine ⟨14633332658506283843872003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19511110211341711791829337 14633332658506283843872003)
                ·
                  refine ⟨21949998987759425765808005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14633332658506283843872003 21949998987759425765808005)
                  ·
                    refine ⟨4115624810204892331089001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21949998987759425765808005 4115624810204892331089001)
                    ·
                      refine ⟨3086718607653669248316751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115624810204892331089001 3086718607653669248316751)
                      ·
                        rfl

theorem cell23_6011363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6011363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011363 prefixEnd_6011363 := by exact prefixLift 6011363
  have htrace : WordTrace (prefixWord ++ tailWord_6011363) baseStart_6011363 baseEnd_6011363 := by
    simpa [prefixWord, tailWord_6011363, baseEnd_6011363] using wordTrace_append hprefix tailTrace_6011363
  have hstable : (prefixWord ++ tailWord_6011363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011363).length < 2 ^ (prefixWord ++ tailWord_6011363).sum := by decide
  have hdescent : baseEnd_6011363 < baseStart_6011363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011379 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3]
def baseStart_6011379 : Nat := 118140960795 + 6011379 * 2 ^ 59
def prefixEnd_6011379 : Nat := 4983230072969 + 3 ^ 40 * 6011379 * 2
def baseEnd_6011379 : Nat := 3086726823344141185716677

theorem tailTrace_6011379 : CollatzResearch.WordTrace tailWord_6011379 prefixEnd_6011379 3086726823344141185716677 := by
  unfold tailWord_6011379
  simp only [CollatzResearch.WordTrace]
  refine ⟨219253004488808019641589191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146168669659205346427726127 219253004488808019641589191)
  ·
    refine ⟨328879506733212029462383787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219253004488808019641589191 328879506733212029462383787)
    ·
      refine ⟨493319260099818044193575681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328879506733212029462383787 493319260099818044193575681)
      ·
        refine ⟨369989445074863533145181761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493319260099818044193575681 369989445074863533145181761)
        ·
          refine ⟨277492083806147649858886321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369989445074863533145181761 277492083806147649858886321)
          ·
            refine ⟨208119062854610737394164741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277492083806147649858886321 208119062854610737394164741)
            ·
              refine ⟨39022324285239513261405889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208119062854610737394164741 39022324285239513261405889)
              ·
                refine ⟨29266743213929634946054417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39022324285239513261405889 29266743213929634946054417)
                ·
                  refine ⟨21950057410447226209540813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29266743213929634946054417 21950057410447226209540813)
                  ·
                    refine ⟨8231271528917709828577805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21950057410447226209540813 8231271528917709828577805)
                    ·
                      refine ⟨3086726823344141185716677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231271528917709828577805 3086726823344141185716677)
                      ·
                        rfl

theorem cell23_6011379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_6011379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011379 prefixEnd_6011379 := by exact prefixLift 6011379
  have htrace : WordTrace (prefixWord ++ tailWord_6011379) baseStart_6011379 baseEnd_6011379 := by
    simpa [prefixWord, tailWord_6011379, baseEnd_6011379] using wordTrace_append hprefix tailTrace_6011379
  have hstable : (prefixWord ++ tailWord_6011379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011379).length < 2 ^ (prefixWord ++ tailWord_6011379).sum := by decide
  have hdescent : baseEnd_6011379 < baseStart_6011379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011396 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6011396 : Nat := 118140960795 + 6011396 * 2 ^ 59
def prefixEnd_6011396 : Nat := 4983230072969 + 3 ^ 40 * 6011396 * 2
def baseEnd_6011396 : Nat := 3086735552515267619204099

theorem tailTrace_6011396 : CollatzResearch.WordTrace tailWord_6011396 prefixEnd_6011396 3086735552515267619204099 := by
  unfold tailWord_6011396
  simp only [CollatzResearch.WordTrace]
  refine ⟨109626812264873215772479021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146169083019830954363305361 109626812264873215772479021)
  ·
    refine ⟨41110054599327455914679633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109626812264873215772479021 41110054599327455914679633)
    ·
      refine ⟨30832540949495591936009725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41110054599327455914679633 30832540949495591936009725)
      ·
        refine ⟨11562202856060846976003647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30832540949495591936009725 11562202856060846976003647)
        ·
          refine ⟨17343304284091270464005471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562202856060846976003647 17343304284091270464005471)
          ·
            refine ⟨26014956426136905696008207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17343304284091270464005471 26014956426136905696008207)
            ·
              refine ⟨39022434639205358544012311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26014956426136905696008207 39022434639205358544012311)
              ·
                refine ⟨58533651958808037816018467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39022434639205358544012311 58533651958808037816018467)
                ·
                  refine ⟨87800477938212056724027701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58533651958808037816018467 87800477938212056724027701)
                  ·
                    refine ⟨8231294806707380317877597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87800477938212056724027701 8231294806707380317877597)
                    ·
                      refine ⟨3086735552515267619204099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231294806707380317877597 3086735552515267619204099)
                      ·
                        rfl

theorem cell23_6011396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6011396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011396 prefixEnd_6011396 := by exact prefixLift 6011396
  have htrace : WordTrace (prefixWord ++ tailWord_6011396) baseStart_6011396 baseEnd_6011396 := by
    simpa [prefixWord, tailWord_6011396, baseEnd_6011396] using wordTrace_append hprefix tailTrace_6011396
  have hstable : (prefixWord ++ tailWord_6011396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011396).length < 2 ^ (prefixWord ++ tailWord_6011396).sum := by decide
  have hdescent : baseEnd_6011396 < baseStart_6011396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011416 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_6011416 : Nat := 118140960795 + 6011416 * 2 ^ 59
def prefixEnd_6011416 : Nat := 4983230072969 + 3 ^ 40 * 6011416 * 2
def baseEnd_6011416 : Nat := 1028915274042785846984669

theorem tailTrace_6011416 : CollatzResearch.WordTrace tailWord_6011416 prefixEnd_6011416 1028915274042785846984669 := by
  unfold tailWord_6011416
  simp only [CollatzResearch.WordTrace]
  refine ⟨109627176994836987480343051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146169569326449316640457401 109627176994836987480343051)
  ·
    refine ⟨164440765492255481220514577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109627176994836987480343051 164440765492255481220514577)
    ·
      refine ⟨123330574119191610915385933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164440765492255481220514577 123330574119191610915385933)
      ·
        refine ⟨46248965294696854093269725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123330574119191610915385933 46248965294696854093269725)
        ·
          refine ⟨17343361985511320284976147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46248965294696854093269725 17343361985511320284976147)
          ·
            refine ⟨26015042978266980427464221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17343361985511320284976147 26015042978266980427464221)
            ·
              refine ⟨9755641116850117660299083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26015042978266980427464221 9755641116850117660299083)
              ·
                refine ⟨14633461675275176490448625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755641116850117660299083 14633461675275176490448625)
                ·
                  refine ⟨10975096256456382367836469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14633461675275176490448625 10975096256456382367836469)
                  ·
                    refine ⟨1028915274042785846984669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10975096256456382367836469 1028915274042785846984669)
                    ·
                      rfl

theorem cell23_6011416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_6011416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011416 prefixEnd_6011416 := by exact prefixLift 6011416
  have htrace : WordTrace (prefixWord ++ tailWord_6011416) baseStart_6011416 baseEnd_6011416 := by
    simpa [prefixWord, tailWord_6011416, baseEnd_6011416] using wordTrace_append hprefix tailTrace_6011416
  have hstable : (prefixWord ++ tailWord_6011416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011416).length < 2 ^ (prefixWord ++ tailWord_6011416).sum := by decide
  have hdescent : baseEnd_6011416 < baseStart_6011416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011431 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6011431 : Nat := 118140960795 + 6011431 * 2 ^ 59
def prefixEnd_6011431 : Nat := 4983230072969 + 3 ^ 40 * 6011431 * 2
def baseEnd_6011431 : Nat := 3086753524338174982266439

theorem tailTrace_6011431 : CollatzResearch.WordTrace tailWord_6011431 prefixEnd_6011431 3086753524338174982266439 := by
  unfold tailWord_6011431
  simp only [CollatzResearch.WordTrace]
  refine ⟨219254901084619632522482147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146169934056413088348321431 219254901084619632522482147)
  ·
    refine ⟨328882351626929448783723221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219254901084619632522482147 328882351626929448783723221)
    ·
      refine ⟨7708180116256158955868513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 328882351626929448783723221 7708180116256158955868513)
      ·
        refine ⟨5781135087192119216901385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708180116256158955868513 5781135087192119216901385)
        ·
          refine ⟨4335851315394089412676039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5781135087192119216901385 4335851315394089412676039)
          ·
            refine ⟨6503776973091134119014059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335851315394089412676039 6503776973091134119014059)
            ·
              refine ⟨9755665459636701178521089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503776973091134119014059 9755665459636701178521089)
              ·
                refine ⟨7316749094727525883890817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755665459636701178521089 7316749094727525883890817)
                ·
                  refine ⟨5487561821045644412918113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7316749094727525883890817 5487561821045644412918113)
                  ·
                    refine ⟨4115671365784233309688585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5487561821045644412918113 4115671365784233309688585)
                    ·
                      refine ⟨3086753524338174982266439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115671365784233309688585 3086753524338174982266439)
                      ·
                        rfl

theorem cell23_6011431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6011431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011431 prefixEnd_6011431 := by exact prefixLift 6011431
  have htrace : WordTrace (prefixWord ++ tailWord_6011431) baseStart_6011431 baseEnd_6011431 := by
    simpa [prefixWord, tailWord_6011431, baseEnd_6011431] using wordTrace_append hprefix tailTrace_6011431
  have hstable : (prefixWord ++ tailWord_6011431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011431).length < 2 ^ (prefixWord ++ tailWord_6011431).sum := by decide
  have hdescent : baseEnd_6011431 < baseStart_6011431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011449 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6011449 : Nat := 118140960795 + 6011449 * 2 ^ 59
def prefixEnd_6011449 : Nat := 4983230072969 + 3 ^ 40 * 6011449 * 2
def baseEnd_6011449 : Nat := 3086762766989955911841355

theorem tailTrace_6011449 : CollatzResearch.WordTrace tailWord_6011449 prefixEnd_6011449 3086762766989955911841355 := by
  unfold tailWord_6011449
  simp only [CollatzResearch.WordTrace]
  refine ⟨219255557598554421596637401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146170371732369614397758267 219255557598554421596637401)
  ·
    refine ⟨164441668198915816197478051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219255557598554421596637401 164441668198915816197478051)
    ·
      refine ⟨246662502298373724296217077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164441668198915816197478051 246662502298373724296217077)
      ·
        refine ⟨23124609590472536652770351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246662502298373724296217077 23124609590472536652770351)
        ·
          refine ⟨34686914385708804979155527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23124609590472536652770351 34686914385708804979155527)
          ·
            refine ⟨52030371578563207468733291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34686914385708804979155527 52030371578563207468733291)
            ·
              refine ⟨78045557367844811203099937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52030371578563207468733291 78045557367844811203099937)
              ·
                refine ⟨58534168025883608402324953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78045557367844811203099937 58534168025883608402324953)
                ·
                  refine ⟨43900626019412706301743715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58534168025883608402324953 43900626019412706301743715)
                  ·
                    refine ⟨65850939029119059452615573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43900626019412706301743715 65850939029119059452615573)
                    ·
                      refine ⟨3086762766989955911841355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65850939029119059452615573 3086762766989955911841355)
                      ·
                        rfl

theorem cell23_6011449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6011449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011449 prefixEnd_6011449 := by exact prefixLift 6011449
  have htrace : WordTrace (prefixWord ++ tailWord_6011449) baseStart_6011449 baseEnd_6011449 := by
    simpa [prefixWord, tailWord_6011449, baseEnd_6011449] using wordTrace_append hprefix tailTrace_6011449
  have hstable : (prefixWord ++ tailWord_6011449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011449).length < 2 ^ (prefixWord ++ tailWord_6011449).sum := by decide
  have hdescent : baseEnd_6011449 < baseStart_6011449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011453 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6011453 : Nat := 118140960795 + 6011453 * 2 ^ 59
def prefixEnd_6011453 : Nat := 4983230072969 + 3 ^ 40 * 6011453 * 2
def baseEnd_6011453 : Nat := 3086764820912573896191337

theorem tailTrace_6011453 : CollatzResearch.WordTrace tailWord_6011453 prefixEnd_6011453 3086764820912573896191337 := by
  unfold tailWord_6011453
  simp only [CollatzResearch.WordTrace]
  refine ⟨219255703490539930279783013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146170468993693286853188675 219255703490539930279783013)
  ·
    refine ⟨41110444404476236927459315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219255703490539930279783013 41110444404476236927459315)
    ·
      refine ⟨61665666606714355391188973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41110444404476236927459315 61665666606714355391188973)
      ·
        refine ⟨23124624977517883271695865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61665666606714355391188973 23124624977517883271695865)
        ·
          refine ⟨17343468733138412453771899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23124624977517883271695865 17343468733138412453771899)
          ·
            refine ⟨26015203099707618680657849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17343468733138412453771899 26015203099707618680657849)
            ·
              refine ⟨19511402324780714010493387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26015203099707618680657849 19511402324780714010493387)
              ·
                refine ⟨29267103487171071015740081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19511402324780714010493387 29267103487171071015740081)
                ·
                  refine ⟨21950327615378303261805061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29267103487171071015740081 21950327615378303261805061)
                  ·
                    refine ⟨4115686427883431861588449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21950327615378303261805061 4115686427883431861588449)
                    ·
                      refine ⟨3086764820912573896191337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115686427883431861588449 3086764820912573896191337)
                      ·
                        rfl

theorem cell23_6011453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6011453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011453 prefixEnd_6011453 := by exact prefixLift 6011453
  have htrace : WordTrace (prefixWord ++ tailWord_6011453) baseStart_6011453 baseEnd_6011453 := by
    simpa [prefixWord, tailWord_6011453, baseEnd_6011453] using wordTrace_append hprefix tailTrace_6011453
  have hstable : (prefixWord ++ tailWord_6011453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011453).length < 2 ^ (prefixWord ++ tailWord_6011453).sum := by decide
  have hdescent : baseEnd_6011453 < baseStart_6011453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011459 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 6]
def baseStart_6011459 : Nat := 118140960795 + 6011459 * 2 ^ 59
def prefixEnd_6011459 : Nat := 4983230072969 + 3 ^ 40 * 6011459 * 2
def baseEnd_6011459 : Nat := 342974211310722319190701

theorem tailTrace_6011459 : CollatzResearch.WordTrace tailWord_6011459 prefixEnd_6011459 342974211310722319190701 := by
  unfold tailWord_6011459
  simp only [CollatzResearch.WordTrace]
  refine ⟨219255922328518193304501431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146170614885678795536334287 219255922328518193304501431)
  ·
    refine ⟨328883883492777289956752147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219255922328518193304501431 328883883492777289956752147)
    ·
      refine ⟨493325825239165934935128221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328883883492777289956752147 493325825239165934935128221)
      ·
        refine ⟨184997184464687225600673083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493325825239165934935128221 184997184464687225600673083)
        ·
          refine ⟨277495776697030838401009625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184997184464687225600673083 277495776697030838401009625)
          ·
            refine ⟨208121832522773128800757219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277495776697030838401009625 208121832522773128800757219)
            ·
              refine ⟨312182748784159693201135829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208121832522773128800757219 312182748784159693201135829)
              ·
                refine ⟨7316783174628742809401621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 312182748784159693201135829 7316783174628742809401621)
                ·
                  refine ⟨342974211310722319190701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7316783174628742809401621 342974211310722319190701)
                  ·
                    rfl

theorem cell23_6011459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 6].length) (baseStart_6011459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011459 prefixEnd_6011459 := by exact prefixLift 6011459
  have htrace : WordTrace (prefixWord ++ tailWord_6011459) baseStart_6011459 baseEnd_6011459 := by
    simpa [prefixWord, tailWord_6011459, baseEnd_6011459] using wordTrace_append hprefix tailTrace_6011459
  have hstable : (prefixWord ++ tailWord_6011459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011459).length < 2 ^ (prefixWord ++ tailWord_6011459).sum := by decide
  have hdescent : baseEnd_6011459 < baseStart_6011459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011503 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 3]
def baseStart_6011503 : Nat := 118140960795 + 6011503 * 2 ^ 59
def prefixEnd_6011503 : Nat := 4983230072969 + 3 ^ 40 * 6011503 * 2
def baseEnd_6011503 : Nat := 3086790494945298700566107

theorem tailTrace_6011503 : CollatzResearch.WordTrace tailWord_6011503 prefixEnd_6011503 3086790494945298700566107 := by
  unfold tailWord_6011503
  simp only [CollatzResearch.WordTrace]
  refine ⟨219257527140358788819103163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146171684760239192546068775 219257527140358788819103163)
  ·
    refine ⟨328886290710538183228654745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219257527140358788819103163 328886290710538183228654745)
    ·
      refine ⟨246664718032903637421491059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328886290710538183228654745 246664718032903637421491059)
      ·
        refine ⟨369997077049355456132236589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246664718032903637421491059 369997077049355456132236589)
        ·
          refine ⟨138748903893508296049588721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369997077049355456132236589 138748903893508296049588721)
          ·
            refine ⟨104061677920131222037191541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138748903893508296049588721 104061677920131222037191541)
            ·
              refine ⟨9755782305012302065986707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104061677920131222037191541 9755782305012302065986707)
              ·
                refine ⟨14633673457518453098980061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755782305012302065986707 14633673457518453098980061)
                ·
                  refine ⟨5487627546569419912117523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14633673457518453098980061 5487627546569419912117523)
                  ·
                    refine ⟨8231441319854129868176285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5487627546569419912117523 8231441319854129868176285)
                    ·
                      refine ⟨3086790494945298700566107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231441319854129868176285 3086790494945298700566107)
                      ·
                        rfl

theorem cell23_6011503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_6011503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011503 prefixEnd_6011503 := by exact prefixLift 6011503
  have htrace : WordTrace (prefixWord ++ tailWord_6011503) baseStart_6011503 baseEnd_6011503 := by
    simpa [prefixWord, tailWord_6011503, baseEnd_6011503] using wordTrace_append hprefix tailTrace_6011503
  have hstable : (prefixWord ++ tailWord_6011503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011503).length < 2 ^ (prefixWord ++ tailWord_6011503).sum := by decide
  have hdescent : baseEnd_6011503 < baseStart_6011503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011556 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_6011556 : Nat := 118140960795 + 6011556 * 2 ^ 59
def prefixEnd_6011556 : Nat := 4983230072969 + 3 ^ 40 * 6011556 * 2
def baseEnd_6011556 : Nat := 3086817709419986993203363

theorem tailTrace_6011556 : CollatzResearch.WordTrace tailWord_6011556 prefixEnd_6011556 3086817709419986993203363 := by
  unfold tailWord_6011556
  simp only [CollatzResearch.WordTrace]
  refine ⟨109629730104583389435391261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146172973472777852580521681 109629730104583389435391261)
  ·
    refine ⟨41111148789218771038271723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109629730104583389435391261 41111148789218771038271723)
    ·
      refine ⟨61666723183828156557407585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41111148789218771038271723 61666723183828156557407585)
      ·
        refine ⟨46250042387871117418055689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61666723183828156557407585 46250042387871117418055689)
        ·
          refine ⟨34687531790903338063541767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46250042387871117418055689 34687531790903338063541767)
          ·
            refine ⟨52031297686355007095312651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34687531790903338063541767 52031297686355007095312651)
            ·
              refine ⟨78046946529532510642968977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52031297686355007095312651 78046946529532510642968977)
              ·
                refine ⟨58535209897149382982226733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78046946529532510642968977 58535209897149382982226733)
                ·
                  refine ⟨21950703711431018618335025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58535209897149382982226733 21950703711431018618335025)
                  ·
                    refine ⟨16463027783573263963751269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21950703711431018618335025 16463027783573263963751269)
                    ·
                      refine ⟨3086817709419986993203363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16463027783573263963751269 3086817709419986993203363)
                      ·
                        rfl

theorem cell23_6011556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_6011556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011556 prefixEnd_6011556 := by exact prefixLift 6011556
  have htrace : WordTrace (prefixWord ++ tailWord_6011556) baseStart_6011556 baseEnd_6011556 := by
    simpa [prefixWord, tailWord_6011556, baseEnd_6011556] using wordTrace_append hprefix tailTrace_6011556
  have hstable : (prefixWord ++ tailWord_6011556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011556).length < 2 ^ (prefixWord ++ tailWord_6011556).sum := by decide
  have hdescent : baseEnd_6011556 < baseStart_6011556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011573 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6011573 : Nat := 118140960795 + 6011573 * 2 ^ 59
def prefixEnd_6011573 : Nat := 4983230072969 + 3 ^ 40 * 6011573 * 2
def baseEnd_6011573 : Nat := 3086826438591113426690785

theorem tailTrace_6011573 : CollatzResearch.WordTrace tailWord_6011573 prefixEnd_6011573 3086826438591113426690785 := by
  unfold tailWord_6011573
  simp only [CollatzResearch.WordTrace]
  refine ⟨219260080250105190774151373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146173386833403460516100915 219260080250105190774151373)
  ·
    refine ⟨82222530093789446540306765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219260080250105190774151373 82222530093789446540306765)
    ·
      refine ⟨30833448785171042452615037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82222530093789446540306765 30833448785171042452615037)
      ·
        refine ⟨11562543294439140919730639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30833448785171042452615037 11562543294439140919730639)
        ·
          refine ⟨17343814941658711379595959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562543294439140919730639 17343814941658711379595959)
          ·
            refine ⟨26015722412488067069393939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17343814941658711379595959 26015722412488067069393939)
            ·
              refine ⟨39023583618732100604090909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26015722412488067069393939 39023583618732100604090909)
              ·
                refine ⟨14633843857024537726534091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39023583618732100604090909 14633843857024537726534091)
                ·
                  refine ⟨21950765785536806589801137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14633843857024537726534091 21950765785536806589801137)
                  ·
                    refine ⟨16463074339152604942350853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21950765785536806589801137 16463074339152604942350853)
                    ·
                      refine ⟨3086826438591113426690785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16463074339152604942350853 3086826438591113426690785)
                      ·
                        rfl

theorem cell23_6011573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6011573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011573 prefixEnd_6011573 := by exact prefixLift 6011573
  have htrace : WordTrace (prefixWord ++ tailWord_6011573) baseStart_6011573 baseEnd_6011573 := by
    simpa [prefixWord, tailWord_6011573, baseEnd_6011573] using wordTrace_append hprefix tailTrace_6011573
  have hstable : (prefixWord ++ tailWord_6011573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011573).length < 2 ^ (prefixWord ++ tailWord_6011573).sum := by decide
  have hdescent : baseEnd_6011573 < baseStart_6011573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011594 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_6011594 : Nat := 118140960795 + 6011594 * 2 ^ 59
def prefixEnd_6011594 : Nat := 4983230072969 + 3 ^ 40 * 6011594 * 2
def baseEnd_6011594 : Nat := 3086837221684857844528189

theorem tailTrace_6011594 : CollatzResearch.WordTrace tailWord_6011594 prefixEnd_6011594 3086837221684857844528189 := by
  unfold tailWord_6011594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54815211545757277840166459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146173897455352740907110557 54815211545757277840166459)
  ·
    refine ⟨82222817318635916760249689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54815211545757277840166459 82222817318635916760249689)
    ·
      refine ⟨61667112988976937570187267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82222817318635916760249689 61667112988976937570187267)
      ·
        refine ⟨92500669483465406355280901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61667112988976937570187267 92500669483465406355280901)
        ·
          refine ⟨17343875528149763691615169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92500669483465406355280901 17343875528149763691615169)
          ·
            refine ⟨13007906646112322768711377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17343875528149763691615169 13007906646112322768711377)
            ·
              refine ⟨9755929984584242076533533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007906646112322768711377 9755929984584242076533533)
              ·
                refine ⟨3658473744219090778700075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9755929984584242076533533 3658473744219090778700075)
                ·
                  refine ⟨5487710616328636168050113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658473744219090778700075 5487710616328636168050113)
                  ·
                    refine ⟨4115782962246477126037585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5487710616328636168050113 4115782962246477126037585)
                    ·
                      refine ⟨3086837221684857844528189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115782962246477126037585 3086837221684857844528189)
                      ·
                        rfl

theorem cell23_6011594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_6011594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011594 prefixEnd_6011594 := by exact prefixLift 6011594
  have htrace : WordTrace (prefixWord ++ tailWord_6011594) baseStart_6011594 baseEnd_6011594 := by
    simpa [prefixWord, tailWord_6011594, baseEnd_6011594] using wordTrace_append hprefix tailTrace_6011594
  have hstable : (prefixWord ++ tailWord_6011594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011594).length < 2 ^ (prefixWord ++ tailWord_6011594).sum := by decide
  have hdescent : baseEnd_6011594 < baseStart_6011594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011604 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_6011604 : Nat := 118140960795 + 6011604 * 2 ^ 59
def prefixEnd_6011604 : Nat := 4983230072969 + 3 ^ 40 * 6011604 * 2
def baseEnd_6011604 : Nat := 1028947452163800935134381

theorem tailTrace_6011604 : CollatzResearch.WordTrace tailWord_6011604 prefixEnd_6011604 1028947452163800935134381 := by
  unfold tailWord_6011604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109630605456496441534264933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146174140608661922045686577 109630605456496441534264933)
  ·
    refine ⟨20555738523093082787674675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109630605456496441534264933 20555738523093082787674675)
    ·
      refine ⟨30833607784639624181512013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20555738523093082787674675 30833607784639624181512013)
      ·
        refine ⟨11562602919239859068067005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30833607784639624181512013 11562602919239859068067005)
        ·
          refine ⟨4335976094714947150525127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11562602919239859068067005 4335976094714947150525127)
          ·
            refine ⟨6503964142072420725787691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335976094714947150525127 6503964142072420725787691)
            ·
              refine ⟨9755946213108631088681537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503964142072420725787691 9755946213108631088681537)
              ·
                refine ⟨7316959659831473316511153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755946213108631088681537 7316959659831473316511153)
                ·
                  refine ⟨5487719744873604987383365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7316959659831473316511153 5487719744873604987383365)
                  ·
                    refine ⟨1028947452163800935134381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487719744873604987383365 1028947452163800935134381)
                    ·
                      rfl

theorem cell23_6011604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_6011604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011604 prefixEnd_6011604 := by exact prefixLift 6011604
  have htrace : WordTrace (prefixWord ++ tailWord_6011604) baseStart_6011604 baseEnd_6011604 := by
    simpa [prefixWord, tailWord_6011604, baseEnd_6011604] using wordTrace_append hprefix tailTrace_6011604
  have hstable : (prefixWord ++ tailWord_6011604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011604).length < 2 ^ (prefixWord ++ tailWord_6011604).sum := by decide
  have hdescent : baseEnd_6011604 < baseStart_6011604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011684 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_6011684 : Nat := 118140960795 + 6011684 * 2 ^ 59
def prefixEnd_6011684 : Nat := 4983230072969 + 3 ^ 40 * 6011684 * 2
def baseEnd_6011684 : Nat := 3086883434943762492402775

theorem tailTrace_6011684 : CollatzResearch.WordTrace tailWord_6011684 prefixEnd_6011684 3086883434943762492402775 := by
  unfold tailWord_6011684
  simp only [CollatzResearch.WordTrace]
  refine ⟨109632064376351528365721053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146176085835135371154294737 109632064376351528365721053)
  ·
    refine ⟨41112024141131823137145395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109632064376351528365721053 41112024141131823137145395)
    ·
      refine ⟨61668036211697734705718093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41112024141131823137145395 61668036211697734705718093)
      ·
        refine ⟨23125513579386650514644285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61668036211697734705718093 23125513579386650514644285)
        ·
          refine ⟨8672067592269993942991607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23125513579386650514644285 8672067592269993942991607)
          ·
            refine ⟨13008101388404990914487411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672067592269993942991607 13008101388404990914487411)
            ·
              refine ⟨19512152082607486371731117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008101388404990914487411 19512152082607486371731117)
              ·
                refine ⟨7317057030977807389399169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19512152082607486371731117 7317057030977807389399169)
                ·
                  refine ⟨5487792773233355542049377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317057030977807389399169 5487792773233355542049377)
                  ·
                    refine ⟨4115844579925016656537033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5487792773233355542049377 4115844579925016656537033)
                    ·
                      refine ⟨3086883434943762492402775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115844579925016656537033 3086883434943762492402775)
                      ·
                        rfl

theorem cell23_6011684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_6011684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011684 prefixEnd_6011684 := by exact prefixLift 6011684
  have htrace : WordTrace (prefixWord ++ tailWord_6011684) baseStart_6011684 baseEnd_6011684 := by
    simpa [prefixWord, tailWord_6011684, baseEnd_6011684] using wordTrace_append hprefix tailTrace_6011684
  have hstable : (prefixWord ++ tailWord_6011684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011684).length < 2 ^ (prefixWord ++ tailWord_6011684).sum := by decide
  have hdescent : baseEnd_6011684 < baseStart_6011684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011703 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 2, 5]
def baseStart_6011703 : Nat := 118140960795 + 6011703 * 2 ^ 59
def prefixEnd_6011703 : Nat := 4983230072969 + 3 ^ 40 * 6011703 * 2
def baseEnd_6011703 : Nat := 1028964397025399306021729

theorem tailTrace_6011703 : CollatzResearch.WordTrace tailWord_6011703 prefixEnd_6011703 1028964397025399306021729 := by
  unfold tailWord_6011703
  simp only [CollatzResearch.WordTrace]
  refine ⟨219264821739634222976383763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146176547826422815317589175 219264821739634222976383763)
  ·
    refine ⟨328897232609451334464575645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219264821739634222976383763 328897232609451334464575645)
    ·
      refine ⟨123336462228544250424215867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328897232609451334464575645 123336462228544250424215867)
      ·
        refine ⟨185004693342816375636323801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123336462228544250424215867 185004693342816375636323801)
        ·
          refine ⟨138753520007112281727242851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185004693342816375636323801 138753520007112281727242851)
          ·
            refine ⟨208130280010668422590864277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138753520007112281727242851 208130280010668422590864277)
            ·
              refine ⟨9756106875500082308946763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208130280010668422590864277 9756106875500082308946763)
              ·
                refine ⟨14634160313250123463420145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9756106875500082308946763 14634160313250123463420145)
                ·
                  refine ⟨10975620234937592597565109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14634160313250123463420145 10975620234937592597565109)
                  ·
                    refine ⟨1028964397025399306021729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10975620234937592597565109 1028964397025399306021729)
                    ·
                      rfl

theorem cell23_6011703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_6011703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011703 prefixEnd_6011703 := by exact prefixLift 6011703
  have htrace : WordTrace (prefixWord ++ tailWord_6011703) baseStart_6011703 baseEnd_6011703 := by
    simpa [prefixWord, tailWord_6011703, baseEnd_6011703] using wordTrace_append hprefix tailTrace_6011703
  have hstable : (prefixWord ++ tailWord_6011703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011703).length < 2 ^ (prefixWord ++ tailWord_6011703).sum := by decide
  have hdescent : baseEnd_6011703 < baseStart_6011703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011718 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6011718 : Nat := 118140960795 + 6011718 * 2 ^ 59
def prefixEnd_6011718 : Nat := 4983230072969 + 3 ^ 40 * 6011718 * 2
def baseEnd_6011718 : Nat := 3086900893286015359377619

theorem tailTrace_6011718 : CollatzResearch.WordTrace tailWord_6011718 prefixEnd_6011718 3086900893286015359377619 := by
  unfold tailWord_6011718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6852042776080621266818119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146176912556386587025453205 6852042776080621266818119)
  ·
    refine ⟨10278064164120931900227179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6852042776080621266818119 10278064164120931900227179)
    ·
      refine ⟨15417096246181397850340769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10278064164120931900227179 15417096246181397850340769)
      ·
        refine ⟨11562822184636048387755577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15417096246181397850340769 11562822184636048387755577)
        ·
          refine ⟨8672116638477036290816683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11562822184636048387755577 8672116638477036290816683)
          ·
            refine ⟨13008174957715554436225025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672116638477036290816683 13008174957715554436225025)
            ·
              refine ⟨9756131218286665827168769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13008174957715554436225025 9756131218286665827168769)
              ·
                refine ⟨7317098413714999370376577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9756131218286665827168769 7317098413714999370376577)
                ·
                  refine ⟨5487823810286249527782433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317098413714999370376577 5487823810286249527782433)
                  ·
                    refine ⟨4115867857714687145836825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5487823810286249527782433 4115867857714687145836825)
                    ·
                      refine ⟨3086900893286015359377619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115867857714687145836825 3086900893286015359377619)
                      ·
                        rfl

theorem cell23_6011718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6011718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011718 prefixEnd_6011718 := by exact prefixLift 6011718
  have htrace : WordTrace (prefixWord ++ tailWord_6011718) baseStart_6011718 baseEnd_6011718 := by
    simpa [prefixWord, tailWord_6011718, baseEnd_6011718] using wordTrace_append hprefix tailTrace_6011718
  have hstable : (prefixWord ++ tailWord_6011718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011718).length < 2 ^ (prefixWord ++ tailWord_6011718).sum := by decide
  have hdescent : baseEnd_6011718 < baseStart_6011718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011723 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 6, 2]
def baseStart_6011723 : Nat := 118140960795 + 6011723 * 2 ^ 59
def prefixEnd_6011723 : Nat := 4983230072969 + 3 ^ 40 * 6011723 * 2
def baseEnd_6011723 : Nat := 3086903460689287839815095

theorem tailTrace_6011723 : CollatzResearch.WordTrace tailWord_6011723 prefixEnd_6011723 3086903460689287839815095 := by
  unfold tailWord_6011723
  simp only [CollatzResearch.WordTrace]
  refine ⟨219265551199561766392111823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146177034133041177594741215 219265551199561766392111823)
  ·
    refine ⟨328898326799342649588167735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219265551199561766392111823 328898326799342649588167735)
    ·
      refine ⟨493347490199013974382251603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328898326799342649588167735 493347490199013974382251603)
      ·
        refine ⟨740021235298520961573377405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493347490199013974382251603 740021235298520961573377405)
        ·
          refine ⟨277507963236945360590016527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740021235298520961573377405 277507963236945360590016527)
          ·
            refine ⟨416261944855418040885024791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277507963236945360590016527 416261944855418040885024791)
            ·
              refine ⟨624392917283127061327537187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416261944855418040885024791 624392917283127061327537187)
              ·
                refine ⟨936589375924690591991305781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624392917283127061327537187 936589375924690591991305781)
                ·
                  refine ⟨87805253992939742999184917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 936589375924690591991305781 87805253992939742999184917)
                  ·
                    refine ⟨4115871280919050453086793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87805253992939742999184917 4115871280919050453086793)
                    ·
                      refine ⟨3086903460689287839815095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4115871280919050453086793 3086903460689287839815095)
                      ·
                        rfl

theorem cell23_6011723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6, 2].length) (baseStart_6011723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011723 prefixEnd_6011723 := by exact prefixLift 6011723
  have htrace : WordTrace (prefixWord ++ tailWord_6011723) baseStart_6011723 baseEnd_6011723 := by
    simpa [prefixWord, tailWord_6011723, baseEnd_6011723] using wordTrace_append hprefix tailTrace_6011723
  have hstable : (prefixWord ++ tailWord_6011723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011723).length < 2 ^ (prefixWord ++ tailWord_6011723).sum := by decide
  have hdescent : baseEnd_6011723 < baseStart_6011723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011743 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_6011743 : Nat := 118140960795 + 6011743 * 2 ^ 59
def prefixEnd_6011743 : Nat := 4983230072969 + 3 ^ 40 * 6011743 * 2
def baseEnd_6011743 : Nat := 3086913730302377761565003

theorem tailTrace_6011743 : CollatzResearch.WordTrace tailWord_6011743 prefixEnd_6011743 3086913730302377761565003 := by
  unfold tailWord_6011743
  simp only [CollatzResearch.WordTrace]
  refine ⟨219266280659489309807839883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146177520439659539871893255 219266280659489309807839883)
  ·
    refine ⟨328899420989233964711759825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219266280659489309807839883 328899420989233964711759825)
    ·
      refine ⟨246674565741925473533819869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328899420989233964711759825 246674565741925473533819869)
      ·
        refine ⟨92502962153222052575182451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246674565741925473533819869 92502962153222052575182451)
        ·
          refine ⟨138754443229833078862773677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92502962153222052575182451 138754443229833078862773677)
          ·
            refine ⟨52032916211187404573540129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138754443229833078862773677 52032916211187404573540129)
            ·
              refine ⟨39024687158390553430155097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52032916211187404573540129 39024687158390553430155097)
              ·
                refine ⟨29268515368792915072616323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39024687158390553430155097 29268515368792915072616323)
                ·
                  refine ⟨43902773053189372608924485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29268515368792915072616323 43902773053189372608924485)
                  ·
                    refine ⟨8231769947473007364173341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43902773053189372608924485 8231769947473007364173341)
                    ·
                      refine ⟨3086913730302377761565003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231769947473007364173341 3086913730302377761565003)
                      ·
                        rfl

theorem cell23_6011743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_6011743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011743 prefixEnd_6011743 := by exact prefixLift 6011743
  have htrace : WordTrace (prefixWord ++ tailWord_6011743) baseStart_6011743 baseEnd_6011743 := by
    simpa [prefixWord, tailWord_6011743, baseEnd_6011743] using wordTrace_append hprefix tailTrace_6011743
  have hstable : (prefixWord ++ tailWord_6011743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011743).length < 2 ^ (prefixWord ++ tailWord_6011743).sum := by decide
  have hdescent : baseEnd_6011743 < baseStart_6011743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011760 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_6011760 : Nat := 118140960795 + 6011760 * 2 ^ 59
def prefixEnd_6011760 : Nat := 4983230072969 + 3 ^ 40 * 6011760 * 2
def baseEnd_6011760 : Nat := 3086922459473504195052425

theorem tailTrace_6011760 : CollatzResearch.WordTrace tailWord_6011760 prefixEnd_6011760 3086922459473504195052425 := by
  unfold tailWord_6011760
  simp only [CollatzResearch.WordTrace]
  refine ⟨109633450350213860855604367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146177933800285147807472489 109633450350213860855604367)
  ·
    refine ⟨164450175525320791283406551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109633450350213860855604367 164450175525320791283406551)
    ·
      refine ⟨246675263287981186925109827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164450175525320791283406551 246675263287981186925109827)
      ·
        refine ⟨370012894931971780387664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246675263287981186925109827 370012894931971780387664741)
        ·
          refine ⟨69377417799744708822687139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370012894931971780387664741 69377417799744708822687139)
          ·
            refine ⟨104066126699617063234030709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69377417799744708822687139 104066126699617063234030709)
            ·
              refine ⟨9756199378089099678190379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104066126699617063234030709 9756199378089099678190379)
              ·
                refine ⟨14634299067133649517285569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9756199378089099678190379 14634299067133649517285569)
                ·
                  refine ⟨10975724300350237137964177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14634299067133649517285569 10975724300350237137964177)
                  ·
                    refine ⟨8231793225262677853473133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10975724300350237137964177 8231793225262677853473133)
                    ·
                      refine ⟨3086922459473504195052425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231793225262677853473133 3086922459473504195052425)
                      ·
                        rfl

theorem cell23_6011760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_6011760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011760 prefixEnd_6011760 := by exact prefixLift 6011760
  have htrace : WordTrace (prefixWord ++ tailWord_6011760) baseStart_6011760 baseEnd_6011760 := by
    simpa [prefixWord, tailWord_6011760, baseEnd_6011760] using wordTrace_append hprefix tailTrace_6011760
  have hstable : (prefixWord ++ tailWord_6011760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011760).length < 2 ^ (prefixWord ++ tailWord_6011760).sum := by decide
  have hdescent : baseEnd_6011760 < baseStart_6011760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011783 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_6011783 : Nat := 118140960795 + 6011783 * 2 ^ 59
def prefixEnd_6011783 : Nat := 4983230072969 + 3 ^ 40 * 6011783 * 2
def baseEnd_6011783 : Nat := 3086934269528557605064819

theorem tailTrace_6011783 : CollatzResearch.WordTrace tailWord_6011783 prefixEnd_6011783 3086934269528557605064819 := by
  unfold tailWord_6011783
  simp only [CollatzResearch.WordTrace]
  refine ⟨219267739579344396639296003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146178493052896264426197335 219267739579344396639296003)
  ·
    refine ⟨328901609369016594958944005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219267739579344396639296003 328901609369016594958944005)
    ·
      refine ⟨61669051756690611554802001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328901609369016594958944005 61669051756690611554802001)
      ·
        refine ⟨46251788817517958666101501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61669051756690611554802001 46251788817517958666101501)
        ·
          refine ⟨17344420806569234499788063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46251788817517958666101501 17344420806569234499788063)
          ·
            refine ⟨26016631209853851749682095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344420806569234499788063 26016631209853851749682095)
            ·
              refine ⟨39024946814780777624523143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26016631209853851749682095 39024946814780777624523143)
              ·
                refine ⟨58537420222171166436784715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39024946814780777624523143 58537420222171166436784715)
                ·
                  refine ⟨87806130333256749655177073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58537420222171166436784715 87806130333256749655177073)
                  ·
                    refine ⟨65854597749942562241382805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87806130333256749655177073 65854597749942562241382805)
                    ·
                      refine ⟨3086934269528557605064819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65854597749942562241382805 3086934269528557605064819)
                      ·
                        rfl

theorem cell23_6011783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_6011783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011783 prefixEnd_6011783 := by exact prefixLift 6011783
  have htrace : WordTrace (prefixWord ++ tailWord_6011783) baseStart_6011783 baseEnd_6011783 := by
    simpa [prefixWord, tailWord_6011783, baseEnd_6011783] using wordTrace_append hprefix tailTrace_6011783
  have hstable : (prefixWord ++ tailWord_6011783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011783).length < 2 ^ (prefixWord ++ tailWord_6011783).sum := by decide
  have hdescent : baseEnd_6011783 < baseStart_6011783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011807 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 3]
def baseStart_6011807 : Nat := 118140960795 + 6011807 * 2 ^ 59
def prefixEnd_6011807 : Nat := 4983230072969 + 3 ^ 40 * 6011807 * 2
def baseEnd_6011807 : Nat := 3086946593064265511164709

theorem tailTrace_6011807 : CollatzResearch.WordTrace tailWord_6011807 prefixEnd_6011807 3086946593064265511164709 := by
  unfold tailWord_6011807
  simp only [CollatzResearch.WordTrace]
  refine ⟨219268614931257448738169675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146179076620838299158779783 219268614931257448738169675)
  ·
    refine ⟨328902922396886173107254513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219268614931257448738169675 328902922396886173107254513)
    ·
      refine ⟨246677191797664629830440885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328902922396886173107254513 246677191797664629830440885)
      ·
        refine ⟨23125986731031059046603833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246677191797664629830440885 23125986731031059046603833)
        ·
          refine ⟨17344490048273294284952875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23125986731031059046603833 17344490048273294284952875)
          ·
            refine ⟨26016735072409941427429313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344490048273294284952875 26016735072409941427429313)
            ·
              refine ⟨19512551304307456070571985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26016735072409941427429313 19512551304307456070571985)
              ·
                refine ⟨14634413478230592052928989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19512551304307456070571985 14634413478230592052928989)
                ·
                  refine ⟨5487905054336472019848371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14634413478230592052928989 5487905054336472019848371)
                  ·
                    refine ⟨8231857581504708029772557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5487905054336472019848371 8231857581504708029772557)
                    ·
                      refine ⟨3086946593064265511164709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231857581504708029772557 3086946593064265511164709)
                      ·
                        rfl

theorem cell23_6011807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_6011807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011807 prefixEnd_6011807 := by exact prefixLift 6011807
  have htrace : WordTrace (prefixWord ++ tailWord_6011807) baseStart_6011807 baseEnd_6011807 := by
    simpa [prefixWord, tailWord_6011807, baseEnd_6011807] using wordTrace_append hprefix tailTrace_6011807
  have hstable : (prefixWord ++ tailWord_6011807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011807).length < 2 ^ (prefixWord ++ tailWord_6011807).sum := by decide
  have hdescent : baseEnd_6011807 < baseStart_6011807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011840 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_6011840 : Nat := 118140960795 + 6011840 * 2 ^ 59
def prefixEnd_6011840 : Nat := 4983230072969 + 3 ^ 40 * 6011840 * 2
def baseEnd_6011840 : Nat := 1028987845975287960684019

theorem tailTrace_6011840 : CollatzResearch.WordTrace tailWord_6011840 prefixEnd_6011840 1028987845975287960684019 := by
  unfold tailWord_6011840
  simp only [CollatzResearch.WordTrace]
  refine ⟨109634909270068947687060487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146179879026758596916080649 109634909270068947687060487)
  ·
    refine ⟨164452363905103421530590731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109634909270068947687060487 164452363905103421530590731)
    ·
      refine ⟨246678545857655132295886097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164452363905103421530590731 246678545857655132295886097)
      ·
        refine ⟨185008909393241349221914573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246678545857655132295886097 185008909393241349221914573)
        ·
          refine ⟨69378341022465505958217965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185008909393241349221914573 69378341022465505958217965)
          ·
            refine ⟨26016877883424564734331737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69378341022465505958217965 26016877883424564734331737)
            ·
              refine ⟨19512658412568423550748803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26016877883424564734331737 19512658412568423550748803)
              ·
                refine ⟨29268987618852635326123205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19512658412568423550748803 29268987618852635326123205)
                ·
                  refine ⟨5487935178534869123648101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29268987618852635326123205 5487935178534869123648101)
                  ·
                    refine ⟨1028987845975287960684019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487935178534869123648101 1028987845975287960684019)
                    ·
                      rfl

theorem cell23_6011840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_6011840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011840 prefixEnd_6011840 := by exact prefixLift 6011840
  have htrace : WordTrace (prefixWord ++ tailWord_6011840) baseStart_6011840 baseEnd_6011840 := by
    simpa [prefixWord, tailWord_6011840, baseEnd_6011840] using wordTrace_append hprefix tailTrace_6011840
  have hstable : (prefixWord ++ tailWord_6011840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011840).length < 2 ^ (prefixWord ++ tailWord_6011840).sum := by decide
  have hdescent : baseEnd_6011840 < baseStart_6011840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011843 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_6011843 : Nat := 118140960795 + 6011843 * 2 ^ 59
def prefixEnd_6011843 : Nat := 4983230072969 + 3 ^ 40 * 6011843 * 2
def baseEnd_6011843 : Nat := 3086965078367827370314543

theorem tailTrace_6011843 : CollatzResearch.WordTrace tailWord_6011843 prefixEnd_6011843 3086965078367827370314543 := by
  unfold tailWord_6011843
  simp only [CollatzResearch.WordTrace]
  refine ⟨219269927959127026886480183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146179951972751351257653455 219269927959127026886480183)
  ·
    refine ⟨328904891938690540329720275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219269927959127026886480183 328904891938690540329720275)
    ·
      refine ⟨493357337908035810494580413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328904891938690540329720275 493357337908035810494580413)
      ·
        refine ⟨185009001715513428935467655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493357337908035810494580413 185009001715513428935467655)
        ·
          refine ⟨277513502573270143403201483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185009001715513428935467655 277513502573270143403201483)
          ·
            refine ⟨416270253859905215104802225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277513502573270143403201483 416270253859905215104802225)
            ·
              refine ⟨312202690394928911328601669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416270253859905215104802225 312202690394928911328601669)
              ·
                refine ⟨58538004449049170874112813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312202690394928911328601669 58538004449049170874112813)
                ·
                  refine ⟨21951751668393439077792305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58538004449049170874112813 21951751668393439077792305)
                  ·
                    refine ⟨16463813751295079308344229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21951751668393439077792305 16463813751295079308344229)
                    ·
                      refine ⟨3086965078367827370314543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16463813751295079308344229 3086965078367827370314543)
                      ·
                        rfl

theorem cell23_6011843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_6011843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011843 prefixEnd_6011843 := by exact prefixLift 6011843
  have htrace : WordTrace (prefixWord ++ tailWord_6011843) baseStart_6011843 baseEnd_6011843 := by
    simpa [prefixWord, tailWord_6011843, baseEnd_6011843] using wordTrace_append hprefix tailTrace_6011843
  have hstable : (prefixWord ++ tailWord_6011843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011843).length < 2 ^ (prefixWord ++ tailWord_6011843).sum := by decide
  have hdescent : baseEnd_6011843 < baseStart_6011843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011850 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_6011850 : Nat := 118140960795 + 6011850 * 2 ^ 59
def prefixEnd_6011850 : Nat := 4983230072969 + 3 ^ 40 * 6011850 * 2
def baseEnd_6011850 : Nat := 3086968672732408842927011

theorem tailTrace_6011850 : CollatzResearch.WordTrace tailWord_6011850 prefixEnd_6011850 3086968672732408842927011 := by
  unfold tailWord_6011850
  simp only [CollatzResearch.WordTrace]
  refine ⟨54817545817525416770496251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146180122180067778054656669 54817545817525416770496251)
  ·
    refine ⟨82226318726288125155744377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54817545817525416770496251 82226318726288125155744377)
    ·
      refine ⟨61669739044716093866808283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82226318726288125155744377 61669739044716093866808283)
      ·
        refine ⟨92504608567074140800212425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61669739044716093866808283 92504608567074140800212425)
        ·
          refine ⟨69378456425305605600159319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92504608567074140800212425 69378456425305605600159319)
          ·
            refine ⟨104067684637958408400238979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69378456425305605600159319 104067684637958408400238979)
            ·
              refine ⟨156101526956937612600358469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104067684637958408400238979 156101526956937612600358469)
              ·
                refine ⟨29269036304425802362567213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156101526956937612600358469 29269036304425802362567213)
                ·
                  refine ⟨10975888614159675885962705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29269036304425802362567213 10975888614159675885962705)
                  ·
                    refine ⟨8231916460619756914472029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10975888614159675885962705 8231916460619756914472029)
                    ·
                      refine ⟨3086968672732408842927011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231916460619756914472029 3086968672732408842927011)
                      ·
                        rfl

theorem cell23_6011850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_6011850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011850 prefixEnd_6011850 := by exact prefixLift 6011850
  have htrace : WordTrace (prefixWord ++ tailWord_6011850) baseStart_6011850 baseEnd_6011850 := by
    simpa [prefixWord, tailWord_6011850, baseEnd_6011850] using wordTrace_append hprefix tailTrace_6011850
  have hstable : (prefixWord ++ tailWord_6011850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011850).length < 2 ^ (prefixWord ++ tailWord_6011850).sum := by decide
  have hdescent : baseEnd_6011850 < baseStart_6011850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011860 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6011860 : Nat := 118140960795 + 6011860 * 2 ^ 59
def prefixEnd_6011860 : Nat := 4983230072969 + 3 ^ 40 * 6011860 * 2
def baseEnd_6011860 : Nat := 3086973807538953803801965

theorem tailTrace_6011860 : CollatzResearch.WordTrace tailWord_6011860 prefixEnd_6011860 3086973807538953803801965 := by
  unfold tailWord_6011860
  simp only [CollatzResearch.WordTrace]
  refine ⟨109635274000032719394924517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146180365333376959193232689 109635274000032719394924517)
  ·
    refine ⟨20556613875006134886548347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109635274000032719394924517 20556613875006134886548347)
    ·
      refine ⟨30834920812509202329822521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20556613875006134886548347 30834920812509202329822521)
      ·
        refine ⟨23126190609381901747366891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30834920812509202329822521 23126190609381901747366891)
        ·
          refine ⟨34689285914072852621050337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23126190609381901747366891 34689285914072852621050337)
          ·
            refine ⟨26016964435554639465787753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34689285914072852621050337 26016964435554639465787753)
            ·
              refine ⟨19512723326665979599340815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26016964435554639465787753 19512723326665979599340815)
              ·
                refine ⟨29269084989998969399011223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19512723326665979599340815 29269084989998969399011223)
                ·
                  refine ⟨43903627484998454098516835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29269084989998969399011223 43903627484998454098516835)
                  ·
                    refine ⟨65855441227497681147775253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43903627484998454098516835 65855441227497681147775253)
                    ·
                      refine ⟨3086973807538953803801965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65855441227497681147775253 3086973807538953803801965)
                      ·
                        rfl

theorem cell23_6011860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6011860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011860 prefixEnd_6011860 := by exact prefixLift 6011860
  have htrace : WordTrace (prefixWord ++ tailWord_6011860) baseStart_6011860 baseEnd_6011860 := by
    simpa [prefixWord, tailWord_6011860, baseEnd_6011860] using wordTrace_append hprefix tailTrace_6011860
  have hstable : (prefixWord ++ tailWord_6011860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011860).length < 2 ^ (prefixWord ++ tailWord_6011860).sum := by decide
  have hdescent : baseEnd_6011860 < baseStart_6011860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011880 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6011880 : Nat := 118140960795 + 6011880 * 2 ^ 59
def prefixEnd_6011880 : Nat := 4983230072969 + 3 ^ 40 * 6011880 * 2
def baseEnd_6011880 : Nat := 3086984077152043725551873

theorem tailTrace_6011880 : CollatzResearch.WordTrace tailWord_6011880 prefixEnd_6011880 3086984077152043725551873 := by
  unfold tailWord_6011880
  simp only [CollatzResearch.WordTrace]
  refine ⟨109635638729996491102788547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146180851639995321470384729 109635638729996491102788547)
  ·
    refine ⟨164453458094994736654182821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109635638729996491102788547 164453458094994736654182821)
    ·
      refine ⟨30835023392811513122659279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164453458094994736654182821 30835023392811513122659279)
      ·
        refine ⟨46252535089217269683988919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30835023392811513122659279 46252535089217269683988919)
        ·
          refine ⟨69378802633825904525983379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46252535089217269683988919 69378802633825904525983379)
          ·
            refine ⟨104068203950738856788975069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69378802633825904525983379 104068203950738856788975069)
            ·
              refine ⟨39025576481527071295865651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104068203950738856788975069 39025576481527071295865651)
              ·
                refine ⟨58538364722290606943798477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39025576481527071295865651 58538364722290606943798477)
                ·
                  refine ⟨21951886770858977603924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58538364722290606943798477 21951886770858977603924429)
                  ·
                    refine ⟨8231957539072116601471661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21951886770858977603924429 8231957539072116601471661)
                    ·
                      refine ⟨3086984077152043725551873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231957539072116601471661 3086984077152043725551873)
                      ·
                        rfl

theorem cell23_6011880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6011880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011880 prefixEnd_6011880 := by exact prefixLift 6011880
  have htrace : WordTrace (prefixWord ++ tailWord_6011880) baseStart_6011880 baseEnd_6011880 := by
    simpa [prefixWord, tailWord_6011880, baseEnd_6011880] using wordTrace_append hprefix tailTrace_6011880
  have hstable : (prefixWord ++ tailWord_6011880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011880).length < 2 ^ (prefixWord ++ tailWord_6011880).sum := by decide
  have hdescent : baseEnd_6011880 < baseStart_6011880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011892 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6011892 : Nat := 118140960795 + 6011892 * 2 ^ 59
def prefixEnd_6011892 : Nat := 4983230072969 + 3 ^ 40 * 6011892 * 2
def baseEnd_6011892 : Nat := 3086990238919897678601819

theorem tailTrace_6011892 : CollatzResearch.WordTrace tailWord_6011892 prefixEnd_6011892 3086990238919897678601819 := by
  unfold tailWord_6011892
  simp only [CollatzResearch.WordTrace]
  refine ⟨109635857567974754127506965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146181143423966338836675953 109635857567974754127506965)
  ·
    refine ⟨5139180823498816599726889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109635857567974754127506965 5139180823498816599726889)
    ·
      refine ⟨3854385617624112449795167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5139180823498816599726889 3854385617624112449795167)
      ·
        refine ⟨5781578426436168674692751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854385617624112449795167 5781578426436168674692751)
        ·
          refine ⟨8672367639654253012039127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781578426436168674692751 8672367639654253012039127)
          ·
            refine ⟨13008551459481379518058691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672367639654253012039127 13008551459481379518058691)
            ·
              refine ⟨19512827189222069277088037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008551459481379518058691 19512827189222069277088037)
              ·
                refine ⟨3658655097979137989454007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19512827189222069277088037 3658655097979137989454007)
                ·
                  refine ⟨5487982646968706984181011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658655097979137989454007 5487982646968706984181011)
                  ·
                    refine ⟨8231973970453060476271517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5487982646968706984181011 8231973970453060476271517)
                    ·
                      refine ⟨3086990238919897678601819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8231973970453060476271517 3086990238919897678601819)
                      ·
                        rfl

theorem cell23_6011892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6011892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011892 prefixEnd_6011892 := by exact prefixLift 6011892
  have htrace : WordTrace (prefixWord ++ tailWord_6011892) baseStart_6011892 baseEnd_6011892 := by
    simpa [prefixWord, tailWord_6011892, baseEnd_6011892] using wordTrace_append hprefix tailTrace_6011892
  have hstable : (prefixWord ++ tailWord_6011892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011892).length < 2 ^ (prefixWord ++ tailWord_6011892).sum := by decide
  have hdescent : baseEnd_6011892 < baseStart_6011892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011914 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_6011914 : Nat := 118140960795 + 6011914 * 2 ^ 59
def prefixEnd_6011914 : Nat := 4983230072969 + 3 ^ 40 * 6011914 * 2
def baseEnd_6011914 : Nat := 3087001535494296592526717

theorem tailTrace_6011914 : CollatzResearch.WordTrace tailWord_6011914 prefixEnd_6011914 3087001535494296592526717 := by
  unfold tailWord_6011914
  simp only [CollatzResearch.WordTrace]
  refine ⟨54818129385467451503078699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146181678361246537341543197 54818129385467451503078699)
  ·
    refine ⟨82227194078201177254618049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54818129385467451503078699 82227194078201177254618049)
    ·
      refine ⟨61670395558650882940963537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82227194078201177254618049 61670395558650882940963537)
      ·
        refine ⟨46252796668988162205722653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61670395558650882940963537 46252796668988162205722653)
        ·
          refine ⟨17344798750870560827145995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46252796668988162205722653 17344798750870560827145995)
          ·
            refine ⟨26017198126305841240718993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344798750870560827145995 26017198126305841240718993)
            ·
              refine ⟨19512898594729380930539245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26017198126305841240718993 19512898594729380930539245)
              ·
                refine ⟨7317336973023517848952217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19512898594729380930539245 7317336973023517848952217)
                ·
                  refine ⟨5488002729767638386714163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317336973023517848952217 5488002729767638386714163)
                  ·
                    refine ⟨8232004094651457580071245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5488002729767638386714163 8232004094651457580071245)
                    ·
                      refine ⟨3087001535494296592526717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232004094651457580071245 3087001535494296592526717)
                      ·
                        rfl

theorem cell23_6011914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_6011914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011914 prefixEnd_6011914 := by exact prefixLift 6011914
  have htrace : WordTrace (prefixWord ++ tailWord_6011914) baseStart_6011914 baseEnd_6011914 := by
    simpa [prefixWord, tailWord_6011914, baseEnd_6011914] using wordTrace_append hprefix tailTrace_6011914
  have hstable : (prefixWord ++ tailWord_6011914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011914).length < 2 ^ (prefixWord ++ tailWord_6011914).sum := by decide
  have hdescent : baseEnd_6011914 < baseStart_6011914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011954 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_6011954 : Nat := 118140960795 + 6011954 * 2 ^ 59
def prefixEnd_6011954 : Nat := 4983230072969 + 3 ^ 40 * 6011954 * 2
def baseEnd_6011954 : Nat := 3087022074720476436026533

theorem tailTrace_6011954 : CollatzResearch.WordTrace tailWord_6011954 prefixEnd_6011954 3087022074720476436026533 := by
  unfold tailWord_6011954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54818494115431223210942729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146182650974483261895847277 54818494115431223210942729)
  ·
    refine ⟨41113870586573417408207047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54818494115431223210942729 41113870586573417408207047)
    ·
      refine ⟨61670805879860126112310571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41113870586573417408207047 61670805879860126112310571)
      ·
        refine ⟨92506208819790189168465857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61670805879860126112310571 92506208819790189168465857)
        ·
          refine ⟨69379656614842641876349393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92506208819790189168465857 69379656614842641876349393)
          ·
            refine ⟨52034742461131981407262045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69379656614842641876349393 52034742461131981407262045)
            ·
              refine ⟨19513028422924493027723267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52034742461131981407262045 19513028422924493027723267)
              ·
                refine ⟨29269542634386739541584901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19513028422924493027723267 29269542634386739541584901)
                ·
                  refine ⟨5488039243947513664047169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29269542634386739541584901 5488039243947513664047169)
                  ·
                    refine ⟨4116029432960635248035377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5488039243947513664047169 4116029432960635248035377)
                    ·
                      refine ⟨3087022074720476436026533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116029432960635248035377 3087022074720476436026533)
                      ·
                        rfl

theorem cell23_6011954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_6011954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011954 prefixEnd_6011954 := by exact prefixLift 6011954
  have htrace : WordTrace (prefixWord ++ tailWord_6011954) baseStart_6011954 baseEnd_6011954 := by
    simpa [prefixWord, tailWord_6011954, baseEnd_6011954] using wordTrace_append hprefix tailTrace_6011954
  have hstable : (prefixWord ++ tailWord_6011954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011954).length < 2 ^ (prefixWord ++ tailWord_6011954).sum := by decide
  have hdescent : baseEnd_6011954 < baseStart_6011954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011960 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 7]
def baseStart_6011960 : Nat := 118140960795 + 6011960 * 2 ^ 59
def prefixEnd_6011960 : Nat := 4983230072969 + 3 ^ 40 * 6011960 * 2
def baseEnd_6011960 : Nat := 343002795067155934727945

theorem tailTrace_6011960 : CollatzResearch.WordTrace tailWord_6011960 prefixEnd_6011960 343002795067155934727945 := by
  unfold tailWord_6011960
  simp only [CollatzResearch.WordTrace]
  refine ⟨109637097649851577934244667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146182796866468770578992889 109637097649851577934244667)
  ·
    refine ⟨164455646474777366901367001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109637097649851577934244667 164455646474777366901367001)
    ·
      refine ⟨123341734856083025176025251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164455646474777366901367001 123341734856083025176025251)
      ·
        refine ⟨185012602284124537764037877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123341734856083025176025251 185012602284124537764037877)
        ·
          refine ⟨17344931464136675415378551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185012602284124537764037877 17344931464136675415378551)
          ·
            refine ⟨26017397196205013123067827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344931464136675415378551 26017397196205013123067827)
            ·
              refine ⟨39026095794307519684601741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26017397196205013123067827 39026095794307519684601741)
              ·
                refine ⟨14634785922865319881725653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39026095794307519684601741 14634785922865319881725653)
                ·
                  refine ⟨343002795067155934727945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14634785922865319881725653 343002795067155934727945)
                  ·
                    rfl

theorem cell23_6011960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_6011960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011960 prefixEnd_6011960 := by exact prefixLift 6011960
  have htrace : WordTrace (prefixWord ++ tailWord_6011960) baseStart_6011960 baseEnd_6011960 := by
    simpa [prefixWord, tailWord_6011960, baseEnd_6011960] using wordTrace_append hprefix tailTrace_6011960
  have hstable : (prefixWord ++ tailWord_6011960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011960).length < 2 ^ (prefixWord ++ tailWord_6011960).sum := by decide
  have hdescent : baseEnd_6011960 < baseStart_6011960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011963 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_6011963 : Nat := 118140960795 + 6011963 * 2 ^ 59
def prefixEnd_6011963 : Nat := 4983230072969 + 3 ^ 40 * 6011963 * 2
def baseEnd_6011963 : Nat := 3087026696046366900813991

theorem tailTrace_6011963 : CollatzResearch.WordTrace tailWord_6011963 prefixEnd_6011963 3087026696046366900813991 := by
  unfold tailWord_6011963
  simp only [CollatzResearch.WordTrace]
  refine ⟨219274304718692287380848543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146182869812461524920565695 219274304718692287380848543)
  ·
    refine ⟨328911457078038431071272815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219274304718692287380848543 328911457078038431071272815)
    ·
      refine ⟨493367185617057646606909223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328911457078038431071272815 493367185617057646606909223)
      ·
        refine ⟨740050778425586469910363835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493367185617057646606909223 740050778425586469910363835)
        ·
          refine ⟨1110076167638379704865545753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740050778425586469910363835 1110076167638379704865545753)
          ·
            refine ⟨832557125728784778649159315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110076167638379704865545753 832557125728784778649159315)
            ·
              refine ⟨1248835688593177167973738973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832557125728784778649159315 1248835688593177167973738973)
              ·
                refine ⟨468313383222441437990152115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1248835688593177167973738973 468313383222441437990152115)
                ·
                  refine ⟨702470074833662156985228173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468313383222441437990152115 702470074833662156985228173)
                  ·
                    refine ⟨263426278062623308869460565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702470074833662156985228173 263426278062623308869460565)
                    ·
                      refine ⟨3087026696046366900813991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263426278062623308869460565 3087026696046366900813991)
                      ·
                        rfl

theorem cell23_6011963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_6011963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011963 prefixEnd_6011963 := by exact prefixLift 6011963
  have htrace : WordTrace (prefixWord ++ tailWord_6011963) baseStart_6011963 baseEnd_6011963 := by
    simpa [prefixWord, tailWord_6011963, baseEnd_6011963] using wordTrace_append hprefix tailTrace_6011963
  have hstable : (prefixWord ++ tailWord_6011963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011963).length < 2 ^ (prefixWord ++ tailWord_6011963).sum := by decide
  have hdescent : baseEnd_6011963 < baseStart_6011963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6011971 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 2, 2, 2]
def baseStart_6011971 : Nat := 118140960795 + 6011971 * 2 ^ 59
def prefixEnd_6011971 : Nat := 4983230072969 + 3 ^ 40 * 6011971 * 2
def baseEnd_6011971 : Nat := 3087030803891602869513955

theorem tailTrace_6011971 : CollatzResearch.WordTrace tailWord_6011971 prefixEnd_6011971 3087030803891602869513955 := by
  unfold tailWord_6011971
  simp only [CollatzResearch.WordTrace]
  refine ⟨219274596502663304747139767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146183064335108869831426511 219274596502663304747139767)
  ·
    refine ⟨328911894753994957120709651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219274596502663304747139767 328911894753994957120709651)
    ·
      refine ⟨493367842130992435681064477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328911894753994957120709651 493367842130992435681064477)
      ·
        refine ⟨185012940799122163380399179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493367842130992435681064477 185012940799122163380399179)
        ·
          refine ⟨277519411198683245070598769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185012940799122163380399179 277519411198683245070598769)
          ·
            refine ⟨208139558399012433802949077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277519411198683245070598769 208139558399012433802949077)
            ·
              refine ⟨4878270899976853917256619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 208139558399012433802949077 4878270899976853917256619)
              ·
                refine ⟨7317406349965280875884929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878270899976853917256619 7317406349965280875884929)
                ·
                  refine ⟨5488054762473960656913697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317406349965280875884929 5488054762473960656913697)
                  ·
                    refine ⟨4116041071855470492685273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5488054762473960656913697 4116041071855470492685273)
                    ·
                      refine ⟨3087030803891602869513955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116041071855470492685273 3087030803891602869513955)
                      ·
                        rfl

theorem cell23_6011971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_6011971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6011971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6011971 prefixEnd_6011971 := by exact prefixLift 6011971
  have htrace : WordTrace (prefixWord ++ tailWord_6011971) baseStart_6011971 baseEnd_6011971 := by
    simpa [prefixWord, tailWord_6011971, baseEnd_6011971] using wordTrace_append hprefix tailTrace_6011971
  have hstable : (prefixWord ++ tailWord_6011971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6011971).length < 2 ^ (prefixWord ++ tailWord_6011971).sum := by decide
  have hdescent : baseEnd_6011971 < baseStart_6011971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6011971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012000 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_6012000 : Nat := 118140960795 + 6012000 * 2 ^ 59
def prefixEnd_6012000 : Nat := 4983230072969 + 3 ^ 40 * 6012000 * 2
def baseEnd_6012000 : Nat := 3087045694830583256051321

theorem tailTrace_6012000 : CollatzResearch.WordTrace tailWord_6012000 prefixEnd_6012000 3087045694830583256051321 := by
  unfold tailWord_6012000
  simp only [CollatzResearch.WordTrace]
  refine ⟨109637827109779121349972727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146183769479705495133296969 109637827109779121349972727)
  ·
    refine ⟨164456740664668682024959091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109637827109779121349972727 164456740664668682024959091)
    ·
      refine ⟨246685110997003023037438637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164456740664668682024959091 246685110997003023037438637)
      ·
        refine ⟨92506916623876133639039489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246685110997003023037438637 92506916623876133639039489)
        ·
          refine ⟨69380187467907100229279617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92506916623876133639039489 69380187467907100229279617)
          ·
            refine ⟨52035140600930325171959713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69380187467907100229279617 52035140600930325171959713)
            ·
              refine ⟨39026355450697743878969785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52035140600930325171959713 39026355450697743878969785)
              ·
                refine ⟨29269766588023307909227339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39026355450697743878969785 29269766588023307909227339)
                ·
                  refine ⟨43904649882034961863841009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29269766588023307909227339 43904649882034961863841009)
                  ·
                    refine ⟨32928487411526221397880757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43904649882034961863841009 32928487411526221397880757)
                    ·
                      refine ⟨3087045694830583256051321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32928487411526221397880757 3087045694830583256051321)
                      ·
                        rfl

theorem cell23_6012000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_6012000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012000 prefixEnd_6012000 := by exact prefixLift 6012000
  have htrace : WordTrace (prefixWord ++ tailWord_6012000) baseStart_6012000 baseEnd_6012000 := by
    simpa [prefixWord, tailWord_6012000, baseEnd_6012000] using wordTrace_append hprefix tailTrace_6012000
  have hstable : (prefixWord ++ tailWord_6012000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012000).length < 2 ^ (prefixWord ++ tailWord_6012000).sum := by decide
  have hdescent : baseEnd_6012000 < baseStart_6012000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012007 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 2, 5]
def baseStart_6012007 : Nat := 118140960795 + 6012007 * 2 ^ 59
def prefixEnd_6012007 : Nat := 4983230072969 + 3 ^ 40 * 6012007 * 2
def baseEnd_6012007 : Nat := 1029016429731721576221263

theorem tailTrace_6012007 : CollatzResearch.WordTrace tailWord_6012007 prefixEnd_6012007 1029016429731721576221263 := by
  unfold tailWord_6012007
  simp only [CollatzResearch.WordTrace]
  refine ⟨219275909530532882895450275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146183939687021921930300183 219275909530532882895450275)
  ·
    refine ⟨328913864295799324343175413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219275909530532882895450275 328913864295799324343175413)
    ·
      refine ⟨30835674777731186657172695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328913864295799324343175413 30835674777731186657172695)
      ·
        refine ⟨46253512166596779985759043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30835674777731186657172695 46253512166596779985759043)
        ·
          refine ⟨69380268249895169978638565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46253512166596779985759043 69380268249895169978638565)
          ·
            refine ⟨13008800296855344370994731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69380268249895169978638565 13008800296855344370994731)
            ·
              refine ⟨19513200445283016556492097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008800296855344370994731 19513200445283016556492097)
              ·
                refine ⟨14634900333962262417369073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19513200445283016556492097 14634900333962262417369073)
                ·
                  refine ⟨10976175250471696813026805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14634900333962262417369073 10976175250471696813026805)
                  ·
                    refine ⟨1029016429731721576221263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10976175250471696813026805 1029016429731721576221263)
                    ·
                      rfl

theorem cell23_6012007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_6012007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012007 prefixEnd_6012007 := by exact prefixLift 6012007
  have htrace : WordTrace (prefixWord ++ tailWord_6012007) baseStart_6012007 baseEnd_6012007 := by
    simpa [prefixWord, tailWord_6012007, baseEnd_6012007] using wordTrace_append hprefix tailTrace_6012007
  have hstable : (prefixWord ++ tailWord_6012007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012007).length < 2 ^ (prefixWord ++ tailWord_6012007).sum := by decide
  have hdescent : baseEnd_6012007 < baseStart_6012007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012027 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 2, 4, 2]
def baseStart_6012027 : Nat := 118140960795 + 6012027 * 2 ^ 59
def prefixEnd_6012027 : Nat := 4983230072969 + 3 ^ 40 * 6012027 * 2
def baseEnd_6012027 : Nat := 3087059558808254650413697

theorem tailTrace_6012027 : CollatzResearch.WordTrace tailWord_6012027 prefixEnd_6012027 3087059558808254650413697 := by
  unfold tailWord_6012027
  simp only [CollatzResearch.WordTrace]
  refine ⟨219276638990460426311178335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146184425993640284207452223 219276638990460426311178335)
  ·
    refine ⟨328914958485690639466767503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219276638990460426311178335 328914958485690639466767503)
    ·
      refine ⟨493372437728535959200151255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328914958485690639466767503 493372437728535959200151255)
      ·
        refine ⟨740058656592803938800226883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493372437728535959200151255 740058656592803938800226883)
        ·
          refine ⟨1110087984889205908200340325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740058656592803938800226883 1110087984889205908200340325)
          ·
            refine ⟨208141497166726107787563811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1110087984889205908200340325 208141497166726107787563811)
            ·
              refine ⟨312212245750089161681345717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208141497166726107787563811 312212245750089161681345717)
              ·
                refine ⟨29269898039070858907626161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312212245750089161681345717 29269898039070858907626161)
                ·
                  refine ⟨21952423529303144180719621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29269898039070858907626161 21952423529303144180719621)
                  ·
                    refine ⟨4116079411744339533884929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21952423529303144180719621 4116079411744339533884929)
                    ·
                      refine ⟨3087059558808254650413697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116079411744339533884929 3087059558808254650413697)
                      ·
                        rfl

theorem cell23_6012027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4, 2].length) (baseStart_6012027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012027 prefixEnd_6012027 := by exact prefixLift 6012027
  have htrace : WordTrace (prefixWord ++ tailWord_6012027) baseStart_6012027 baseEnd_6012027 := by
    simpa [prefixWord, tailWord_6012027, baseEnd_6012027] using wordTrace_append hprefix tailTrace_6012027
  have hstable : (prefixWord ++ tailWord_6012027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012027).length < 2 ^ (prefixWord ++ tailWord_6012027).sum := by decide
  have hdescent : baseEnd_6012027 < baseStart_6012027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012090 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_6012090 : Nat := 118140960795 + 6012090 * 2 ^ 59
def prefixEnd_6012090 : Nat := 4983230072969 + 3 ^ 40 * 6012090 * 2
def baseEnd_6012090 : Nat := 3087091908089487903925907

theorem tailTrace_6012090 : CollatzResearch.WordTrace tailWord_6012090 prefixEnd_6012090 3087091908089487903925907 := by
  unfold tailWord_6012090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54819734197308047017680431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146185957859488125380481149 54819734197308047017680431)
  ·
    refine ⟨82229601295962070526520647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54819734197308047017680431 82229601295962070526520647)
    ·
      refine ⟨123344401943943105789780971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82229601295962070526520647 123344401943943105789780971)
      ·
        refine ⟨185016602915914658684671457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123344401943943105789780971 185016602915914658684671457)
        ·
          refine ⟨138762452186935994013503593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185016602915914658684671457 138762452186935994013503593)
          ·
            refine ⟨104071839140201995510127695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138762452186935994013503593 104071839140201995510127695)
            ·
              refine ⟨156107758710302993265191543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104071839140201995510127695 156107758710302993265191543)
              ·
                refine ⟨234161638065454489897787315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156107758710302993265191543 234161638065454489897787315)
                ·
                  refine ⟨351242457098181734846680973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234161638065454489897787315 351242457098181734846680973)
                  ·
                    refine ⟨131715921411818150567505365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351242457098181734846680973 131715921411818150567505365)
                    ·
                      refine ⟨3087091908089487903925907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131715921411818150567505365 3087091908089487903925907)
                      ·
                        rfl

theorem cell23_6012090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_6012090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012090 prefixEnd_6012090 := by exact prefixLift 6012090
  have htrace : WordTrace (prefixWord ++ tailWord_6012090) baseStart_6012090 baseEnd_6012090 := by
    simpa [prefixWord, tailWord_6012090, baseEnd_6012090] using wordTrace_append hprefix tailTrace_6012090
  have hstable : (prefixWord ++ tailWord_6012090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012090).length < 2 ^ (prefixWord ++ tailWord_6012090).sum := by decide
  have hdescent : baseEnd_6012090 < baseStart_6012090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012098 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6012098 : Nat := 118140960795 + 6012098 * 2 ^ 59
def prefixEnd_6012098 : Nat := 4983230072969 + 3 ^ 40 * 6012098 * 2
def baseEnd_6012098 : Nat := 3087096015934723872625871

theorem tailTrace_6012098 : CollatzResearch.WordTrace tailWord_6012098 prefixEnd_6012098 3087096015934723872625871 := by
  unfold tailWord_6012098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54819807143300801359253237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146186152382135470291341965 54819807143300801359253237)
  ·
    refine ⟨5139356919684450127429991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54819807143300801359253237 5139356919684450127429991)
    ·
      refine ⟨7709035379526675191144987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139356919684450127429991 7709035379526675191144987)
      ·
        refine ⟨11563553069290012786717481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709035379526675191144987 11563553069290012786717481)
        ·
          refine ⟨8672664801967509590038111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11563553069290012786717481 8672664801967509590038111)
          ·
            refine ⟨13008997202951264385057167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672664801967509590038111 13008997202951264385057167)
            ·
              refine ⟨19513495804426896577585751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008997202951264385057167 19513495804426896577585751)
              ·
                refine ⟨29270243706640344866378627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19513495804426896577585751 29270243706640344866378627)
                ·
                  refine ⟨43905365559960517299567941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29270243706640344866378627 43905365559960517299567941)
                  ·
                    refine ⟨8232256042492596993668989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43905365559960517299567941 8232256042492596993668989)
                    ·
                      refine ⟨3087096015934723872625871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232256042492596993668989 3087096015934723872625871)
                      ·
                        rfl

theorem cell23_6012098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6012098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012098 prefixEnd_6012098 := by exact prefixLift 6012098
  have htrace : WordTrace (prefixWord ++ tailWord_6012098) baseStart_6012098 baseEnd_6012098 := by
    simpa [prefixWord, tailWord_6012098, baseEnd_6012098] using wordTrace_append hprefix tailTrace_6012098
  have hstable : (prefixWord ++ tailWord_6012098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012098).length < 2 ^ (prefixWord ++ tailWord_6012098).sum := by decide
  have hdescent : baseEnd_6012098 < baseStart_6012098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012114 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_6012114 : Nat := 118140960795 + 6012114 * 2 ^ 59
def prefixEnd_6012114 : Nat := 4983230072969 + 3 ^ 40 * 6012114 * 2
def baseEnd_6012114 : Nat := 1029034743875065270008599

theorem tailTrace_6012114 : CollatzResearch.WordTrace tailWord_6012114 prefixEnd_6012114 1029034743875065270008599 := by
  unfold tailWord_6012114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54819953035286310042398849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146186541427430160113063597 54819953035286310042398849)
  ·
    refine ⟨41114964776464732531799137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54819953035286310042398849 41114964776464732531799137)
    ·
      refine ⟨30836223582348549398849353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41114964776464732531799137 30836223582348549398849353)
      ·
        refine ⟨23127167686761412049137015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30836223582348549398849353 23127167686761412049137015)
        ·
          refine ⟨34690751530142118073705523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23127167686761412049137015 34690751530142118073705523)
          ·
            refine ⟨52036127295213177110558285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34690751530142118073705523 52036127295213177110558285)
            ·
              refine ⟨19513547735704941416459357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52036127295213177110558285 19513547735704941416459357)
              ·
                refine ⟨7317580400889353031172259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19513547735704941416459357 7317580400889353031172259)
                ·
                  refine ⟨10976370601334029546758389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7317580400889353031172259 10976370601334029546758389)
                  ·
                    refine ⟨1029034743875065270008599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10976370601334029546758389 1029034743875065270008599)
                    ·
                      rfl

theorem cell23_6012114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_6012114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012114 prefixEnd_6012114 := by exact prefixLift 6012114
  have htrace : WordTrace (prefixWord ++ tailWord_6012114) baseStart_6012114 baseEnd_6012114 := by
    simpa [prefixWord, tailWord_6012114, baseEnd_6012114] using wordTrace_append hprefix tailTrace_6012114
  have hstable : (prefixWord ++ tailWord_6012114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012114).length < 2 ^ (prefixWord ++ tailWord_6012114).sum := by decide
  have hdescent : baseEnd_6012114 < baseStart_6012114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012118 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6012118 : Nat := 118140960795 + 6012118 * 2 ^ 59
def prefixEnd_6012118 : Nat := 4983230072969 + 3 ^ 40 * 6012118 * 2
def baseEnd_6012118 : Nat := 343011809505312643819531

theorem tailTrace_6012118 : CollatzResearch.WordTrace tailWord_6012118 prefixEnd_6012118 343011809505312643819531 := by
  unfold tailWord_6012118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13704997377070671803296313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146186638688753832568494005 13704997377070671803296313)
  ·
    refine ⟨10278748032803003852472235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13704997377070671803296313 10278748032803003852472235)
    ·
      refine ⟨15418122049204505778708353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10278748032803003852472235 15418122049204505778708353)
      ·
        refine ⟨11563591536903379334031265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15418122049204505778708353 11563591536903379334031265)
        ·
          refine ⟨8672693652677534500523449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11563591536903379334031265 8672693652677534500523449)
          ·
            refine ⟨6504520239508150875392587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8672693652677534500523449 6504520239508150875392587)
            ·
              refine ⟨9756780359262226313088881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504520239508150875392587 9756780359262226313088881)
              ·
                refine ⟨7317585269446669734816661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9756780359262226313088881 7317585269446669734816661)
                ·
                  refine ⟨343011809505312643819531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7317585269446669734816661 343011809505312643819531)
                  ·
                    rfl

theorem cell23_6012118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6012118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012118 prefixEnd_6012118 := by exact prefixLift 6012118
  have htrace : WordTrace (prefixWord ++ tailWord_6012118) baseStart_6012118 baseEnd_6012118 := by
    simpa [prefixWord, tailWord_6012118, baseEnd_6012118] using wordTrace_append hprefix tailTrace_6012118
  have hstable : (prefixWord ++ tailWord_6012118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012118).length < 2 ^ (prefixWord ++ tailWord_6012118).sum := by decide
  have hdescent : baseEnd_6012118 < baseStart_6012118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012147 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6]
def baseStart_6012147 : Nat := 118140960795 + 6012147 * 2 ^ 59
def prefixEnd_6012147 : Nat := 4983230072969 + 3 ^ 40 * 6012147 * 2
def baseEnd_6012147 : Nat := 3087121176486794180913145

theorem tailTrace_6012147 : CollatzResearch.WordTrace tailWord_6012147 prefixEnd_6012147 3087121176486794180913145 := by
  unfold tailWord_6012147
  simp only [CollatzResearch.WordTrace]
  refine ⟨219281015750025686805546695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146187343833350457870364463 219281015750025686805546695)
  ·
    refine ⟨328921523625038530208320043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219281015750025686805546695 328921523625038530208320043)
    ·
      refine ⟨493382285437557795312480065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328921523625038530208320043 493382285437557795312480065)
      ·
        refine ⟨370036714078168346484360049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493382285437557795312480065 370036714078168346484360049)
        ·
          refine ⟨277527535558626259863270037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370036714078168346484360049 277527535558626259863270037)
          ·
            refine ⟨13009103229310605931090783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277527535558626259863270037 13009103229310605931090783)
            ·
              refine ⟨19513654843965908896636175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13009103229310605931090783 19513654843965908896636175)
              ·
                refine ⟨29270482265948863344954263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19513654843965908896636175 29270482265948863344954263)
                ·
                  refine ⟨43905723398923295017431395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29270482265948863344954263 43905723398923295017431395)
                  ·
                    refine ⟨65858585098384942526147093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43905723398923295017431395 65858585098384942526147093)
                    ·
                      refine ⟨3087121176486794180913145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65858585098384942526147093 3087121176486794180913145)
                      ·
                        rfl

theorem cell23_6012147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_6012147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012147 prefixEnd_6012147 := by exact prefixLift 6012147
  have htrace : WordTrace (prefixWord ++ tailWord_6012147) baseStart_6012147 baseEnd_6012147 := by
    simpa [prefixWord, tailWord_6012147, baseEnd_6012147] using wordTrace_append hprefix tailTrace_6012147
  have hstable : (prefixWord ++ tailWord_6012147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012147).length < 2 ^ (prefixWord ++ tailWord_6012147).sum := by decide
  have hdescent : baseEnd_6012147 < baseStart_6012147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012162 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6012162 : Nat := 118140960795 + 6012162 * 2 ^ 59
def prefixEnd_6012162 : Nat := 4983230072969 + 3 ^ 40 * 6012162 * 2
def baseEnd_6012162 : Nat := 3087128878696611622225577

theorem tailTrace_6012162 : CollatzResearch.WordTrace tailWord_6012162 prefixEnd_6012162 3087128878696611622225577 := by
  unfold tailWord_6012162
  simp only [CollatzResearch.WordTrace]
  refine ⟨54820390711242836091835685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146187708563314229578228493 54820390711242836091835685)
  ·
    refine ⟨10278823258358031767219191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54820390711242836091835685 10278823258358031767219191)
    ·
      refine ⟨15418234887537047650828787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10278823258358031767219191 15418234887537047650828787)
      ·
        refine ⟨23127352331305571476243181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15418234887537047650828787 23127352331305571476243181)
        ·
          refine ⟨8672757124239589303591193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23127352331305571476243181 8672757124239589303591193)
          ·
            refine ⟨6504567843179691977693395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8672757124239589303591193 6504567843179691977693395)
            ·
              refine ⟨9756851764769537966540093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504567843179691977693395 9756851764769537966540093)
              ·
                refine ⟨3658819411788576737452535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9756851764769537966540093 3658819411788576737452535)
                ·
                  refine ⟨5488229117682865106178803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658819411788576737452535 5488229117682865106178803)
                  ·
                    refine ⟨8232343676524297659268205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5488229117682865106178803 8232343676524297659268205)
                    ·
                      refine ⟨3087128878696611622225577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232343676524297659268205 3087128878696611622225577)
                      ·
                        rfl

theorem cell23_6012162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6012162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012162 prefixEnd_6012162 := by exact prefixLift 6012162
  have htrace : WordTrace (prefixWord ++ tailWord_6012162) baseStart_6012162 baseEnd_6012162 := by
    simpa [prefixWord, tailWord_6012162, baseEnd_6012162] using wordTrace_append hprefix tailTrace_6012162
  have hstable : (prefixWord ++ tailWord_6012162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012162).length < 2 ^ (prefixWord ++ tailWord_6012162).sum := by decide
  have hdescent : baseEnd_6012162 < baseStart_6012162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012205 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6012205 : Nat := 118140960795 + 6012205 * 2 ^ 59
def prefixEnd_6012205 : Nat := 4983230072969 + 3 ^ 40 * 6012205 * 2
def baseEnd_6012205 : Nat := 3087150958364754953987879

theorem tailTrace_6012205 : CollatzResearch.WordTrace tailWord_6012205 prefixEnd_6012205 3087150958364754953987879 := by
  unfold tailWord_6012205
  simp only [CollatzResearch.WordTrace]
  refine ⟨219283131183815562711158069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146188754122543708474105379 219283131183815562711158069)
  ·
    refine ⟨20557793548482709004171069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219283131183815562711158069 20557793548482709004171069)
    ·
      refine ⟨7709172580681015876564151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20557793548482709004171069 7709172580681015876564151)
      ·
        refine ⟨11563758871021523814846227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709172580681015876564151 11563758871021523814846227)
        ·
          refine ⟨17345638306532285722269341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11563758871021523814846227 17345638306532285722269341)
          ·
            refine ⟨6504614364949607145851003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17345638306532285722269341 6504614364949607145851003)
            ·
              refine ⟨9756921547424410718776505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504614364949607145851003 9756921547424410718776505)
              ·
                refine ⟨7317691160568308039082379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9756921547424410718776505 7317691160568308039082379)
                ·
                  refine ⟨10976536740852462058623569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7317691160568308039082379 10976536740852462058623569)
                  ·
                    refine ⟨8232402555639346543967677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10976536740852462058623569 8232402555639346543967677)
                    ·
                      refine ⟨3087150958364754953987879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232402555639346543967677 3087150958364754953987879)
                      ·
                        rfl

theorem cell23_6012205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6012205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012205 prefixEnd_6012205 := by exact prefixLift 6012205
  have htrace : WordTrace (prefixWord ++ tailWord_6012205) baseStart_6012205 baseEnd_6012205 := by
    simpa [prefixWord, tailWord_6012205, baseEnd_6012205] using wordTrace_append hprefix tailTrace_6012205
  have hstable : (prefixWord ++ tailWord_6012205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012205).length < 2 ^ (prefixWord ++ tailWord_6012205).sum := by decide
  have hdescent : baseEnd_6012205 < baseStart_6012205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012211 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 3, 3, 2]
def baseStart_6012211 : Nat := 118140960795 + 6012211 * 2 ^ 59
def prefixEnd_6012211 : Nat := 4983230072969 + 3 ^ 40 * 6012211 * 2
def baseEnd_6012211 : Nat := 3087154039248681930512851

theorem tailTrace_6012211 : CollatzResearch.WordTrace tailWord_6012211 prefixEnd_6012211 3087154039248681930512851 := by
  unfold tailWord_6012211
  simp only [CollatzResearch.WordTrace]
  refine ⟨219283350021793825735876487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146188900014529217157250991 219283350021793825735876487)
  ·
    refine ⟨328925025032690738603814731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219283350021793825735876487 328925025032690738603814731)
    ·
      refine ⟨493387537549036107905722097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328925025032690738603814731 493387537549036107905722097)
      ·
        refine ⟨370040653161777080929291573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493387537549036107905722097 370040653161777080929291573)
        ·
          refine ⟨34691311233916601337121085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 370040653161777080929291573 34691311233916601337121085)
          ·
            refine ⟨13009241712718725501420407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34691311233916601337121085 13009241712718725501420407)
            ·
              refine ⟨19513862569078088252130611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13009241712718725501420407 19513862569078088252130611)
              ·
                refine ⟨29270793853617132378195917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19513862569078088252130611 29270793853617132378195917)
                ·
                  refine ⟨10976547695106424641823469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29270793853617132378195917 10976547695106424641823469)
                  ·
                    refine ⟨4116205385664909240683801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10976547695106424641823469 4116205385664909240683801)
                    ·
                      refine ⟨3087154039248681930512851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116205385664909240683801 3087154039248681930512851)
                      ·
                        rfl

theorem cell23_6012211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3, 2].length) (baseStart_6012211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012211 prefixEnd_6012211 := by exact prefixLift 6012211
  have htrace : WordTrace (prefixWord ++ tailWord_6012211) baseStart_6012211 baseEnd_6012211 := by
    simpa [prefixWord, tailWord_6012211, baseEnd_6012211] using wordTrace_append hprefix tailTrace_6012211
  have hstable : (prefixWord ++ tailWord_6012211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012211).length < 2 ^ (prefixWord ++ tailWord_6012211).sum := by decide
  have hdescent : baseEnd_6012211 < baseStart_6012211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012244 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_6012244 : Nat := 118140960795 + 6012244 * 2 ^ 59
def prefixEnd_6012244 : Nat := 4983230072969 + 3 ^ 40 * 6012244 * 2
def baseEnd_6012244 : Nat := 3087170984110280301400199

theorem tailTrace_6012244 : CollatzResearch.WordTrace tailWord_6012244 prefixEnd_6012244 3087170984110280301400199 := by
  unfold tailWord_6012244
  simp only [CollatzResearch.WordTrace]
  refine ⟨109642276815337136185913893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146189702420449514914551857 109642276815337136185913893)
  ·
    refine ⟨20557926902875713034858855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109642276815337136185913893 20557926902875713034858855)
    ·
      refine ⟨30836890354313569552288283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20557926902875713034858855 30836890354313569552288283)
      ·
        refine ⟨46255335531470354328432425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30836890354313569552288283 46255335531470354328432425)
        ·
          refine ⟨34691501648602765746324319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46255335531470354328432425 34691501648602765746324319)
          ·
            refine ⟨52037252472904148619486479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34691501648602765746324319 52037252472904148619486479)
            ·
              refine ⟨78055878709356222929229719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52037252472904148619486479 78055878709356222929229719)
              ·
                refine ⟨117083818064034334393844579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78055878709356222929229719 117083818064034334393844579)
                ·
                  refine ⟨175625727096051501590766869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117083818064034334393844579 175625727096051501590766869)
                  ·
                    refine ⟨8232455957627414137067197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175625727096051501590766869 8232455957627414137067197)
                    ·
                      refine ⟨3087170984110280301400199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232455957627414137067197 3087170984110280301400199)
                      ·
                        rfl

theorem cell23_6012244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_6012244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012244 prefixEnd_6012244 := by exact prefixLift 6012244
  have htrace : WordTrace (prefixWord ++ tailWord_6012244) baseStart_6012244 baseEnd_6012244 := by
    simpa [prefixWord, tailWord_6012244, baseEnd_6012244] using wordTrace_append hprefix tailTrace_6012244
  have hstable : (prefixWord ++ tailWord_6012244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012244).length < 2 ^ (prefixWord ++ tailWord_6012244).sum := by decide
  have hdescent : baseEnd_6012244 < baseStart_6012244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012258 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6012258 : Nat := 118140960795 + 6012258 * 2 ^ 59
def prefixEnd_6012258 : Nat := 4983230072969 + 3 ^ 40 * 6012258 * 2
def baseEnd_6012258 : Nat := 3087178172839443246625135

theorem tailTrace_6012258 : CollatzResearch.WordTrace tailWord_6012258 prefixEnd_6012258 3087178172839443246625135 := by
  unfold tailWord_6012258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54821266063155888190709357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146190042835082368508558285 54821266063155888190709357)
  ·
    refine ⟨20557974773683458071516009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54821266063155888190709357 20557974773683458071516009)
    ·
      refine ⟨15418481080262593553637007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20557974773683458071516009 15418481080262593553637007)
      ·
        refine ⟨23127721620393890330455511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15418481080262593553637007 23127721620393890330455511)
        ·
          refine ⟨34691582430590835495683267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23127721620393890330455511 34691582430590835495683267)
          ·
            refine ⟨52037373645886253243524901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34691582430590835495683267 52037373645886253243524901)
            ·
              refine ⟨9757007558603672483160919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52037373645886253243524901 9757007558603672483160919)
              ·
                refine ⟨14635511337905508724741379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757007558603672483160919 14635511337905508724741379)
                ·
                  refine ⟨21953267006858263087112069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14635511337905508724741379 21953267006858263087112069)
                  ·
                    refine ⟨4116237563785924328833513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21953267006858263087112069 4116237563785924328833513)
                    ·
                      refine ⟨3087178172839443246625135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116237563785924328833513 3087178172839443246625135)
                      ·
                        rfl

theorem cell23_6012258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6012258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012258 prefixEnd_6012258 := by exact prefixLift 6012258
  have htrace : WordTrace (prefixWord ++ tailWord_6012258) baseStart_6012258 baseEnd_6012258 := by
    simpa [prefixWord, tailWord_6012258, baseEnd_6012258] using wordTrace_append hprefix tailTrace_6012258
  have hstable : (prefixWord ++ tailWord_6012258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012258).length < 2 ^ (prefixWord ++ tailWord_6012258).sum := by decide
  have hdescent : baseEnd_6012258 < baseStart_6012258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012274 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6012274 : Nat := 118140960795 + 6012274 * 2 ^ 59
def prefixEnd_6012274 : Nat := 4983230072969 + 3 ^ 40 * 6012274 * 2
def baseEnd_6012274 : Nat := 3087186388529915184025061

theorem tailTrace_6012274 : CollatzResearch.WordTrace tailWord_6012274 prefixEnd_6012274 3087186388529915184025061 := by
  unfold tailWord_6012274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54821411955141396873854969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146190431880377058330279917 54821411955141396873854969)
  ·
    refine ⟨41116058966356047655391227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54821411955141396873854969 41116058966356047655391227)
    ·
      refine ⟨61674088449534071483086841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41116058966356047655391227 61674088449534071483086841)
      ·
        refine ⟨46255566337150553612315131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61674088449534071483086841 46255566337150553612315131)
        ·
          refine ⟨69383349505725830418472697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46255566337150553612315131 69383349505725830418472697)
          ·
            refine ⟨52037512129294372813854523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69383349505725830418472697 52037512129294372813854523)
            ·
              refine ⟨78056268193941559220781785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52037512129294372813854523 78056268193941559220781785)
              ·
                refine ⟨58542201145456169415586339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78056268193941559220781785 58542201145456169415586339)
                ·
                  refine ⟨87813301718184254123379509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58542201145456169415586339 87813301718184254123379509)
                  ·
                    refine ⟨8232497036079773824066829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87813301718184254123379509 8232497036079773824066829)
                    ·
                      refine ⟨3087186388529915184025061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232497036079773824066829 3087186388529915184025061)
                      ·
                        rfl

theorem cell23_6012274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6012274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012274 prefixEnd_6012274 := by exact prefixLift 6012274
  have htrace : WordTrace (prefixWord ++ tailWord_6012274) baseStart_6012274 baseEnd_6012274 := by
    simpa [prefixWord, tailWord_6012274, baseEnd_6012274] using wordTrace_append hprefix tailTrace_6012274
  have hstable : (prefixWord ++ tailWord_6012274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012274).length < 2 ^ (prefixWord ++ tailWord_6012274).sum := by decide
  have hdescent : baseEnd_6012274 < baseStart_6012274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012314 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6012314 : Nat := 118140960795 + 6012314 * 2 ^ 59
def prefixEnd_6012314 : Nat := 4983230072969 + 3 ^ 40 * 6012314 * 2
def baseEnd_6012314 : Nat := 3087206927756095027524877

theorem tailTrace_6012314 : CollatzResearch.WordTrace tailWord_6012314 prefixEnd_6012314 3087206927756095027524877 := by
  unfold tailWord_6012314
  simp only [CollatzResearch.WordTrace]
  refine ⟨54821776685105168581718999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146191404493613782884583997 54821776685105168581718999)
  ·
    refine ⟨82232665027657752872578499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54821776685105168581718999 82232665027657752872578499)
    ·
      refine ⟨123348997541486629308867749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82232665027657752872578499 123348997541486629308867749)
      ·
        refine ⟨23127937039028742995412703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123348997541486629308867749 23127937039028742995412703)
        ·
          refine ⟨34691905558543114493119055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23127937039028742995412703 34691905558543114493119055)
          ·
            refine ⟨52037858337814671739678583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34691905558543114493119055 52037858337814671739678583)
            ·
              refine ⟨78056787506722007609517875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52037858337814671739678583 78056787506722007609517875)
              ·
                refine ⟨117085181260083011414276813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78056787506722007609517875 117085181260083011414276813)
                ·
                  refine ⟨43906942972531129280353805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117085181260083011414276813 43906942972531129280353805)
                  ·
                    refine ⟨16465103614699173480132677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43906942972531129280353805 16465103614699173480132677)
                    ·
                      refine ⟨3087206927756095027524877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16465103614699173480132677 3087206927756095027524877)
                      ·
                        rfl

theorem cell23_6012314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6012314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012314 prefixEnd_6012314 := by exact prefixLift 6012314
  have htrace : WordTrace (prefixWord ++ tailWord_6012314) baseStart_6012314 baseEnd_6012314 := by
    simpa [prefixWord, tailWord_6012314, baseEnd_6012314] using wordTrace_append hprefix tailTrace_6012314
  have hstable : (prefixWord ++ tailWord_6012314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012314).length < 2 ^ (prefixWord ++ tailWord_6012314).sum := by decide
  have hdescent : baseEnd_6012314 < baseStart_6012314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012348 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6012348 : Nat := 118140960795 + 6012348 * 2 ^ 59
def prefixEnd_6012348 : Nat := 4983230072969 + 3 ^ 40 * 6012348 * 2
def baseEnd_6012348 : Nat := 3087224386098347894499721

theorem tailTrace_6012348 : CollatzResearch.WordTrace tailWord_6012348 prefixEnd_6012348 3087224386098347894499721 := by
  unfold tailWord_6012348
  simp only [CollatzResearch.WordTrace]
  refine ⟨109644173411148749066806849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146192231214864998755742465 109644173411148749066806849)
  ·
    refine ⟨82233130058361561800105137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109644173411148749066806849 82233130058361561800105137)
    ·
      refine ⟨61674847543771171350078853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82233130058361561800105137 61674847543771171350078853)
      ·
        refine ⟨11564033914457094628139785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61674847543771171350078853 11564033914457094628139785)
        ·
          refine ⟨8673025435842820971104839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11564033914457094628139785 8673025435842820971104839)
          ·
            refine ⟨13009538153764231456657259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673025435842820971104839 13009538153764231456657259)
            ·
              refine ⟨19514307230646347184985889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13009538153764231456657259 19514307230646347184985889)
              ·
                refine ⟨14635730422984760388739417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19514307230646347184985889 14635730422984760388739417)
                ·
                  refine ⟨10976797817238570291554563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14635730422984760388739417 10976797817238570291554563)
                  ·
                    refine ⟨16465196725857855437331845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10976797817238570291554563 16465196725857855437331845)
                    ·
                      refine ⟨3087224386098347894499721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16465196725857855437331845 3087224386098347894499721)
                      ·
                        rfl

theorem cell23_6012348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6012348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012348 prefixEnd_6012348 := by exact prefixLift 6012348
  have htrace : WordTrace (prefixWord ++ tailWord_6012348) baseStart_6012348 baseEnd_6012348 := by
    simpa [prefixWord, tailWord_6012348, baseEnd_6012348] using wordTrace_append hprefix tailTrace_6012348
  have hstable : (prefixWord ++ tailWord_6012348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012348).length < 2 ^ (prefixWord ++ tailWord_6012348).sum := by decide
  have hdescent : baseEnd_6012348 < baseStart_6012348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012408 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_6012408 : Nat := 118140960795 + 6012408 * 2 ^ 59
def prefixEnd_6012408 : Nat := 4983230072969 + 3 ^ 40 * 6012408 * 2
def baseEnd_6012408 : Nat := 3087255194937617659749445

theorem tailTrace_6012408 : CollatzResearch.WordTrace tailWord_6012408 prefixEnd_6012408 3087255194937617659749445 := by
  unfold tailWord_6012408
  simp only [CollatzResearch.WordTrace]
  refine ⟨109645267601040064190398939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146193690134720085587198585 109645267601040064190398939)
  ·
    refine ⟨164467901401560096285598409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109645267601040064190398939 164467901401560096285598409)
    ·
      refine ⟨123350926051170072214198807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164467901401560096285598409 123350926051170072214198807)
      ·
        refine ⟨185026389076755108321298211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123350926051170072214198807 185026389076755108321298211)
        ·
          refine ⟨277539583615132662481947317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185026389076755108321298211 277539583615132662481947317)
          ·
            refine ⟨26019335963918687107682561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277539583615132662481947317 26019335963918687107682561)
            ·
              refine ⟨19514501972939015330761921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26019335963918687107682561 19514501972939015330761921)
              ·
                refine ⟨14635876479704261498071441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19514501972939015330761921 14635876479704261498071441)
                ·
                  refine ⟨10976907359778196123553581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14635876479704261498071441 10976907359778196123553581)
                  ·
                    refine ⟨4116340259916823546332593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10976907359778196123553581 4116340259916823546332593)
                    ·
                      refine ⟨3087255194937617659749445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116340259916823546332593 3087255194937617659749445)
                      ·
                        rfl

theorem cell23_6012408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_6012408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012408 prefixEnd_6012408 := by exact prefixLift 6012408
  have htrace : WordTrace (prefixWord ++ tailWord_6012408) baseStart_6012408 baseEnd_6012408 := by
    simpa [prefixWord, tailWord_6012408, baseEnd_6012408] using wordTrace_append hprefix tailTrace_6012408
  have hstable : (prefixWord ++ tailWord_6012408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012408).length < 2 ^ (prefixWord ++ tailWord_6012408).sum := by decide
  have hdescent : baseEnd_6012408 < baseStart_6012408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012418 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6012418 : Nat := 118140960795 + 6012418 * 2 ^ 59
def prefixEnd_6012418 : Nat := 4983230072969 + 3 ^ 40 * 6012418 * 2
def baseEnd_6012418 : Nat := 1029086776581387540208133

theorem tailTrace_6012418 : CollatzResearch.WordTrace tailWord_6012418 prefixEnd_6012418 1029086776581387540208133 := by
  unfold tailWord_6012418
  simp only [CollatzResearch.WordTrace]
  refine ⟨54822724983010975022165477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146193933288029266725774605 54822724983010975022165477)
  ·
    refine ⟨10279260934314557816656027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54822724983010975022165477 10279260934314557816656027)
    ·
      refine ⟨15418891401471836724984041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279260934314557816656027 15418891401471836724984041)
      ·
        refine ⟨11564168551103877543738031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15418891401471836724984041 11564168551103877543738031)
        ·
          refine ⟨17346252826655816315607047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564168551103877543738031 17346252826655816315607047)
          ·
            refine ⟨26019379239983724473410571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17346252826655816315607047 26019379239983724473410571)
            ·
              refine ⟨39029068859975586710115857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26019379239983724473410571 39029068859975586710115857)
              ·
                refine ⟨29271801644981690032586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39029068859975586710115857 29271801644981690032586893)
                ·
                  refine ⟨10976925616868133762220085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29271801644981690032586893 10976925616868133762220085)
                  ·
                    refine ⟨1029086776581387540208133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10976925616868133762220085 1029086776581387540208133)
                    ·
                      rfl

theorem cell23_6012418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6012418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012418 prefixEnd_6012418 := by exact prefixLift 6012418
  have htrace : WordTrace (prefixWord ++ tailWord_6012418) baseStart_6012418 baseEnd_6012418 := by
    simpa [prefixWord, tailWord_6012418, baseEnd_6012418] using wordTrace_append hprefix tailTrace_6012418
  have hstable : (prefixWord ++ tailWord_6012418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012418).length < 2 ^ (prefixWord ++ tailWord_6012418).sum := by decide
  have hdescent : baseEnd_6012418 < baseStart_6012418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012421 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_6012421 : Nat := 118140960795 + 6012421 * 2 ^ 59
def prefixEnd_6012421 : Nat := 4983230072969 + 3 ^ 40 * 6012421 * 2
def baseEnd_6012421 : Nat := 3087261870186126108886885

theorem tailTrace_6012421 : CollatzResearch.WordTrace tailWord_6012421 prefixEnd_6012421 3087261870186126108886885 := by
  unfold tailWord_6012421
  simp only [CollatzResearch.WordTrace]
  refine ⟨219291009351033031601021117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146194006234022021067347411 219291009351033031601021117)
  ·
    refine ⟨82234128506637386850382919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219291009351033031601021117 82234128506637386850382919)
    ·
      refine ⟨123351192759956080275574379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82234128506637386850382919 123351192759956080275574379)
      ·
        refine ⟨185026789139934120413361569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123351192759956080275574379 185026789139934120413361569)
        ·
          refine ⟨138770091854950590310021177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185026789139934120413361569 138770091854950590310021177)
          ·
            refine ⟨104077568891212942732515883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138770091854950590310021177 104077568891212942732515883)
            ·
              refine ⟨156116353336819414098773825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104077568891212942732515883 156116353336819414098773825)
              ·
                refine ⟨117087265002614560574080369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156116353336819414098773825 117087265002614560574080369)
                ·
                  refine ⟨87815448751960920430560277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117087265002614560574080369 87815448751960920430560277)
                  ·
                    refine ⟨4116349160248168145182513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87815448751960920430560277 4116349160248168145182513)
                    ·
                      refine ⟨3087261870186126108886885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116349160248168145182513 3087261870186126108886885)
                      ·
                        rfl

theorem cell23_6012421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_6012421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012421 prefixEnd_6012421 := by exact prefixLift 6012421
  have htrace : WordTrace (prefixWord ++ tailWord_6012421) baseStart_6012421 baseEnd_6012421 := by
    simpa [prefixWord, tailWord_6012421, baseEnd_6012421] using wordTrace_append hprefix tailTrace_6012421
  have hstable : (prefixWord ++ tailWord_6012421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012421).length < 2 ^ (prefixWord ++ tailWord_6012421).sum := by decide
  have hdescent : baseEnd_6012421 < baseStart_6012421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012464 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_6012464 : Nat := 118140960795 + 6012464 * 2 ^ 59
def prefixEnd_6012464 : Nat := 4983230072969 + 3 ^ 40 * 6012464 * 2
def baseEnd_6012464 : Nat := 3087283949854269440649187

theorem tailTrace_6012464 : CollatzResearch.WordTrace tailWord_6012464 prefixEnd_6012464 3087283949854269440649187 := by
  unfold tailWord_6012464
  simp only [CollatzResearch.WordTrace]
  refine ⟨109646288844938624972418223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146195051793251499963224297 109646288844938624972418223)
  ·
    refine ⟨164469433267407937458627335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109646288844938624972418223 164469433267407937458627335)
    ·
      refine ⟨246704149901111906187941003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164469433267407937458627335 246704149901111906187941003)
      ·
        refine ⟨370056224851667859281911505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246704149901111906187941003 370056224851667859281911505)
        ·
          refine ⟨277542168638750894461433629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370056224851667859281911505 277542168638750894461433629)
          ·
            refine ⟨104078313239531585423037611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277542168638750894461433629 104078313239531585423037611)
            ·
              refine ⟨156117469859297378134556417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104078313239531585423037611 156117469859297378134556417)
              ·
                refine ⟨117088102394473033600917313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156117469859297378134556417 117088102394473033600917313)
                ·
                  refine ⟨87816076795854775200687985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117088102394473033600917313 87816076795854775200687985)
                  ·
                    refine ⟨65862057596891081400515989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87816076795854775200687985 65862057596891081400515989)
                    ·
                      refine ⟨3087283949854269440649187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65862057596891081400515989 3087283949854269440649187)
                      ·
                        rfl

theorem cell23_6012464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_6012464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012464 prefixEnd_6012464 := by exact prefixLift 6012464
  have htrace : WordTrace (prefixWord ++ tailWord_6012464) baseStart_6012464 baseEnd_6012464 := by
    simpa [prefixWord, tailWord_6012464, baseEnd_6012464] using wordTrace_append hprefix tailTrace_6012464
  have hstable : (prefixWord ++ tailWord_6012464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012464).length < 2 ^ (prefixWord ++ tailWord_6012464).sum := by decide
  have hdescent : baseEnd_6012464 < baseStart_6012464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012472 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 1, 2, 2]
def baseStart_6012472 : Nat := 118140960795 + 6012472 * 2 ^ 59
def prefixEnd_6012472 : Nat := 4983230072969 + 3 ^ 40 * 6012472 * 2
def baseEnd_6012472 : Nat := 3087288057699505409349151

theorem tailTrace_6012472 : CollatzResearch.WordTrace tailWord_6012472 prefixEnd_6012472 3087288057699505409349151 := by
  unfold tailWord_6012472
  simp only [CollatzResearch.WordTrace]
  refine ⟨109646434736924133655563835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146195246315898844874085113 109646434736924133655563835)
  ·
    refine ⟨164469652105386200483345753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109646434736924133655563835 164469652105386200483345753)
    ·
      refine ⟨123352239079039650362509315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164469652105386200483345753 123352239079039650362509315)
      ·
        refine ⟨185028358618559475543763973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123352239079039650362509315 185028358618559475543763973)
        ·
          refine ⟨34692817240979901664455745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185028358618559475543763973 34692817240979901664455745)
          ·
            refine ⟨26019612930734926248341809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34692817240979901664455745 26019612930734926248341809)
            ·
              refine ⟨19514709698051194686256357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26019612930734926248341809 19514709698051194686256357)
              ·
                refine ⟨3659008068384599003673067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19514709698051194686256357 3659008068384599003673067)
                ·
                  refine ⟨5488512102576898505509601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659008068384599003673067 5488512102576898505509601)
                  ·
                    refine ⟨4116384076932673879132201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5488512102576898505509601 4116384076932673879132201)
                    ·
                      refine ⟨3087288057699505409349151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116384076932673879132201 3087288057699505409349151)
                      ·
                        rfl

theorem cell23_6012472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_6012472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012472 prefixEnd_6012472 := by exact prefixLift 6012472
  have htrace : WordTrace (prefixWord ++ tailWord_6012472) baseStart_6012472 baseEnd_6012472 := by
    simpa [prefixWord, tailWord_6012472, baseEnd_6012472] using wordTrace_append hprefix tailTrace_6012472
  have hstable : (prefixWord ++ tailWord_6012472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012472).length < 2 ^ (prefixWord ++ tailWord_6012472).sum := by decide
  have hdescent : baseEnd_6012472 < baseStart_6012472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012515 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 1, 3, 2]
def baseStart_6012515 : Nat := 118140960795 + 6012515 * 2 ^ 59
def prefixEnd_6012515 : Nat := 4983230072969 + 3 ^ 40 * 6012515 * 2
def baseEnd_6012515 : Nat := 3087310137367648741111453

theorem tailTrace_6012515 : CollatzResearch.WordTrace tailWord_6012515 prefixEnd_6012515 3087310137367648741111453 := by
  unfold tailWord_6012515
  simp only [CollatzResearch.WordTrace]
  refine ⟨219294437812692485654942999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146196291875128323769961999 219294437812692485654942999)
  ·
    refine ⟨328941656719038728482414499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219294437812692485654942999 328941656719038728482414499)
    ·
      refine ⟨493412485078558092723621749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328941656719038728482414499 493412485078558092723621749)
      ·
        refine ⟨46257420476114821192839539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 493412485078558092723621749 46257420476114821192839539)
        ·
          refine ⟨69386130714172231789259309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46257420476114821192839539 69386130714172231789259309)
          ·
            refine ⟨26019799017814586920972241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69386130714172231789259309 26019799017814586920972241)
            ·
              refine ⟨19514849263360940190729181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26019799017814586920972241 19514849263360940190729181)
              ·
                refine ⟨7318068473760352571523443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19514849263360940190729181 7318068473760352571523443)
                ·
                  refine ⟨10977102710640528857285165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7318068473760352571523443 10977102710640528857285165)
                  ·
                    refine ⟨4116413516490198321481937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10977102710640528857285165 4116413516490198321481937)
                    ·
                      refine ⟨3087310137367648741111453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116413516490198321481937 3087310137367648741111453)
                      ·
                        rfl

theorem cell23_6012515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_6012515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012515 prefixEnd_6012515 := by exact prefixLift 6012515
  have htrace : WordTrace (prefixWord ++ tailWord_6012515) baseStart_6012515 baseEnd_6012515 := by
    simpa [prefixWord, tailWord_6012515, baseEnd_6012515] using wordTrace_append hprefix tailTrace_6012515
  have hstable : (prefixWord ++ tailWord_6012515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012515).length < 2 ^ (prefixWord ++ tailWord_6012515).sum := by decide
  have hdescent : baseEnd_6012515 < baseStart_6012515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012561 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_6012561 : Nat := 118140960795 + 6012561 * 2 ^ 59
def prefixEnd_6012561 : Nat := 4983230072969 + 3 ^ 40 * 6012561 * 2
def baseEnd_6012561 : Nat := 3087333757477755561136241

theorem tailTrace_6012561 : CollatzResearch.WordTrace tailWord_6012561 prefixEnd_6012561 3087333757477755561136241 := by
  unfold tailWord_6012561
  simp only [CollatzResearch.WordTrace]
  refine ⟨219296115570525835511117537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146197410380350557007411691 219296115570525835511117537)
  ·
    refine ⟨164472086677894376633338153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219296115570525835511117537 164472086677894376633338153)
    ·
      refine ⟨123354065008420782475003615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164472086677894376633338153 123354065008420782475003615)
      ·
        refine ⟨185031097512631173712505423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123354065008420782475003615 185031097512631173712505423)
        ·
          refine ⟨277546646268946760568758135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185031097512631173712505423 277546646268946760568758135)
          ·
            refine ⟨416319969403420140853137203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277546646268946760568758135 416319969403420140853137203)
            ·
              refine ⟨624479954105130211279705805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416319969403420140853137203 624479954105130211279705805)
              ·
                refine ⟨234179982789423829229889677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624479954105130211279705805 234179982789423829229889677)
                ·
                  refine ⟨87817493546033935961208629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234179982789423829229889677 87817493546033935961208629)
                  ·
                    refine ⟨8232890019940681496363309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87817493546033935961208629 8232890019940681496363309)
                    ·
                      refine ⟨3087333757477755561136241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8232890019940681496363309 3087333757477755561136241)
                      ·
                        rfl

theorem cell23_6012561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_6012561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012561 prefixEnd_6012561 := by exact prefixLift 6012561
  have htrace : WordTrace (prefixWord ++ tailWord_6012561) baseStart_6012561 baseEnd_6012561 := by
    simpa [prefixWord, tailWord_6012561, baseEnd_6012561] using wordTrace_append hprefix tailTrace_6012561
  have hstable : (prefixWord ++ tailWord_6012561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012561).length < 2 ^ (prefixWord ++ tailWord_6012561).sum := by decide
  have hdescent : baseEnd_6012561 < baseStart_6012561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012562 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6012562 : Nat := 118140960795 + 6012562 * 2 ^ 59
def prefixEnd_6012562 : Nat := 4983230072969 + 3 ^ 40 * 6012562 * 2
def baseEnd_6012562 : Nat := 3087334270958410057223737

theorem tailTrace_6012562 : CollatzResearch.WordTrace tailWord_6012562 prefixEnd_6012562 3087334270958410057223737 := by
  unfold tailWord_6012562
  simp only [CollatzResearch.WordTrace]
  refine ⟨54824038010880553170475985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146197434695681475121269293 54824038010880553170475985)
  ·
    refine ⟨41118028508160414877856989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54824038010880553170475985 41118028508160414877856989)
    ·
      refine ⟨15419260690560155579196371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41118028508160414877856989 15419260690560155579196371)
      ·
        refine ⟨23128891035840233368794557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15419260690560155579196371 23128891035840233368794557)
        ·
          refine ⟨8673334138440087513297959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23128891035840233368794557 8673334138440087513297959)
          ·
            refine ⟨13010001207660131269946939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673334138440087513297959 13010001207660131269946939)
            ·
              refine ⟨19515001811490196904920409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13010001207660131269946939 19515001811490196904920409)
              ·
                refine ⟨14636251358617647678690307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19515001811490196904920409 14636251358617647678690307)
                ·
                  refine ⟨21954377037926471518035461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14636251358617647678690307 21954377037926471518035461)
                  ·
                    refine ⟨4116445694611213409631649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21954377037926471518035461 4116445694611213409631649)
                    ·
                      refine ⟨3087334270958410057223737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116445694611213409631649 3087334270958410057223737)
                      ·
                        rfl

theorem cell23_6012562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6012562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012562 prefixEnd_6012562 := by exact prefixLift 6012562
  have htrace : WordTrace (prefixWord ++ tailWord_6012562) baseStart_6012562 baseEnd_6012562 := by
    simpa [prefixWord, tailWord_6012562, baseEnd_6012562] using wordTrace_append hprefix tailTrace_6012562
  have hstable : (prefixWord ++ tailWord_6012562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012562).length < 2 ^ (prefixWord ++ tailWord_6012562).sum := by decide
  have hdescent : baseEnd_6012562 < baseStart_6012562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012591 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_6012591 : Nat := 118140960795 + 6012591 * 2 ^ 59
def prefixEnd_6012591 : Nat := 4983230072969 + 3 ^ 40 * 6012591 * 2
def baseEnd_6012591 : Nat := 3087349161897390443761103

theorem tailTrace_6012591 : CollatzResearch.WordTrace tailWord_6012591 prefixEnd_6012591 3087349161897390443761103 := by
  unfold tailWord_6012591
  simp only [CollatzResearch.WordTrace]
  refine ⟨219297209760417150634709627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146198139840278100423139751 219297209760417150634709627)
  ·
    refine ⟨328945814640625725952064441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219297209760417150634709627 328945814640625725952064441)
    ·
      refine ⟨246709360980469294464048331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328945814640625725952064441 246709360980469294464048331)
      ·
        refine ⟨370064041470703941696072497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246709360980469294464048331 370064041470703941696072497)
        ·
          refine ⟨277548031103027956272054373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370064041470703941696072497 277548031103027956272054373)
          ·
            refine ⟨52040255831817741801010195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277548031103027956272054373 52040255831817741801010195)
            ·
              refine ⟨78060383747726612701515293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52040255831817741801010195 78060383747726612701515293)
              ·
                refine ⟨29272643905397479763068235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78060383747726612701515293 29272643905397479763068235)
                ·
                  refine ⟨43908965858096219644602353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29272643905397479763068235 43908965858096219644602353)
                  ·
                    refine ⟨32931724393572164733451765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43908965858096219644602353 32931724393572164733451765)
                    ·
                      refine ⟨3087349161897390443761103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32931724393572164733451765 3087349161897390443761103)
                      ·
                        rfl

theorem cell23_6012591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_6012591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012591 prefixEnd_6012591 := by exact prefixLift 6012591
  have htrace : WordTrace (prefixWord ++ tailWord_6012591) baseStart_6012591 baseEnd_6012591 := by
    simpa [prefixWord, tailWord_6012591, baseEnd_6012591] using wordTrace_append hprefix tailTrace_6012591
  have hstable : (prefixWord ++ tailWord_6012591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012591).length < 2 ^ (prefixWord ++ tailWord_6012591).sum := by decide
  have hdescent : baseEnd_6012591 < baseStart_6012591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012630 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6012630 : Nat := 118140960795 + 6012630 * 2 ^ 59
def prefixEnd_6012630 : Nat := 4983230072969 + 3 ^ 40 * 6012630 * 2
def baseEnd_6012630 : Nat := 3087369187642915791173425

theorem tailTrace_6012630 : CollatzResearch.WordTrace tailWord_6012630 prefixEnd_6012630 3087369187642915791173425 := by
  unfold tailWord_6012630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13706164512954741268461209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146199088138183906863586229 13706164512954741268461209)
  ·
    refine ⟨10279623384716055951345907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13706164512954741268461209 10279623384716055951345907)
    ·
      refine ⟨15419435077074083927018861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279623384716055951345907 15419435077074083927018861)
      ·
        refine ⟨5782288153902781472632073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15419435077074083927018861 5782288153902781472632073)
        ·
          refine ⟨4336716115427086104474055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5782288153902781472632073 4336716115427086104474055)
          ·
            refine ⟨6505074173140629156711083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336716115427086104474055 6505074173140629156711083)
            ·
              refine ⟨9757611259710943735066625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505074173140629156711083 9757611259710943735066625)
              ·
                refine ⟨7318208444783207801299969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9757611259710943735066625 7318208444783207801299969)
                ·
                  refine ⟨5488656333587405850974977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7318208444783207801299969 5488656333587405850974977)
                  ·
                    refine ⟨4116492250190554388231233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5488656333587405850974977 4116492250190554388231233)
                    ·
                      refine ⟨3087369187642915791173425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116492250190554388231233 3087369187642915791173425)
                      ·
                        rfl

theorem cell23_6012630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6012630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012630 prefixEnd_6012630 := by exact prefixLift 6012630
  have htrace : WordTrace (prefixWord ++ tailWord_6012630) baseStart_6012630 baseEnd_6012630 := by
    simpa [prefixWord, tailWord_6012630, baseEnd_6012630] using wordTrace_append hprefix tailTrace_6012630
  have hstable : (prefixWord ++ tailWord_6012630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012630).length < 2 ^ (prefixWord ++ tailWord_6012630).sum := by decide
  have hdescent : baseEnd_6012630 < baseStart_6012630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012631 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_6012631 : Nat := 118140960795 + 6012631 * 2 ^ 59
def prefixEnd_6012631 : Nat := 4983230072969 + 3 ^ 40 * 6012631 * 2
def baseEnd_6012631 : Nat := 3087369701123570287260919

theorem tailTrace_6012631 : CollatzResearch.WordTrace tailWord_6012631 prefixEnd_6012631 3087369701123570287260919 := by
  unfold tailWord_6012631
  simp only [CollatzResearch.WordTrace]
  refine ⟨219298668680272237466165747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146199112453514824977443831 219298668680272237466165747)
  ·
    refine ⟨328948003020408356199248621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219298668680272237466165747 328948003020408356199248621)
    ·
      refine ⟨123355501132653133574718233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328948003020408356199248621 123355501132653133574718233)
      ·
        refine ⟨92516625849489850181038675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123355501132653133574718233 92516625849489850181038675)
        ·
          refine ⟨138774938774234775271558013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92516625849489850181038675 138774938774234775271558013)
          ·
            refine ⟨52040602040338040726834255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138774938774234775271558013 52040602040338040726834255)
            ·
              refine ⟨78060903060507061090251383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52040602040338040726834255 78060903060507061090251383)
              ·
                refine ⟨117091354590760591635377075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78060903060507061090251383 117091354590760591635377075)
                ·
                  refine ⟨175637031886140887453065613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117091354590760591635377075 175637031886140887453065613)
                  ·
                    refine ⟨65863886957302832794899605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175637031886140887453065613 65863886957302832794899605)
                    ·
                      refine ⟨3087369701123570287260919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65863886957302832794899605 3087369701123570287260919)
                      ·
                        rfl

theorem cell23_6012631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_6012631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012631 prefixEnd_6012631 := by exact prefixLift 6012631
  have htrace : WordTrace (prefixWord ++ tailWord_6012631) baseStart_6012631 baseEnd_6012631 := by
    simpa [prefixWord, tailWord_6012631, baseEnd_6012631] using wordTrace_append hprefix tailTrace_6012631
  have hstable : (prefixWord ++ tailWord_6012631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012631).length < 2 ^ (prefixWord ++ tailWord_6012631).sum := by decide
  have hdescent : baseEnd_6012631 < baseStart_6012631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012645 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_6012645 : Nat := 118140960795 + 6012645 * 2 ^ 59
def prefixEnd_6012645 : Nat := 4983230072969 + 3 ^ 40 * 6012645 * 2
def baseEnd_6012645 : Nat := 1029125629950911077495285

theorem tailTrace_6012645 : CollatzResearch.WordTrace tailWord_6012645 prefixEnd_6012645 1029125629950911077495285 := by
  unfold tailWord_6012645
  simp only [CollatzResearch.WordTrace]
  refine ⟨219299179302221517857175389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146199452868147678571450259 219299179302221517857175389)
  ·
    refine ⟨82237192238333069196440771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219299179302221517857175389 82237192238333069196440771)
    ·
      refine ⟨123355788357499603794661157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82237192238333069196440771 123355788357499603794661157)
      ·
        refine ⟨23129210317031175711498967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123355788357499603794661157 23129210317031175711498967)
        ·
          refine ⟨34693815475546763567248451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23129210317031175711498967 34693815475546763567248451)
          ·
            refine ⟨52040723213320145350872677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34693815475546763567248451 52040723213320145350872677)
            ·
              refine ⟨9757635602497527253288627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52040723213320145350872677 9757635602497527253288627)
              ·
                refine ⟨14636453403746290879932941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757635602497527253288627 14636453403746290879932941)
                ·
                  refine ⟨5488670026404859079974853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14636453403746290879932941 5488670026404859079974853)
                  ·
                    refine ⟨1029125629950911077495285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488670026404859079974853 1029125629950911077495285)
                    ·
                      rfl

theorem cell23_6012645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_6012645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012645 prefixEnd_6012645 := by exact prefixLift 6012645
  have htrace : WordTrace (prefixWord ++ tailWord_6012645) baseStart_6012645 baseEnd_6012645 := by
    simpa [prefixWord, tailWord_6012645, baseEnd_6012645] using wordTrace_append hprefix tailTrace_6012645
  have hstable : (prefixWord ++ tailWord_6012645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012645).length < 2 ^ (prefixWord ++ tailWord_6012645).sum := by decide
  have hdescent : baseEnd_6012645 < baseStart_6012645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012668 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_6012668 : Nat := 118140960795 + 6012668 * 2 ^ 59
def prefixEnd_6012668 : Nat := 4983230072969 + 3 ^ 40 * 6012668 * 2
def baseEnd_6012668 : Nat := 3087388699907786642498249

theorem tailTrace_6012668 : CollatzResearch.WordTrace tailWord_6012668 prefixEnd_6012668 3087388699907786642498249 := by
  unfold tailWord_6012668
  simp only [CollatzResearch.WordTrace]
  refine ⟨109650009090569096392631329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146200012120758795190175105 109650009090569096392631329)
  ·
    refine ⟨82237506817926822294473497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109650009090569096392631329 82237506817926822294473497)
    ·
      refine ⟨61678130113445116720855123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82237506817926822294473497 61678130113445116720855123)
      ·
        refine ⟨92517195170167675081282685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61678130113445116720855123 92517195170167675081282685)
        ·
          refine ⟨34693948188812878155481007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92517195170167675081282685 34693948188812878155481007)
          ·
            refine ⟨52040922283219317233221511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34693948188812878155481007 52040922283219317233221511)
            ·
              refine ⟨78061383424828975849832267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52040922283219317233221511 78061383424828975849832267)
              ·
                refine ⟨117092075137243463774748401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78061383424828975849832267 117092075137243463774748401)
                ·
                  refine ⟨87819056352932597831061301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117092075137243463774748401 87819056352932597831061301)
                  ·
                    refine ⟨8233036533087431046661997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87819056352932597831061301 8233036533087431046661997)
                    ·
                      refine ⟨3087388699907786642498249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233036533087431046661997 3087388699907786642498249)
                      ·
                        rfl

theorem cell23_6012668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_6012668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012668 prefixEnd_6012668 := by exact prefixLift 6012668
  have htrace : WordTrace (prefixWord ++ tailWord_6012668) baseStart_6012668 baseEnd_6012668 := by
    simpa [prefixWord, tailWord_6012668, baseEnd_6012668] using wordTrace_append hprefix tailTrace_6012668
  have hstable : (prefixWord ++ tailWord_6012668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012668).length < 2 ^ (prefixWord ++ tailWord_6012668).sum := by decide
  have hdescent : baseEnd_6012668 < baseStart_6012668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012722 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_6012722 : Nat := 118140960795 + 6012722 * 2 ^ 59
def prefixEnd_6012722 : Nat := 4983230072969 + 3 ^ 40 * 6012722 * 2
def baseEnd_6012722 : Nat := 1029138809287709810407667

theorem tailTrace_6012722 : CollatzResearch.WordTrace tailWord_6012722 prefixEnd_6012722 1029138809287709810407667 := by
  unfold tailWord_6012722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54825496930735640001932105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146201325148628373338485613 54825496930735640001932105)
  ·
    refine ⟨41119122698051730001449079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54825496930735640001932105 41119122698051730001449079)
    ·
      refine ⟨61678684047077595002173619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41119122698051730001449079 61678684047077595002173619)
      ·
        refine ⟨92518026070616392503260429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61678684047077595002173619 92518026070616392503260429)
        ·
          refine ⟨34694259776481147188722661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92518026070616392503260429 34694259776481147188722661)
          ·
            refine ⟨6505173708090215097885499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34694259776481147188722661 6505173708090215097885499)
            ·
              refine ⟨9757760562135322646828249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505173708090215097885499 9757760562135322646828249)
              ·
                refine ⟨7318320421601491985121187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9757760562135322646828249 7318320421601491985121187)
                ·
                  refine ⟨10977480632402237977681781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7318320421601491985121187 10977480632402237977681781)
                  ·
                    refine ⟨1029138809287709810407667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10977480632402237977681781 1029138809287709810407667)
                    ·
                      rfl

theorem cell23_6012722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_6012722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012722 prefixEnd_6012722 := by exact prefixLift 6012722
  have htrace : WordTrace (prefixWord ++ tailWord_6012722) baseStart_6012722 baseEnd_6012722 := by
    simpa [prefixWord, tailWord_6012722, baseEnd_6012722] using wordTrace_append hprefix tailTrace_6012722
  have hstable : (prefixWord ++ tailWord_6012722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012722).length < 2 ^ (prefixWord ++ tailWord_6012722).sum := by decide
  have hdescent : baseEnd_6012722 < baseStart_6012722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012735 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 1, 6]
def baseStart_6012735 : Nat := 118140960795 + 6012735 * 2 ^ 59
def prefixEnd_6012735 : Nat := 4983230072969 + 3 ^ 40 * 6012735 * 2
def baseEnd_6012735 : Nat := 1029141034370545960120147

theorem tailTrace_6012735 : CollatzResearch.WordTrace tailWord_6012735 prefixEnd_6012735 1029141034370545960120147 := by
  unfold tailWord_6012735
  simp only [CollatzResearch.WordTrace]
  refine ⟨219302461871895463227951659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146201641247930308818634439 219302461871895463227951659)
  ·
    refine ⟨328953692807843194841927489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219302461871895463227951659 328953692807843194841927489)
    ·
      refine ⟨246715269605882396131445617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328953692807843194841927489 246715269605882396131445617)
      ·
        refine ⟨185036452204411797098584213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246715269605882396131445617 185036452204411797098584213)
        ·
          refine ⟨8673583697081802988996135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185036452204411797098584213 8673583697081802988996135)
          ·
            refine ⟨13010375545622704483494203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673583697081802988996135 13010375545622704483494203)
            ·
              refine ⟨19515563318434056725241305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13010375545622704483494203 19515563318434056725241305)
              ·
                refine ⟨14636672488825542543930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19515563318434056725241305 14636672488825542543930979)
                ·
                  refine ⟨21955008733238313815896469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14636672488825542543930979 21955008733238313815896469)
                  ·
                    refine ⟨1029141034370545960120147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21955008733238313815896469 1029141034370545960120147)
                    ·
                      rfl

theorem cell23_6012735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_6012735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012735 prefixEnd_6012735 := by exact prefixLift 6012735
  have htrace : WordTrace (prefixWord ++ tailWord_6012735) baseStart_6012735 baseEnd_6012735 := by
    simpa [prefixWord, tailWord_6012735, baseEnd_6012735] using wordTrace_append hprefix tailTrace_6012735
  have hstable : (prefixWord ++ tailWord_6012735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012735).length < 2 ^ (prefixWord ++ tailWord_6012735).sum := by decide
  have hdescent : baseEnd_6012735 < baseStart_6012735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012748 : List Nat := [2, 2, 1, 3, 4, 11]
def baseStart_6012748 : Nat := 118140960795 + 6012748 * 2 ^ 59
def prefixEnd_6012748 : Nat := 4983230072969 + 3 ^ 40 * 6012748 * 2
def baseEnd_6012748 : Nat := 12705472338930643331267

theorem tailTrace_6012748 : CollatzResearch.WordTrace tailWord_6012748 prefixEnd_6012748 12705472338930643331267 := by
  unfold tailWord_6012748
  simp only [CollatzResearch.WordTrace]
  refine ⟨109651468010424183224087449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146201957347232244298783265 109651468010424183224087449)
  ·
    refine ⟨82238601007818137418065587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109651468010424183224087449 82238601007818137418065587)
    ·
      refine ⟨123357901511727206127098381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82238601007818137418065587 123357901511727206127098381)
      ·
        refine ⟨46259213066897702297661893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123357901511727206127098381 46259213066897702297661893)
        ·
          refine ⟨8673602450043319180811605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46259213066897702297661893 8673602450043319180811605)
          ·
            refine ⟨12705472338930643331267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8673602450043319180811605 12705472338930643331267)
            ·
              rfl

theorem cell23_6012748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 11].length) (baseStart_6012748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012748 prefixEnd_6012748 := by exact prefixLift 6012748
  have htrace : WordTrace (prefixWord ++ tailWord_6012748) baseStart_6012748 baseEnd_6012748 := by
    simpa [prefixWord, tailWord_6012748, baseEnd_6012748] using wordTrace_append hprefix tailTrace_6012748
  have hstable : (prefixWord ++ tailWord_6012748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012748).length < 2 ^ (prefixWord ++ tailWord_6012748).sum := by decide
  have hdescent : baseEnd_6012748 < baseStart_6012748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012772 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_6012772 : Nat := 118140960795 + 6012772 * 2 ^ 59
def prefixEnd_6012772 : Nat := 4983230072969 + 3 ^ 40 * 6012772 * 2
def baseEnd_6012772 : Nat := 3087442101895854235597771

theorem tailTrace_6012772 : CollatzResearch.WordTrace tailWord_6012772 prefixEnd_6012772 3087442101895854235597771 := by
  unfold tailWord_6012772
  simp only [CollatzResearch.WordTrace]
  refine ⟨109651905686380709273524285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146202540915174279031365713 109651905686380709273524285)
  ·
    refine ⟨41119464632392765977571607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109651905686380709273524285 41119464632392765977571607)
    ·
      refine ⟨61679196948589148966357411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41119464632392765977571607 61679196948589148966357411)
      ·
        refine ⟨92518795422883723449536117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61679196948589148966357411 92518795422883723449536117)
        ·
          refine ⟨8673637070895349073394011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92518795422883723449536117 8673637070895349073394011)
          ·
            refine ⟨13010455606343023610091017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673637070895349073394011 13010455606343023610091017)
            ·
              refine ⟨9757841704757267707568263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13010455606343023610091017 9757841704757267707568263)
              ·
                refine ⟨14636762557135901561352395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757841704757267707568263 14636762557135901561352395)
                ·
                  refine ⟨21955143835703852342028593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14636762557135901561352395 21955143835703852342028593)
                  ·
                    refine ⟨16466357876777889256521445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21955143835703852342028593 16466357876777889256521445)
                    ·
                      refine ⟨3087442101895854235597771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16466357876777889256521445 3087442101895854235597771)
                      ·
                        rfl

theorem cell23_6012772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_6012772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012772 prefixEnd_6012772 := by exact prefixLift 6012772
  have htrace : WordTrace (prefixWord ++ tailWord_6012772) baseStart_6012772 baseEnd_6012772 := by
    simpa [prefixWord, tailWord_6012772, baseEnd_6012772] using wordTrace_append hprefix tailTrace_6012772
  have hstable : (prefixWord ++ tailWord_6012772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012772).length < 2 ^ (prefixWord ++ tailWord_6012772).sum := by decide
  have hdescent : baseEnd_6012772 < baseStart_6012772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012782 : List Nat := [4, 1, 2, 3, 1, 2, 3, 7]
def baseStart_6012782 : Nat := 118140960795 + 6012782 * 2 ^ 59
def prefixEnd_6012782 : Nat := 4983230072969 + 3 ^ 40 * 6012782 * 2
def baseEnd_6012782 : Nat := 114349897655644414684175

theorem tailTrace_6012782 : CollatzResearch.WordTrace tailWord_6012782 prefixEnd_6012782 114349897655644414684175 := by
  unfold tailWord_6012782
  simp only [CollatzResearch.WordTrace]
  refine ⟨27413022012840648781864075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146202784068483460169941733 27413022012840648781864075)
  ·
    refine ⟨41119533019260973172796113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27413022012840648781864075 41119533019260973172796113)
    ·
      refine ⟨30839649764445729879597085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41119533019260973172796113 30839649764445729879597085)
      ·
        refine ⟨11564868661667148704848907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30839649764445729879597085 11564868661667148704848907)
        ·
          refine ⟨17347302992500723057273361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564868661667148704848907 17347302992500723057273361)
          ·
            refine ⟨13010477244375542292955021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17347302992500723057273361 13010477244375542292955021)
            ·
              refine ⟨4878928966640828359858133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13010477244375542292955021 4878928966640828359858133)
              ·
                refine ⟨114349897655644414684175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4878928966640828359858133 114349897655644414684175)
                ·
                  rfl

theorem cell23_6012782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_6012782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012782 prefixEnd_6012782 := by exact prefixLift 6012782
  have htrace : WordTrace (prefixWord ++ tailWord_6012782) baseStart_6012782 baseEnd_6012782 := by
    simpa [prefixWord, tailWord_6012782, baseEnd_6012782] using wordTrace_append hprefix tailTrace_6012782
  have hstable : (prefixWord ++ tailWord_6012782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012782).length < 2 ^ (prefixWord ++ tailWord_6012782).sum := by decide
  have hdescent : baseEnd_6012782 < baseStart_6012782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012826 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6012826 : Nat := 118140960795 + 6012826 * 2 ^ 59
def prefixEnd_6012826 : Nat := 4983230072969 + 3 ^ 40 * 6012826 * 2
def baseEnd_6012826 : Nat := 3087469829851197024322523

theorem tailTrace_6012826 : CollatzResearch.WordTrace tailWord_6012826 prefixEnd_6012826 3087469829851197024322523 := by
  unfold tailWord_6012826
  simp only [CollatzResearch.WordTrace]
  refine ⟨54826445228641446442378583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146203853943043857179676221 54826445228641446442378583)
  ·
    refine ⟨82239667842962169663567875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54826445228641446442378583 82239667842962169663567875)
    ·
      refine ⟨123359501764443254495351813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82239667842962169663567875 123359501764443254495351813)
      ·
        refine ⟨23129906580833110217878465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123359501764443254495351813 23129906580833110217878465)
        ·
          refine ⟨17347429935624832663408849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23129906580833110217878465 17347429935624832663408849)
          ·
            refine ⟨13010572451718624497556637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17347429935624832663408849 13010572451718624497556637)
            ·
              refine ⟨4878964669394484186583739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13010572451718624497556637 4878964669394484186583739)
              ·
                refine ⟨7318447004091726279875609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878964669394484186583739 7318447004091726279875609)
                ·
                  refine ⟨5488835253068794709906707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7318447004091726279875609 5488835253068794709906707)
                  ·
                    refine ⟨8233252879603192064860061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5488835253068794709906707 8233252879603192064860061)
                    ·
                      refine ⟨3087469829851197024322523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233252879603192064860061 3087469829851197024322523)
                      ·
                        rfl

theorem cell23_6012826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6012826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012826 prefixEnd_6012826 := by exact prefixLift 6012826
  have htrace : WordTrace (prefixWord ++ tailWord_6012826) baseStart_6012826 baseEnd_6012826 := by
    simpa [prefixWord, tailWord_6012826, baseEnd_6012826] using wordTrace_append hprefix tailTrace_6012826
  have hstable : (prefixWord ++ tailWord_6012826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012826).length < 2 ^ (prefixWord ++ tailWord_6012826).sum := by decide
  have hdescent : baseEnd_6012826 < baseStart_6012826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012849 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6012849 : Nat := 118140960795 + 6012849 * 2 ^ 59
def prefixEnd_6012849 : Nat := 4983230072969 + 3 ^ 40 * 6012849 * 2
def baseEnd_6012849 : Nat := 3087481639906250434334917

theorem tailTrace_6012849 : CollatzResearch.WordTrace tailWord_6012849 prefixEnd_6012849 3087481639906250434334917 := by
  unfold tailWord_6012849
  simp only [CollatzResearch.WordTrace]
  refine ⟨219306619793482460697601601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146204413195654973798401067 219306619793482460697601601)
  ·
    refine ⟨164479964845111845523201201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219306619793482460697601601 164479964845111845523201201)
    ·
      refine ⟨123359973633833884142400901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164479964845111845523201201 123359973633833884142400901)
      ·
        refine ⟨23129995056343853276700169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123359973633833884142400901 23129995056343853276700169)
        ·
          refine ⟨17347496292257889957525127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23129995056343853276700169 17347496292257889957525127)
          ·
            refine ⟨26021244438386834936287691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17347496292257889957525127 26021244438386834936287691)
            ·
              refine ⟨39031866657580252404431537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26021244438386834936287691 39031866657580252404431537)
              ·
                refine ⟨29273899993185189303323653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39031866657580252404431537 29273899993185189303323653)
                ·
                  refine ⟨5488856248722222994373185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29273899993185189303323653 5488856248722222994373185)
                  ·
                    refine ⟨4116642186541667245779889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5488856248722222994373185 4116642186541667245779889)
                    ·
                      refine ⟨3087481639906250434334917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116642186541667245779889 3087481639906250434334917)
                      ·
                        rfl

theorem cell23_6012849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6012849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012849 prefixEnd_6012849 := by exact prefixLift 6012849
  have htrace : WordTrace (prefixWord ++ tailWord_6012849) baseStart_6012849 baseEnd_6012849 := by
    simpa [prefixWord, tailWord_6012849, baseEnd_6012849] using wordTrace_append hprefix tailTrace_6012849
  have hstable : (prefixWord ++ tailWord_6012849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012849).length < 2 ^ (prefixWord ++ tailWord_6012849).sum := by decide
  have hdescent : baseEnd_6012849 < baseStart_6012849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012872 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 7]
def baseStart_6012872 : Nat := 118140960795 + 6012872 * 2 ^ 59
def prefixEnd_6012872 : Nat := 4983230072969 + 3 ^ 40 * 6012872 * 2
def baseEnd_6012872 : Nat := 343054827773478204927479

theorem tailTrace_6012872 : CollatzResearch.WordTrace tailWord_6012872 prefixEnd_6012872 343054827773478204927479 := by
  unfold tailWord_6012872
  simp only [CollatzResearch.WordTrace]
  refine ⟨109653729336199567812844435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146204972448266090417125913 109653729336199567812844435)
  ·
    refine ⟨164480594004299351719266653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109653729336199567812844435 164480594004299351719266653)
    ·
      refine ⟨61680222751612256894724995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164480594004299351719266653 61680222751612256894724995)
      ·
        refine ⟨92520334127418385342087493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61680222751612256894724995 92520334127418385342087493)
        ·
          refine ⟨17347562648890947251641405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92520334127418385342087493 17347562648890947251641405)
          ·
            refine ⟨6505335993334105219365527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17347562648890947251641405 6505335993334105219365527)
            ·
              refine ⟨9758003990001157829048291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505335993334105219365527 9758003990001157829048291)
              ·
                refine ⟨14637005985001736743572437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9758003990001157829048291 14637005985001736743572437)
                ·
                  refine ⟨343054827773478204927479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14637005985001736743572437 343054827773478204927479)
                  ·
                    rfl

theorem cell23_6012872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_6012872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012872 prefixEnd_6012872 := by exact prefixLift 6012872
  have htrace : WordTrace (prefixWord ++ tailWord_6012872) baseStart_6012872 baseEnd_6012872 := by
    simpa [prefixWord, tailWord_6012872, baseEnd_6012872] using wordTrace_append hprefix tailTrace_6012872
  have hstable : (prefixWord ++ tailWord_6012872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012872).length < 2 ^ (prefixWord ++ tailWord_6012872).sum := by decide
  have hdescent : baseEnd_6012872 < baseStart_6012872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012942 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_6012942 : Nat := 118140960795 + 6012942 * 2 ^ 59
def prefixEnd_6012942 : Nat := 4983230072969 + 3 ^ 40 * 6012942 * 2
def baseEnd_6012942 : Nat := 3087529393607118570471989

theorem tailTrace_6012942 : CollatzResearch.WordTrace tailWord_6012942 prefixEnd_6012942 3087529393607118570471989 := by
  unfold tailWord_6012942
  simp only [CollatzResearch.WordTrace]
  refine ⟨27413751472768192197592135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146206674521430358387158053 27413751472768192197592135)
  ·
    refine ⟨41120627209152288296388203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27413751472768192197592135 41120627209152288296388203)
    ·
      refine ⟨61680940813728432444582305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41120627209152288296388203 61680940813728432444582305)
      ·
        refine ⟨46260705610296324333436729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61680940813728432444582305 46260705610296324333436729)
        ·
          refine ⟨34695529207722243250077547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46260705610296324333436729 34695529207722243250077547)
          ·
            refine ⟨52043293811583364875116321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34695529207722243250077547 52043293811583364875116321)
            ·
              refine ⟨39032470358687523656337241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52043293811583364875116321 39032470358687523656337241)
              ·
                refine ⟨29274352769015642742252931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39032470358687523656337241 29274352769015642742252931)
                ·
                  refine ⟨43911529153523464113379397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29274352769015642742252931 43911529153523464113379397)
                  ·
                    refine ⟨8233411716285649521258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43911529153523464113379397 8233411716285649521258637)
                    ·
                      refine ⟨3087529393607118570471989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233411716285649521258637 3087529393607118570471989)
                      ·
                        rfl

theorem cell23_6012942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_6012942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012942 prefixEnd_6012942 := by exact prefixLift 6012942
  have htrace : WordTrace (prefixWord ++ tailWord_6012942) baseStart_6012942 baseEnd_6012942 := by
    simpa [prefixWord, tailWord_6012942, baseEnd_6012942] using wordTrace_append hprefix tailTrace_6012942
  have hstable : (prefixWord ++ tailWord_6012942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012942).length < 2 ^ (prefixWord ++ tailWord_6012942).sum := by decide
  have hdescent : baseEnd_6012942 < baseStart_6012942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012949 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_6012949 : Nat := 118140960795 + 6012949 * 2 ^ 59
def prefixEnd_6012949 : Nat := 4983230072969 + 3 ^ 40 * 6012949 * 2
def baseEnd_6012949 : Nat := 1029177662657233347694819

theorem tailTrace_6012949 : CollatzResearch.WordTrace tailWord_6012949 prefixEnd_6012949 1029177662657233347694819 := by
  unfold tailWord_6012949
  simp only [CollatzResearch.WordTrace]
  refine ⟨219310267093120177776241901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146206844728746785184161267 219310267093120177776241901)
  ·
    refine ⟨82241350159920066666090713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219310267093120177776241901 82241350159920066666090713)
    ·
      refine ⟨61681012619940049999568035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82241350159920066666090713 61681012619940049999568035)
      ·
        refine ⟨92521518929910074999352053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61681012619940049999568035 92521518929910074999352053)
        ·
          refine ⟨8673892399679069531189255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92521518929910074999352053 8673892399679069531189255)
          ·
            refine ⟨13010838599518604296783883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673892399679069531189255 13010838599518604296783883)
            ·
              refine ⟨19516257899277906445175825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13010838599518604296783883 19516257899277906445175825)
              ·
                refine ⟨14637193424458429833881869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19516257899277906445175825 14637193424458429833881869)
                ·
                  refine ⟨5488947534171911187705701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14637193424458429833881869 5488947534171911187705701)
                  ·
                    refine ⟨1029177662657233347694819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488947534171911187705701 1029177662657233347694819)
                    ·
                      rfl

theorem cell23_6012949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_6012949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012949 prefixEnd_6012949 := by exact prefixLift 6012949
  have htrace : WordTrace (prefixWord ++ tailWord_6012949) baseStart_6012949 baseEnd_6012949 := by
    simpa [prefixWord, tailWord_6012949, baseEnd_6012949] using wordTrace_append hprefix tailTrace_6012949
  have hstable : (prefixWord ++ tailWord_6012949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012949).length < 2 ^ (prefixWord ++ tailWord_6012949).sum := by decide
  have hdescent : baseEnd_6012949 < baseStart_6012949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012955 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3]
def baseStart_6012955 : Nat := 118140960795 + 6012955 * 2 ^ 59
def prefixEnd_6012955 : Nat := 4983230072969 + 3 ^ 40 * 6012955 * 2
def baseEnd_6012955 : Nat := 3087536068855627019609429

theorem tailTrace_6012955 : CollatzResearch.WordTrace tailWord_6012955 prefixEnd_6012955 3087536068855627019609429 := by
  unfold tailWord_6012955
  simp only [CollatzResearch.WordTrace]
  refine ⟨219310485931098440800960319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146206990620732293867306879 219310485931098440800960319)
  ·
    refine ⟨328965728896647661201440479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219310485931098440800960319 328965728896647661201440479)
    ·
      refine ⟨493448593344971491802160719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328965728896647661201440479 493448593344971491802160719)
      ·
        refine ⟨740172890017457237703241079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493448593344971491802160719 740172890017457237703241079)
        ·
          refine ⟨1110259335026185856554861619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740172890017457237703241079 1110259335026185856554861619)
          ·
            refine ⟨1665389002539278784832292429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110259335026185856554861619 1665389002539278784832292429)
            ·
              refine ⟨624520875952229544312109661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1665389002539278784832292429 624520875952229544312109661)
              ·
                refine ⟨234195328482086079117041123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624520875952229544312109661 234195328482086079117041123)
                ·
                  refine ⟨351292992723129118675561685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234195328482086079117041123 351292992723129118675561685)
                  ·
                    refine ⟨8233429516948338718958477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 351292992723129118675561685 8233429516948338718958477)
                    ·
                      refine ⟨3087536068855627019609429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233429516948338718958477 3087536068855627019609429)
                      ·
                        rfl

theorem cell23_6012955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3].length) (baseStart_6012955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012955 prefixEnd_6012955 := by exact prefixLift 6012955
  have htrace : WordTrace (prefixWord ++ tailWord_6012955) baseStart_6012955 baseEnd_6012955 := by
    simpa [prefixWord, tailWord_6012955, baseEnd_6012955] using wordTrace_append hprefix tailTrace_6012955
  have hstable : (prefixWord ++ tailWord_6012955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012955).length < 2 ^ (prefixWord ++ tailWord_6012955).sum := by decide
  have hdescent : baseEnd_6012955 < baseStart_6012955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012975 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 5, 5]
def baseStart_6012975 : Nat := 118140960795 + 6012975 * 2 ^ 59
def prefixEnd_6012975 : Nat := 4983230072969 + 3 ^ 40 * 6012975 * 2
def baseEnd_6012975 : Nat := 1029182112822905647119779

theorem tailTrace_6012975 : CollatzResearch.WordTrace tailWord_6012975 prefixEnd_6012975 1029182112822905647119779 := by
  unfold tailWord_6012975
  simp only [CollatzResearch.WordTrace]
  refine ⟨219311215391025984216688379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146207476927350656144458919 219311215391025984216688379)
  ·
    refine ⟨328966823086538976325032569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219311215391025984216688379 328966823086538976325032569)
    ·
      refine ⟨246725117314904232243774427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328966823086538976325032569 246725117314904232243774427)
      ·
        refine ⟨370087675972356348365661641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246725117314904232243774427 370087675972356348365661641)
        ·
          refine ⟨277565756979267261274246231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370087675972356348365661641 277565756979267261274246231)
          ·
            refine ⟨416348635468900891911369347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277565756979267261274246231 416348635468900891911369347)
            ·
              refine ⟨624522953203351337867054021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416348635468900891911369347 624522953203351337867054021)
              ·
                refine ⟨117098053725628375850072629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624522953203351337867054021 117098053725628375850072629)
                ·
                  refine ⟨10977942536777660235944309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117098053725628375850072629 10977942536777660235944309)
                  ·
                    refine ⟨1029182112822905647119779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10977942536777660235944309 1029182112822905647119779)
                    ·
                      rfl

theorem cell23_6012975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_6012975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012975 prefixEnd_6012975 := by exact prefixLift 6012975
  have htrace : WordTrace (prefixWord ++ tailWord_6012975) baseStart_6012975 baseEnd_6012975 := by
    simpa [prefixWord, tailWord_6012975, baseEnd_6012975] using wordTrace_append hprefix tailTrace_6012975
  have hstable : (prefixWord ++ tailWord_6012975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012975).length < 2 ^ (prefixWord ++ tailWord_6012975).sum := by decide
  have hdescent : baseEnd_6012975 < baseStart_6012975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012982 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6012982 : Nat := 118140960795 + 6012982 * 2 ^ 59
def prefixEnd_6012982 : Nat := 4983230072969 + 3 ^ 40 * 6012982 * 2
def baseEnd_6012982 : Nat := 3087549932833298413971805

theorem tailTrace_6012982 : CollatzResearch.WordTrace tailWord_6012982 prefixEnd_6012982 3087549932833298413971805 := by
  unfold tailWord_6012982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13706966918875039025762075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146207647134667082941462133 13706966918875039025762075)
  ·
    refine ⟨20560450378312558538643113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13706966918875039025762075 20560450378312558538643113)
    ·
      refine ⟨15420337783734418903982335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20560450378312558538643113 15420337783734418903982335)
      ·
        refine ⟨23130506675601628355973503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15420337783734418903982335 23130506675601628355973503)
        ·
          refine ⟨34695760013402442533960255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23130506675601628355973503 34695760013402442533960255)
          ·
            refine ⟨52043640020103663800940383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34695760013402442533960255 52043640020103663800940383)
            ·
              refine ⟨78065460030155495701410575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52043640020103663800940383 78065460030155495701410575)
              ·
                refine ⟨117098190045233243552115863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78065460030155495701410575 117098190045233243552115863)
                ·
                  refine ⟨175647285067849865328173795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117098190045233243552115863 175647285067849865328173795)
                  ·
                    refine ⟨263470927601774797992260693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175647285067849865328173795 263470927601774797992260693)
                    ·
                      refine ⟨3087549932833298413971805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263470927601774797992260693 3087549932833298413971805)
                      ·
                        rfl

theorem cell23_6012982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6012982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012982 prefixEnd_6012982 := by exact prefixLift 6012982
  have htrace : WordTrace (prefixWord ++ tailWord_6012982) baseStart_6012982 baseEnd_6012982 := by
    simpa [prefixWord, tailWord_6012982, baseEnd_6012982] using wordTrace_append hprefix tailTrace_6012982
  have hstable : (prefixWord ++ tailWord_6012982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012982).length < 2 ^ (prefixWord ++ tailWord_6012982).sum := by decide
  have hdescent : baseEnd_6012982 < baseStart_6012982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6012995 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_6012995 : Nat := 118140960795 + 6012995 * 2 ^ 59
def prefixEnd_6012995 : Nat := 4983230072969 + 3 ^ 40 * 6012995 * 2
def baseEnd_6012995 : Nat := 3087556608081806863109245

theorem tailTrace_6012995 : CollatzResearch.WordTrace tailWord_6012995 prefixEnd_6012995 3087556608081806863109245 := by
  unfold tailWord_6012995
  simp only [CollatzResearch.WordTrace]
  refine ⟨219311944850953527632416439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146207963233969018421610959 219311944850953527632416439)
  ·
    refine ⟨328967917276430291448624659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219311944850953527632416439 328967917276430291448624659)
    ·
      refine ⟨493451875914645437172936989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328967917276430291448624659 493451875914645437172936989)
      ·
        refine ⟨185044453467992038939851371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493451875914645437172936989 185044453467992038939851371)
        ·
          refine ⟨277566680201988058409777057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185044453467992038939851371 277566680201988058409777057)
          ·
            refine ⟨208175010151491043807332793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277566680201988058409777057 208175010151491043807332793)
            ·
              refine ⟨156131257613618282855499595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208175010151491043807332793 156131257613618282855499595)
              ·
                refine ⟨234196886420427424283249393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156131257613618282855499595 234196886420427424283249393)
                ·
                  refine ⟨175647664815320568212437045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234196886420427424283249393 175647664815320568212437045)
                  ·
                    refine ⟨16466968576436303269915973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175647664815320568212437045 16466968576436303269915973)
                    ·
                      refine ⟨3087556608081806863109245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16466968576436303269915973 3087556608081806863109245)
                      ·
                        rfl

theorem cell23_6012995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_6012995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6012995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6012995 prefixEnd_6012995 := by exact prefixLift 6012995
  have htrace : WordTrace (prefixWord ++ tailWord_6012995) baseStart_6012995 baseEnd_6012995 := by
    simpa [prefixWord, tailWord_6012995, baseEnd_6012995] using wordTrace_append hprefix tailTrace_6012995
  have hstable : (prefixWord ++ tailWord_6012995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6012995).length < 2 ^ (prefixWord ++ tailWord_6012995).sum := by decide
  have hdescent : baseEnd_6012995 < baseStart_6012995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6012995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013029 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_6013029 : Nat := 118140960795 + 6013029 * 2 ^ 59
def prefixEnd_6013029 : Nat := 4983230072969 + 3 ^ 40 * 6013029 * 2
def baseEnd_6013029 : Nat := 3087574066424059730084089

theorem tailTrace_6013029 : CollatzResearch.WordTrace tailWord_6013029 prefixEnd_6013029 3087574066424059730084089 := by
  unfold tailWord_6013029
  simp only [CollatzResearch.WordTrace]
  refine ⟨219313184932830351439154141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146208789955220234292769427 219313184932830351439154141)
  ·
    refine ⟨82242444349811381789682803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219313184932830351439154141 82242444349811381789682803)
    ·
      refine ⟨123363666524717072684524205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82242444349811381789682803 123363666524717072684524205)
      ·
        refine ⟨46261374946768902256696577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123363666524717072684524205 46261374946768902256696577)
        ·
          refine ⟨34696031210076676692522433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46261374946768902256696577 34696031210076676692522433)
          ·
            refine ⟨26022023407557507519391825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34696031210076676692522433 26022023407557507519391825)
            ·
              refine ⟨19516517555668130639543869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26022023407557507519391825 19516517555668130639543869)
              ·
                refine ⟨7318694083375548989828951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19516517555668130639543869 7318694083375548989828951)
                ·
                  refine ⟨10978041125063323484743427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7318694083375548989828951 10978041125063323484743427)
                  ·
                    refine ⟨16467061687594985227115141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10978041125063323484743427 16467061687594985227115141)
                    ·
                      refine ⟨3087574066424059730084089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16467061687594985227115141 3087574066424059730084089)
                      ·
                        rfl

theorem cell23_6013029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_6013029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013029 prefixEnd_6013029 := by exact prefixLift 6013029
  have htrace : WordTrace (prefixWord ++ tailWord_6013029) baseStart_6013029 baseEnd_6013029 := by
    simpa [prefixWord, tailWord_6013029, baseEnd_6013029] using wordTrace_append hprefix tailTrace_6013029
  have hstable : (prefixWord ++ tailWord_6013029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013029).length < 2 ^ (prefixWord ++ tailWord_6013029).sum := by decide
  have hdescent : baseEnd_6013029 < baseStart_6013029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013042 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6013042 : Nat := 118140960795 + 6013042 * 2 ^ 59
def prefixEnd_6013042 : Nat := 4983230072969 + 3 ^ 40 * 6013042 * 2
def baseEnd_6013042 : Nat := 3087580741672568179221529

theorem tailTrace_6013042 : CollatzResearch.WordTrace tailWord_6013042 prefixEnd_6013042 3087580741672568179221529 := by
  unfold tailWord_6013042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54828414770445813664844345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146209106054522169772918253 54828414770445813664844345)
  ·
    refine ⟨41121311077834360248633259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54828414770445813664844345 41121311077834360248633259)
    ·
      refine ⟨61681966616751540372949889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41121311077834360248633259 61681966616751540372949889)
      ·
        refine ⟨46261474962563655279712417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61681966616751540372949889 46261474962563655279712417)
        ·
          refine ⟨34696106221922741459784313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46261474962563655279712417 34696106221922741459784313)
          ·
            refine ⟨26022079666442056094838235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34696106221922741459784313 26022079666442056094838235)
            ·
              refine ⟨39033119499663084142257353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26022079666442056094838235 39033119499663084142257353)
              ·
                refine ⟨29274839624747313106693015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39033119499663084142257353 29274839624747313106693015)
                ·
                  refine ⟨43912259437120969660039523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29274839624747313106693015 43912259437120969660039523)
                  ·
                    refine ⟨65868389155681454490059285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43912259437120969660039523 65868389155681454490059285)
                    ·
                      refine ⟨3087580741672568179221529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65868389155681454490059285 3087580741672568179221529)
                      ·
                        rfl

theorem cell23_6013042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6013042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013042 prefixEnd_6013042 := by exact prefixLift 6013042
  have htrace : WordTrace (prefixWord ++ tailWord_6013042) baseStart_6013042 baseEnd_6013042 := by
    simpa [prefixWord, tailWord_6013042, baseEnd_6013042] using wordTrace_append hprefix tailTrace_6013042
  have hstable : (prefixWord ++ tailWord_6013042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013042).length < 2 ^ (prefixWord ++ tailWord_6013042).sum := by decide
  have hdescent : baseEnd_6013042 < baseStart_6013042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013052 : List Nat := [2, 2, 2, 1, 1, 5, 2, 8]
def baseStart_6013052 : Nat := 118140960795 + 6013052 * 2 ^ 59
def prefixEnd_6013052 : Nat := 4983230072969 + 3 ^ 40 * 6013052 * 2
def baseEnd_6013052 : Nat := 114355032462189375559129

theorem tailTrace_6013052 : CollatzResearch.WordTrace tailWord_6013052 prefixEnd_6013052 114355032462189375559129 := by
  unfold tailWord_6013052
  simp only [CollatzResearch.WordTrace]
  refine ⟨109657011905873513183620705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146209349207831350911494273 109657011905873513183620705)
  ·
    refine ⟨82242758929405134887715529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109657011905873513183620705 82242758929405134887715529)
    ·
      refine ⟨61682069197053851165786647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82242758929405134887715529 61682069197053851165786647)
      ·
        refine ⟨92523103795580776748679971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61682069197053851165786647 92523103795580776748679971)
        ·
          refine ⟨138784655693371165123019957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92523103795580776748679971 138784655693371165123019957)
          ·
            refine ⟨13011061471253546730283121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138784655693371165123019957 13011061471253546730283121)
            ·
              refine ⟨9758296103440160047712341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13011061471253546730283121 9758296103440160047712341)
              ·
                refine ⟨114355032462189375559129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9758296103440160047712341 114355032462189375559129)
                ·
                  rfl

theorem cell23_6013052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 8].length) (baseStart_6013052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013052 prefixEnd_6013052 := by exact prefixLift 6013052
  have htrace : WordTrace (prefixWord ++ tailWord_6013052) baseStart_6013052 baseEnd_6013052 := by
    simpa [prefixWord, tailWord_6013052, baseEnd_6013052] using wordTrace_append hprefix tailTrace_6013052
  have hstable : (prefixWord ++ tailWord_6013052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013052).length < 2 ^ (prefixWord ++ tailWord_6013052).sum := by decide
  have hdescent : baseEnd_6013052 < baseStart_6013052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013066 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6013066 : Nat := 118140960795 + 6013066 * 2 ^ 59
def prefixEnd_6013066 : Nat := 4983230072969 + 3 ^ 40 * 6013066 * 2
def baseEnd_6013066 : Nat := 3087593065208276085321419

theorem tailTrace_6013066 : CollatzResearch.WordTrace tailWord_6013066 prefixEnd_6013066 3087593065208276085321419 := by
  unfold tailWord_6013066
  simp only [CollatzResearch.WordTrace]
  refine ⟨54828633608424076689562763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146209689622464204505500701 54828633608424076689562763)
  ·
    refine ⟨82242950412636115034344145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54828633608424076689562763 82242950412636115034344145)
    ·
      refine ⟨61682212809477086275758109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82242950412636115034344145 61682212809477086275758109)
      ·
        refine ⟨23130829803553907353409291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61682212809477086275758109 23130829803553907353409291)
        ·
          refine ⟨34696244705330861030113937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23130829803553907353409291 34696244705330861030113937)
          ·
            refine ⟨26022183528998145772585453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34696244705330861030113937 26022183528998145772585453)
            ·
              refine ⟨9758318823374304664719545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26022183528998145772585453 9758318823374304664719545)
              ·
                refine ⟨7318739117530728498539659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9758318823374304664719545 7318739117530728498539659)
                ·
                  refine ⟨10978108676296092747809489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7318739117530728498539659 10978108676296092747809489)
                  ·
                    refine ⟨8233581507222069560857117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10978108676296092747809489 8233581507222069560857117)
                    ·
                      refine ⟨3087593065208276085321419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233581507222069560857117 3087593065208276085321419)
                      ·
                        rfl

theorem cell23_6013066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6013066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013066 prefixEnd_6013066 := by exact prefixLift 6013066
  have htrace : WordTrace (prefixWord ++ tailWord_6013066) baseStart_6013066 baseEnd_6013066 := by
    simpa [prefixWord, tailWord_6013066, baseEnd_6013066] using wordTrace_append hprefix tailTrace_6013066
  have hstable : (prefixWord ++ tailWord_6013066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013066).length < 2 ^ (prefixWord ++ tailWord_6013066).sum := by decide
  have hdescent : baseEnd_6013066 < baseStart_6013066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013112 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_6013112 : Nat := 118140960795 + 6013112 * 2 ^ 59
def prefixEnd_6013112 : Nat := 4983230072969 + 3 ^ 40 * 6013112 * 2
def baseEnd_6013112 : Nat := 1029205561772794301782069

theorem tailTrace_6013112 : CollatzResearch.WordTrace tailWord_6013112 prefixEnd_6013112 1029205561772794301782069 := by
  unfold tailWord_6013112
  simp only [CollatzResearch.WordTrace]
  refine ⟨109658106095764828307212795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146210808127686437742950393 109658106095764828307212795)
  ·
    refine ⟨164487159143647242460819193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109658106095764828307212795 164487159143647242460819193)
    ·
      refine ⟨123365369357735431845614395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164487159143647242460819193 123365369357735431845614395)
      ·
        refine ⟨185048054036603147768421593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123365369357735431845614395 185048054036603147768421593)
        ·
          refine ⟨138786040527452360826316195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185048054036603147768421593 138786040527452360826316195)
          ·
            refine ⟨208179060791178541239474293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138786040527452360826316195 208179060791178541239474293)
            ·
              refine ⟨19516786949172988241200715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208179060791178541239474293 19516786949172988241200715)
              ·
                refine ⟨29275180423759482361801073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19516786949172988241200715 29275180423759482361801073)
                ·
                  refine ⟨21956385317819611771350805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29275180423759482361801073 21956385317819611771350805)
                  ·
                    refine ⟨1029205561772794301782069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21956385317819611771350805 1029205561772794301782069)
                    ·
                      rfl

theorem cell23_6013112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_6013112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013112 prefixEnd_6013112 := by exact prefixLift 6013112
  have htrace : WordTrace (prefixWord ++ tailWord_6013112) baseStart_6013112 baseEnd_6013112 := by
    simpa [prefixWord, tailWord_6013112, baseEnd_6013112] using wordTrace_append hprefix tailTrace_6013112
  have hstable : (prefixWord ++ tailWord_6013112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013112).length < 2 ^ (prefixWord ++ tailWord_6013112).sum := by decide
  have hdescent : baseEnd_6013112 < baseStart_6013112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013159 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 7]
def baseStart_6013159 : Nat := 118140960795 + 6013159 * 2 ^ 59
def prefixEnd_6013159 : Nat := 4983230072969 + 3 ^ 40 * 6013159 * 2
def baseEnd_6013159 : Nat := 343071202101016024606499

theorem tailTrace_6013159 : CollatzResearch.WordTrace tailWord_6013159 prefixEnd_6013159 343071202101016024606499 := by
  unfold tailWord_6013159
  simp only [CollatzResearch.WordTrace]
  refine ⟨219317926422359383641386531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146211950948239589094257687 219317926422359383641386531)
  ·
    refine ⟨328976889633539075462079797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219317926422359383641386531 328976889633539075462079797)
    ·
      refine ⟨30841583403144288324569981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 328976889633539075462079797 30841583403144288324569981)
      ·
        refine ⟨11565593776179108121713743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30841583403144288324569981 11565593776179108121713743)
        ·
          refine ⟨17348390664268662182570615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565593776179108121713743 17348390664268662182570615)
          ·
            refine ⟨26022585996402993273855923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17348390664268662182570615 26022585996402993273855923)
            ·
              refine ⟨39033878994604489910783885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26022585996402993273855923 39033878994604489910783885)
              ·
                refine ⟨14637704622976683716543957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39033878994604489910783885 14637704622976683716543957)
                ·
                  refine ⟨343071202101016024606499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14637704622976683716543957 343071202101016024606499)
                  ·
                    rfl

theorem cell23_6013159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 7].length) (baseStart_6013159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013159 prefixEnd_6013159 := by exact prefixLift 6013159
  have htrace : WordTrace (prefixWord ++ tailWord_6013159) baseStart_6013159 baseEnd_6013159 := by
    simpa [prefixWord, tailWord_6013159, baseEnd_6013159] using wordTrace_append hprefix tailTrace_6013159
  have hstable : (prefixWord ++ tailWord_6013159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013159).length < 2 ^ (prefixWord ++ tailWord_6013159).sum := by decide
  have hdescent : baseEnd_6013159 < baseStart_6013159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013169 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_6013169 : Nat := 118140960795 + 6013169 * 2 ^ 59
def prefixEnd_6013169 : Nat := 4983230072969 + 3 ^ 40 * 6013169 * 2
def baseEnd_6013169 : Nat := 3087645953715689182333445

theorem tailTrace_6013169 : CollatzResearch.WordTrace tailWord_6013169 prefixEnd_6013169 3087645953715689182333445 := by
  unfold tailWord_6013169
  simp only [CollatzResearch.WordTrace]
  refine ⟨219318291152323155349250561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146212194101548770232833707 219318291152323155349250561)
  ·
    refine ⟨164488718364242366511937921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219318291152323155349250561 164488718364242366511937921)
    ·
      refine ⟨123366538773181774883953441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164488718364242366511937921 123366538773181774883953441)
      ·
        refine ⟨92524904079886331162965081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123366538773181774883953441 92524904079886331162965081)
        ·
          refine ⟨69393678059914748372223811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92524904079886331162965081 69393678059914748372223811)
          ·
            refine ⟨104090517089872122558335717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69393678059914748372223811 104090517089872122558335717)
            ·
              refine ⟨19516971954351022979687947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104090517089872122558335717 19516971954351022979687947)
              ·
                refine ⟨29275457931526534469531921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19516971954351022979687947 29275457931526534469531921)
                ·
                  refine ⟨21956593448644900852148941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29275457931526534469531921 21956593448644900852148941)
                  ·
                    refine ⟨8233722543241837819555853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21956593448644900852148941 8233722543241837819555853)
                    ·
                      refine ⟨3087645953715689182333445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233722543241837819555853 3087645953715689182333445)
                      ·
                        rfl

theorem cell23_6013169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_6013169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013169 prefixEnd_6013169 := by exact prefixLift 6013169
  have htrace : WordTrace (prefixWord ++ tailWord_6013169) baseStart_6013169 baseEnd_6013169 := by
    simpa [prefixWord, tailWord_6013169, baseEnd_6013169] using wordTrace_append hprefix tailTrace_6013169
  have hstable : (prefixWord ++ tailWord_6013169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013169).length < 2 ^ (prefixWord ++ tailWord_6013169).sum := by decide
  have hdescent : baseEnd_6013169 < baseStart_6013169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013232 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 10]
def baseStart_6013232 : Nat := 118140960795 + 6013232 * 2 ^ 59
def prefixEnd_6013232 : Nat := 4983230072969 + 3 ^ 40 * 6013232 * 2
def baseEnd_6013232 : Nat := 343075366999658048427295

theorem tailTrace_6013232 : CollatzResearch.WordTrace tailWord_6013232 prefixEnd_6013232 343075366999658048427295 := by
  unfold tailWord_6013232
  simp only [CollatzResearch.WordTrace]
  refine ⟨109660294475547458554396975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146213725967396611405862633 109660294475547458554396975)
  ·
    refine ⟨164490441713321187831595463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109660294475547458554396975 164490441713321187831595463)
    ·
      refine ⟨246735662569981781747393195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164490441713321187831595463 246735662569981781747393195)
      ·
        refine ⟨370103493854972672621089793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246735662569981781747393195 370103493854972672621089793)
        ·
          refine ⟨277577620391229504465817345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370103493854972672621089793 277577620391229504465817345)
          ·
            refine ⟨208183215293422128349363009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277577620391229504465817345 208183215293422128349363009)
            ·
              refine ⟨156137411470066596262022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208183215293422128349363009 156137411470066596262022257)
              ·
                refine ⟨117103058602549947196516693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156137411470066596262022257 117103058602549947196516693)
                ·
                  refine ⟨343075366999658048427295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117103058602549947196516693 343075366999658048427295)
                  ·
                    rfl

theorem cell23_6013232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_6013232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013232 prefixEnd_6013232 := by exact prefixLift 6013232
  have htrace : WordTrace (prefixWord ++ tailWord_6013232) baseStart_6013232 baseEnd_6013232 := by
    simpa [prefixWord, tailWord_6013232, baseEnd_6013232] using wordTrace_append hprefix tailTrace_6013232
  have hstable : (prefixWord ++ tailWord_6013232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013232).length < 2 ^ (prefixWord ++ tailWord_6013232).sum := by decide
  have hdescent : baseEnd_6013232 < baseStart_6013232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013279 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 3, 5]
def baseStart_6013279 : Nat := 118140960795 + 6013279 * 2 ^ 59
def prefixEnd_6013279 : Nat := 4983230072969 + 3 ^ 40 * 6013279 * 2
def baseEnd_6013279 : Nat := 1029234145529227917319313

theorem tailTrace_6013279 : CollatzResearch.WordTrace tailWord_6013279 prefixEnd_6013279 1029234145529227917319313 := by
  unfold tailWord_6013279
  simp only [CollatzResearch.WordTrace]
  refine ⟨219322303181924644135754891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146214868787949762757169927 219322303181924644135754891)
  ·
    refine ⟨328983454772886966203632337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219322303181924644135754891 328983454772886966203632337)
    ·
      refine ⟨246737591079665224652724253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328983454772886966203632337 246737591079665224652724253)
      ·
        refine ⟨92526596654874459244771595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246737591079665224652724253 92526596654874459244771595)
        ·
          refine ⟨138789894982311688867157393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92526596654874459244771595 138789894982311688867157393)
          ·
            refine ⟨104092421236733766650368045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138789894982311688867157393 104092421236733766650368045)
            ·
              refine ⟨39034657963775162493888017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104092421236733766650368045 39034657963775162493888017)
              ·
                refine ⟨29275993472831371870416013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39034657963775162493888017 29275993472831371870416013)
                ·
                  refine ⟨10978497552311764451406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29275993472831371870416013 10978497552311764451406005)
                  ·
                    refine ⟨1029234145529227917319313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10978497552311764451406005 1029234145529227917319313)
                    ·
                      rfl

theorem cell23_6013279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_6013279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013279 prefixEnd_6013279 := by exact prefixLift 6013279
  have htrace : WordTrace (prefixWord ++ tailWord_6013279) baseStart_6013279 baseEnd_6013279 := by
    simpa [prefixWord, tailWord_6013279, baseEnd_6013279] using wordTrace_append hprefix tailTrace_6013279
  have hstable : (prefixWord ++ tailWord_6013279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013279).length < 2 ^ (prefixWord ++ tailWord_6013279).sum := by decide
  have hdescent : baseEnd_6013279 < baseStart_6013279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013293 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6013293 : Nat := 118140960795 + 6013293 * 2 ^ 59
def prefixEnd_6013293 : Nat := 4983230072969 + 3 ^ 40 * 6013293 * 2
def baseEnd_6013293 : Nat := 3087709625316846697182875

theorem tailTrace_6013293 : CollatzResearch.WordTrace tailWord_6013293 prefixEnd_6013293 3087709625316846697182875 := by
  unfold tailWord_6013293
  simp only [CollatzResearch.WordTrace]
  refine ⟨219322813803873924526764533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146215209202582616351176355 219322813803873924526764533)
  ·
    refine ⟨20561513794113180424384175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219322813803873924526764533 20561513794113180424384175)
    ·
      refine ⟨30842270691169770636576263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20561513794113180424384175 30842270691169770636576263)
      ·
        refine ⟨46263406036754655954864395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30842270691169770636576263 46263406036754655954864395)
        ·
          refine ⟨69395109055131983932296593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46263406036754655954864395 69395109055131983932296593)
          ·
            refine ⟨52046331791348987949222445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69395109055131983932296593 52046331791348987949222445)
            ·
              refine ⟨19517374421755870480958417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52046331791348987949222445 19517374421755870480958417)
              ·
                refine ⟨14638030816316902860718813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19517374421755870480958417 14638030816316902860718813)
                ·
                  refine ⟨5489261556118838572769555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14638030816316902860718813 5489261556118838572769555)
                  ·
                    refine ⟨8233892334178257859154333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5489261556118838572769555 8233892334178257859154333)
                    ·
                      refine ⟨3087709625316846697182875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8233892334178257859154333 3087709625316846697182875)
                      ·
                        rfl

theorem cell23_6013293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6013293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013293 prefixEnd_6013293 := by exact prefixLift 6013293
  have htrace : WordTrace (prefixWord ++ tailWord_6013293) baseStart_6013293 baseEnd_6013293 := by
    simpa [prefixWord, tailWord_6013293, baseEnd_6013293] using wordTrace_append hprefix tailTrace_6013293
  have hstable : (prefixWord ++ tailWord_6013293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013293).length < 2 ^ (prefixWord ++ tailWord_6013293).sum := by decide
  have hdescent : baseEnd_6013293 < baseStart_6013293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013313 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6013313 : Nat := 118140960795 + 6013313 * 2 ^ 59
def prefixEnd_6013313 : Nat := 4983230072969 + 3 ^ 40 * 6013313 * 2
def baseEnd_6013313 : Nat := 1029239964976645539644261

theorem tailTrace_6013313 : CollatzResearch.WordTrace tailWord_6013313 prefixEnd_6013313 1029239964976645539644261 := by
  unfold tailWord_6013313
  simp only [CollatzResearch.WordTrace]
  refine ⟨219323543263801467942492593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146215695509200978628328395 219323543263801467942492593)
  ·
    refine ⟨164492657447851100956869445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219323543263801467942492593 164492657447851100956869445)
    ·
      refine ⟨30842373271472081429413021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164492657447851100956869445 30842373271472081429413021)
      ·
        refine ⟨11565889976802030536029883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30842373271472081429413021 11565889976802030536029883)
        ·
          refine ⟨17348834965203045804044825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565889976802030536029883 17348834965203045804044825)
          ·
            refine ⟨13011626223902284353033619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17348834965203045804044825 13011626223902284353033619)
            ·
              refine ⟨19517439335853426529550429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13011626223902284353033619 19517439335853426529550429)
              ·
                refine ⟨7319039750945034948581411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19517439335853426529550429 7319039750945034948581411)
                ·
                  refine ⟨10978559626417552422872117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319039750945034948581411 10978559626417552422872117)
                  ·
                    refine ⟨1029239964976645539644261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10978559626417552422872117 1029239964976645539644261)
                    ·
                      rfl

theorem cell23_6013313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6013313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013313 prefixEnd_6013313 := by exact prefixLift 6013313
  have htrace : WordTrace (prefixWord ++ tailWord_6013313) baseStart_6013313 baseEnd_6013313 := by
    simpa [prefixWord, tailWord_6013313, baseEnd_6013313] using wordTrace_append hprefix tailTrace_6013313
  have hstable : (prefixWord ++ tailWord_6013313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013313).length < 2 ^ (prefixWord ++ tailWord_6013313).sum := by decide
  have hdescent : baseEnd_6013313 < baseStart_6013313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013334 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6013334 : Nat := 118140960795 + 6013334 * 2 ^ 59
def prefixEnd_6013334 : Nat := 4983230072969 + 3 ^ 40 * 6013334 * 2
def baseEnd_6013334 : Nat := 343081186447075670752243

theorem tailTrace_6013334 : CollatzResearch.WordTrace tailWord_6013334 prefixEnd_6013334 343081186447075670752243 := by
  unfold tailWord_6013334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13707769324795336783062941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146216206131150259019338037 13707769324795336783062941)
  ·
    refine ⟨5140413496798251293648603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13707769324795336783062941 5140413496798251293648603)
    ·
      refine ⟨7710620245197376940472905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140413496798251293648603 7710620245197376940472905)
      ·
        refine ⟨5782965183898032705354679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7710620245197376940472905 5782965183898032705354679)
        ·
          refine ⟨8674447775847049058032019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782965183898032705354679 8674447775847049058032019)
          ·
            refine ⟨13011671663770573587048029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8674447775847049058032019 13011671663770573587048029)
            ·
              refine ⟨4879376873913965095143011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13011671663770573587048029 4879376873913965095143011)
              ·
                refine ⟨7319065310870947642714517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879376873913965095143011 7319065310870947642714517)
                ·
                  refine ⟨343081186447075670752243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7319065310870947642714517 343081186447075670752243)
                  ·
                    rfl

theorem cell23_6013334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6013334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013334 prefixEnd_6013334 := by exact prefixLift 6013334
  have htrace : WordTrace (prefixWord ++ tailWord_6013334) baseStart_6013334 baseEnd_6013334 := by
    simpa [prefixWord, tailWord_6013334, baseEnd_6013334] using wordTrace_append hprefix tailTrace_6013334
  have hstable : (prefixWord ++ tailWord_6013334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013334).length < 2 ^ (prefixWord ++ tailWord_6013334).sum := by decide
  have hdescent : baseEnd_6013334 < baseStart_6013334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013336 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6013336 : Nat := 118140960795 + 6013336 * 2 ^ 59
def prefixEnd_6013336 : Nat := 4983230072969 + 3 ^ 40 * 6013336 * 2
def baseEnd_6013336 : Nat := 3087731704984990028945177

theorem tailTrace_6013336 : CollatzResearch.WordTrace tailWord_6013336 prefixEnd_6013336 3087731704984990028945177 := by
  unfold tailWord_6013336
  simp only [CollatzResearch.WordTrace]
  refine ⟨109662191071359071435289931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146216254761812095247053241 109662191071359071435289931)
  ·
    refine ⟨164493286607038607152934897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109662191071359071435289931 164493286607038607152934897)
    ·
      refine ⟨123369964955278955364701173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164493286607038607152934897 123369964955278955364701173)
      ·
        refine ⟨11565934214557402065440735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123369964955278955364701173 11565934214557402065440735)
        ·
          refine ⟨17348901321836103098161103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565934214557402065440735 17348901321836103098161103)
          ·
            refine ⟨26023351982754154647241655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17348901321836103098161103 26023351982754154647241655)
            ·
              refine ⟨39035027974131231970862483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26023351982754154647241655 39035027974131231970862483)
              ·
                refine ⟨58552541961196847956293725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39035027974131231970862483 58552541961196847956293725)
                ·
                  refine ⟨21957203235448817983610147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58552541961196847956293725 21957203235448817983610147)
                  ·
                    refine ⟨32935804853173226975415221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21957203235448817983610147 32935804853173226975415221)
                    ·
                      refine ⟨3087731704984990028945177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32935804853173226975415221 3087731704984990028945177)
                      ·
                        rfl

theorem cell23_6013336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6013336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013336 prefixEnd_6013336 := by exact prefixLift 6013336
  have htrace : WordTrace (prefixWord ++ tailWord_6013336) baseStart_6013336 baseEnd_6013336 := by
    simpa [prefixWord, tailWord_6013336, baseEnd_6013336] using wordTrace_append hprefix tailTrace_6013336
  have hstable : (prefixWord ++ tailWord_6013336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013336).length < 2 ^ (prefixWord ++ tailWord_6013336).sum := by decide
  have hdescent : baseEnd_6013336 < baseStart_6013336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013346 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6013346 : Nat := 118140960795 + 6013346 * 2 ^ 59
def prefixEnd_6013346 : Nat := 4983230072969 + 3 ^ 40 * 6013346 * 2
def baseEnd_6013346 : Nat := 3087736839791534989820131

theorem tailTrace_6013346 : CollatzResearch.WordTrace tailWord_6013346 prefixEnd_6013346 3087736839791534989820131 := by
  unfold tailWord_6013346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54831186718170478644610973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146216497915121276385629261 54831186718170478644610973)
  ·
    refine ⟨20561695019313929491729115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54831186718170478644610973 20561695019313929491729115)
    ·
      refine ⟨30842542528970894237593673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20561695019313929491729115 30842542528970894237593673)
      ·
        refine ⟨23131906896728170678195255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30842542528970894237593673 23131906896728170678195255)
        ·
          refine ⟨34697860345092256017292883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23131906896728170678195255 34697860345092256017292883)
          ·
            refine ⟨52046790517638384025939325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34697860345092256017292883 52046790517638384025939325)
            ·
              refine ⟨19517546444114394009727247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52046790517638384025939325 19517546444114394009727247)
              ·
                refine ⟨29276319666171591014590871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19517546444114394009727247 29276319666171591014590871)
                ·
                  refine ⟨43914479499257386521886307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29276319666171591014590871 43914479499257386521886307)
                  ·
                    refine ⟨65871719248886079782829461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43914479499257386521886307 65871719248886079782829461)
                    ·
                      refine ⟨3087736839791534989820131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65871719248886079782829461 3087736839791534989820131)
                      ·
                        rfl

theorem cell23_6013346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6013346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013346 prefixEnd_6013346 := by exact prefixLift 6013346
  have htrace : WordTrace (prefixWord ++ tailWord_6013346) baseStart_6013346 baseEnd_6013346 := by
    simpa [prefixWord, tailWord_6013346, baseEnd_6013346] using wordTrace_append hprefix tailTrace_6013346
  have hstable : (prefixWord ++ tailWord_6013346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013346).length < 2 ^ (prefixWord ++ tailWord_6013346).sum := by decide
  have hdescent : baseEnd_6013346 < baseStart_6013346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013367 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 1, 2, 2]
def baseStart_6013367 : Nat := 118140960795 + 6013367 * 2 ^ 59
def prefixEnd_6013367 : Nat := 4983230072969 + 3 ^ 40 * 6013367 * 2
def baseEnd_6013367 : Nat := 3087747622885279407657535

theorem tailTrace_6013367 : CollatzResearch.WordTrace tailWord_6013367 prefixEnd_6013367 3087747622885279407657535 := by
  unfold tailWord_6013367
  simp only [CollatzResearch.WordTrace]
  refine ⟨219325512805605835164958355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146217008537070556776638903 219325512805605835164958355)
  ·
    refine ⟨328988269208408752747437533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219325512805605835164958355 328988269208408752747437533)
    ·
      refine ⟨123370600953153282280289075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328988269208408752747437533 123370600953153282280289075)
      ·
        refine ⟨185055901429729923420433613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123370600953153282280289075 185055901429729923420433613)
        ·
          refine ⟨69395963036148721282662605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185055901429729923420433613 69395963036148721282662605)
          ·
            refine ⟨26023486138555770480998477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69395963036148721282662605 26023486138555770480998477)
            ·
              refine ⟨9758807301958413930374429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26023486138555770480998477 9758807301958413930374429)
              ·
                refine ⟨3659552738234405223890411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9758807301958413930374429 3659552738234405223890411)
                ·
                  refine ⟨5489329107351607835835617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659552738234405223890411 5489329107351607835835617)
                  ·
                    refine ⟨4116996830513705876876713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5489329107351607835835617 4116996830513705876876713)
                    ·
                      refine ⟨3087747622885279407657535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4116996830513705876876713 3087747622885279407657535)
                      ·
                        rfl

theorem cell23_6013367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_6013367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013367 prefixEnd_6013367 := by exact prefixLift 6013367
  have htrace : WordTrace (prefixWord ++ tailWord_6013367) baseStart_6013367 baseEnd_6013367 := by
    simpa [prefixWord, tailWord_6013367, baseEnd_6013367] using wordTrace_append hprefix tailTrace_6013367
  have hstable : (prefixWord ++ tailWord_6013367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013367).length < 2 ^ (prefixWord ++ tailWord_6013367).sum := by decide
  have hdescent : baseEnd_6013367 < baseStart_6013367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013379 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_6013379 : Nat := 118140960795 + 6013379 * 2 ^ 59
def prefixEnd_6013379 : Nat := 4983230072969 + 3 ^ 40 * 6013379 * 2
def baseEnd_6013379 : Nat := 3087753784653133360707479

theorem tailTrace_6013379 : CollatzResearch.WordTrace tailWord_6013379 prefixEnd_6013379 3087753784653133360707479 := by
  unfold tailWord_6013379
  simp only [CollatzResearch.WordTrace]
  refine ⟨219325950481562361214395191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146217300321041574142930127 219325950481562361214395191)
  ·
    refine ⟨328988925722343541821592787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219325950481562361214395191 328988925722343541821592787)
    ·
      refine ⟨493483388583515312732389181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328988925722343541821592787 493483388583515312732389181)
      ·
        refine ⟨185056270718818242274645943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493483388583515312732389181 185056270718818242274645943)
        ·
          refine ⟨277584406078227363411968915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185056270718818242274645943 277584406078227363411968915)
          ·
            refine ⟨416376609117341045117953373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277584406078227363411968915 416376609117341045117953373)
            ·
              refine ⟨156141228419002891919232515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416376609117341045117953373 156141228419002891919232515)
              ·
                refine ⟨234211842628504337878848773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156141228419002891919232515 234211842628504337878848773)
                ·
                  refine ⟨43914720492844563352284145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234211842628504337878848773 43914720492844563352284145)
                  ·
                    refine ⟨32936040369633422514213109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43914720492844563352284145 32936040369633422514213109)
                    ·
                      refine ⟨3087753784653133360707479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32936040369633422514213109 3087753784653133360707479)
                      ·
                        rfl

theorem cell23_6013379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_6013379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013379 prefixEnd_6013379 := by exact prefixLift 6013379
  have htrace : WordTrace (prefixWord ++ tailWord_6013379) baseStart_6013379 baseEnd_6013379 := by
    simpa [prefixWord, tailWord_6013379, baseEnd_6013379] using wordTrace_append hprefix tailTrace_6013379
  have hstable : (prefixWord ++ tailWord_6013379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013379).length < 2 ^ (prefixWord ++ tailWord_6013379).sum := by decide
  have hdescent : baseEnd_6013379 < baseStart_6013379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013383 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_6013383 : Nat := 118140960795 + 6013383 * 2 ^ 59
def prefixEnd_6013383 : Nat := 4983230072969 + 3 ^ 40 * 6013383 * 2
def baseEnd_6013383 : Nat := 3087755838575751345057461

theorem tailTrace_6013383 : CollatzResearch.WordTrace tailWord_6013383 prefixEnd_6013383 3087755838575751345057461 := by
  unfold tailWord_6013383
  simp only [CollatzResearch.WordTrace]
  refine ⟨219326096373547869897540803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146217397582365246598360535 219326096373547869897540803)
  ·
    refine ⟨328989144560321804846311205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219326096373547869897540803 328989144560321804846311205)
    ·
      refine ⟨61685464605060338408683351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 328989144560321804846311205 61685464605060338408683351)
      ·
        refine ⟨92528196907590507613025027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61685464605060338408683351 92528196907590507613025027)
        ·
          refine ⟨138792295361385761419537541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92528196907590507613025027 138792295361385761419537541)
          ·
            refine ⟨26023555380259830266163289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138792295361385761419537541 26023555380259830266163289)
            ·
              refine ⟨19517666535194872699622467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26023555380259830266163289 19517666535194872699622467)
              ·
                refine ⟨29276499802792309049433701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19517666535194872699622467 29276499802792309049433701)
                ·
                  refine ⟨5489343713023557946768819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29276499802792309049433701 5489343713023557946768819)
                  ·
                    refine ⟨8234015569535336920153229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5489343713023557946768819 8234015569535336920153229)
                    ·
                      refine ⟨3087755838575751345057461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234015569535336920153229 3087755838575751345057461)
                      ·
                        rfl

theorem cell23_6013383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_6013383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013383 prefixEnd_6013383 := by exact prefixLift 6013383
  have htrace : WordTrace (prefixWord ++ tailWord_6013383) baseStart_6013383 baseEnd_6013383 := by
    simpa [prefixWord, tailWord_6013383, baseEnd_6013383] using wordTrace_append hprefix tailTrace_6013383
  have hstable : (prefixWord ++ tailWord_6013383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013383).length < 2 ^ (prefixWord ++ tailWord_6013383).sum := by decide
  have hdescent : baseEnd_6013383 < baseStart_6013383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013384 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_6013384 : Nat := 118140960795 + 6013384 * 2 ^ 59
def prefixEnd_6013384 : Nat := 4983230072969 + 3 ^ 40 * 6013384 * 2
def baseEnd_6013384 : Nat := 3087756352056405841144957

theorem tailTrace_6013384 : CollatzResearch.WordTrace tailWord_6013384 prefixEnd_6013384 3087756352056405841144957 := by
  unfold tailWord_6013384
  simp only [CollatzResearch.WordTrace]
  refine ⟨109663066423272123534163603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146217421897696164712218137 109663066423272123534163603)
  ·
    refine ⟨164494599634908185301245405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109663066423272123534163603 164494599634908185301245405)
    ·
      refine ⟨61685474863090569487967027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164494599634908185301245405 61685474863090569487967027)
      ·
        refine ⟨92528212294635854231950541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61685474863090569487967027 92528212294635854231950541)
        ·
          refine ⟨34698079610488445336981453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92528212294635854231950541 34698079610488445336981453)
          ·
            refine ⟨13011779853933167001368045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34698079610488445336981453 13011779853933167001368045)
            ·
              refine ⟨4879417445224937625513017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13011779853933167001368045 4879417445224937625513017)
              ·
                refine ⟨3659563083918703219134763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879417445224937625513017 3659563083918703219134763)
                ·
                  refine ⟨5489344625878054828702145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659563083918703219134763 5489344625878054828702145)
                  ·
                    refine ⟨4117008469408541121526609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5489344625878054828702145 4117008469408541121526609)
                    ·
                      refine ⟨3087756352056405841144957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117008469408541121526609 3087756352056405841144957)
                      ·
                        rfl

theorem cell23_6013384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_6013384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013384 prefixEnd_6013384 := by exact prefixLift 6013384
  have htrace : WordTrace (prefixWord ++ tailWord_6013384) baseStart_6013384 baseEnd_6013384 := by
    simpa [prefixWord, tailWord_6013384, baseEnd_6013384] using wordTrace_append hprefix tailTrace_6013384
  have hstable : (prefixWord ++ tailWord_6013384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013384).length < 2 ^ (prefixWord ++ tailWord_6013384).sum := by decide
  have hdescent : baseEnd_6013384 < baseStart_6013384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013394 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_6013394 : Nat := 118140960795 + 6013394 * 2 ^ 59
def prefixEnd_6013394 : Nat := 4983230072969 + 3 ^ 40 * 6013394 * 2
def baseEnd_6013394 : Nat := 1029253828954316934006637

theorem tailTrace_6013394 : CollatzResearch.WordTrace tailWord_6013394 prefixEnd_6013394 1029253828954316934006637 := by
  unfold tailWord_6013394
  simp only [CollatzResearch.WordTrace]
  refine ⟨54831624394127004694047809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146217665051005345850794157 54831624394127004694047809)
  ·
    refine ⟨41123718295595253520535857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54831624394127004694047809 41123718295595253520535857)
    ·
      refine ⟨30842788721696440140401893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41123718295595253520535857 30842788721696440140401893)
      ·
        refine ⟨5783022885318082526325355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30842788721696440140401893 5783022885318082526325355)
        ·
          refine ⟨8674534327977123789488033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783022885318082526325355 8674534327977123789488033)
          ·
            refine ⟨6505900745982842842116025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8674534327977123789488033 6505900745982842842116025)
            ·
              refine ⟨4879425559487132131587019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6505900745982842842116025 4879425559487132131587019)
              ·
                refine ⟨7319138339230698197380529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879425559487132131587019 7319138339230698197380529)
                ·
                  refine ⟨5489353754423023648035397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7319138339230698197380529 5489353754423023648035397)
                  ·
                    refine ⟨1029253828954316934006637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489353754423023648035397 1029253828954316934006637)
                    ·
                      rfl

theorem cell23_6013394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_6013394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013394 prefixEnd_6013394 := by exact prefixLift 6013394
  have htrace : WordTrace (prefixWord ++ tailWord_6013394) baseStart_6013394 baseEnd_6013394 := by
    simpa [prefixWord, tailWord_6013394, baseEnd_6013394] using wordTrace_append hprefix tailTrace_6013394
  have hstable : (prefixWord ++ tailWord_6013394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013394).length < 2 ^ (prefixWord ++ tailWord_6013394).sum := by decide
  have hdescent : baseEnd_6013394 < baseStart_6013394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013436 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_6013436 : Nat := 118140960795 + 6013436 * 2 ^ 59
def prefixEnd_6013436 : Nat := 4983230072969 + 3 ^ 40 * 6013436 * 2
def baseEnd_6013436 : Nat := 3087783053050439637694717

theorem tailTrace_6013436 : CollatzResearch.WordTrace tailWord_6013436 prefixEnd_6013436 3087783053050439637694717 := by
  unfold tailWord_6013436
  simp only [CollatzResearch.WordTrace]
  refine ⟨109664014721177929974610081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146218686294903906632813441 109664014721177929974610081)
  ·
    refine ⟨82248011040883447480957561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109664014721177929974610081 82248011040883447480957561)
    ·
      refine ⟨61686008280662585610718171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82248011040883447480957561 61686008280662585610718171)
      ·
        refine ⟨92529012420993878416077257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61686008280662585610718171 92529012420993878416077257)
        ·
          refine ⟨69396759315745408812057943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92529012420993878416077257 69396759315745408812057943)
          ·
            refine ⟨104095138973618113218086915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69396759315745408812057943 104095138973618113218086915)
            ·
              refine ⟨156142708460427169827130373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104095138973618113218086915 156142708460427169827130373)
              ·
                refine ⟨29276757836330094342586945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156142708460427169827130373 29276757836330094342586945)
                ·
                  refine ⟨21957568377247570756940209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29276757836330094342586945 21957568377247570756940209)
                  ·
                    refine ⟨16468176282935678067705157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21957568377247570756940209 16468176282935678067705157)
                    ·
                      refine ⟨3087783053050439637694717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16468176282935678067705157 3087783053050439637694717)
                      ·
                        rfl

theorem cell23_6013436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_6013436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013436 prefixEnd_6013436 := by exact prefixLift 6013436
  have htrace : WordTrace (prefixWord ++ tailWord_6013436) baseStart_6013436 baseEnd_6013436 := by
    simpa [prefixWord, tailWord_6013436, baseEnd_6013436] using wordTrace_append hprefix tailTrace_6013436
  have hstable : (prefixWord ++ tailWord_6013436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013436).length < 2 ^ (prefixWord ++ tailWord_6013436).sum := by decide
  have hdescent : baseEnd_6013436 < baseStart_6013436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013480 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 5]
def baseStart_6013480 : Nat := 118140960795 + 6013480 * 2 ^ 59
def prefixEnd_6013480 : Nat := 4983230072969 + 3 ^ 40 * 6013480 * 2
def baseEnd_6013480 : Nat := 343089516244359718393835

theorem tailTrace_6013480 : CollatzResearch.WordTrace tailWord_6013480 prefixEnd_6013480 343089516244359718393835 := by
  unfold tailWord_6013480
  simp only [CollatzResearch.WordTrace]
  refine ⟨109664817127098227731910947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146219756169464303642547929 109664817127098227731910947)
  ·
    refine ⟨164497225690647341597866421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109664817127098227731910947 164497225690647341597866421)
    ·
      refine ⟨15421614908498188274799977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164497225690647341597866421 15421614908498188274799977)
      ·
        refine ⟨11566211181373641206099983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15421614908498188274799977 11566211181373641206099983)
        ·
          refine ⟨17349316772060461809149975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566211181373641206099983 17349316772060461809149975)
          ·
            refine ⟨26023975158090692713724963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17349316772060461809149975 26023975158090692713724963)
            ·
              refine ⟨39035962737136039070587445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26023975158090692713724963 39035962737136039070587445)
              ·
                refine ⟨3659621506606503662867573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39035962737136039070587445 3659621506606503662867573)
                ·
                  refine ⟨343089516244359718393835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3659621506606503662867573 343089516244359718393835)
                  ·
                    rfl

theorem cell23_6013480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 5].length) (baseStart_6013480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013480 prefixEnd_6013480 := by exact prefixLift 6013480
  have htrace : WordTrace (prefixWord ++ tailWord_6013480) baseStart_6013480 baseEnd_6013480 := by
    simpa [prefixWord, tailWord_6013480, baseEnd_6013480] using wordTrace_append hprefix tailTrace_6013480
  have hstable : (prefixWord ++ tailWord_6013480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013480).length < 2 ^ (prefixWord ++ tailWord_6013480).sum := by decide
  have hdescent : baseEnd_6013480 < baseStart_6013480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013508 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6013508 : Nat := 118140960795 + 6013508 * 2 ^ 59
def prefixEnd_6013508 : Nat := 4983230072969 + 3 ^ 40 * 6013508 * 2
def baseEnd_6013508 : Nat := 3087820023657563355994387

theorem tailTrace_6013508 : CollatzResearch.WordTrace tailWord_6013508 prefixEnd_6013508 3087820023657563355994387 := by
  unfold tailWord_6013508
  simp only [CollatzResearch.WordTrace]
  refine ⟨109665327749047508122920589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146220436998730010830560785 109665327749047508122920589)
  ·
    refine ⟨41124497905892815546095221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109665327749047508122920589 41124497905892815546095221)
    ·
      refine ⟨3855421678677451457446427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41124497905892815546095221 3855421678677451457446427)
      ·
        refine ⟨5783132518016177186169641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855421678677451457446427 5783132518016177186169641)
        ·
          refine ⟨4337349388512132889627231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5783132518016177186169641 4337349388512132889627231)
          ·
            refine ⟨6506024082768199334440847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337349388512132889627231 6506024082768199334440847)
            ·
              refine ⟨9759036124152299001661271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506024082768199334440847 9759036124152299001661271)
              ·
                refine ⟨14638554186228448502491907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759036124152299001661271 14638554186228448502491907)
                ·
                  refine ⟨21957831279342672753737861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14638554186228448502491907 21957831279342672753737861)
                  ·
                    refine ⟨4117093364876751141325849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21957831279342672753737861 4117093364876751141325849)
                    ·
                      refine ⟨3087820023657563355994387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117093364876751141325849 3087820023657563355994387)
                      ·
                        rfl

theorem cell23_6013508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6013508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013508 prefixEnd_6013508 := by exact prefixLift 6013508
  have htrace : WordTrace (prefixWord ++ tailWord_6013508) baseStart_6013508 baseEnd_6013508 := by
    simpa [prefixWord, tailWord_6013508, baseEnd_6013508] using wordTrace_append hprefix tailTrace_6013508
  have hstable : (prefixWord ++ tailWord_6013508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013508).length < 2 ^ (prefixWord ++ tailWord_6013508).sum := by decide
  have hdescent : baseEnd_6013508 < baseStart_6013508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013510 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_6013510 : Nat := 118140960795 + 6013510 * 2 ^ 59
def prefixEnd_6013510 : Nat := 4983230072969 + 3 ^ 40 * 6013510 * 2
def baseEnd_6013510 : Nat := 1029273683539624116056459

theorem tailTrace_6013510 : CollatzResearch.WordTrace tailWord_6013510 prefixEnd_6013510 1029273683539624116056459 := by
  unfold tailWord_6013510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854085263877742830856687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146220485629391847058275989 6854085263877742830856687)
  ·
    refine ⟨10281127895816614246285031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6854085263877742830856687 10281127895816614246285031)
    ·
      refine ⟨15421691843724921369427547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281127895816614246285031 15421691843724921369427547)
      ·
        refine ⟨23132537765587382054141321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15421691843724921369427547 23132537765587382054141321)
        ·
          refine ⟨17349403324190536540605991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23132537765587382054141321 17349403324190536540605991)
          ·
            refine ⟨26024104986285804810908987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17349403324190536540605991 26024104986285804810908987)
            ·
              refine ⟨39036157479428707216363481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26024104986285804810908987 39036157479428707216363481)
              ·
                refine ⟨29277118109571530412272611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39036157479428707216363481 29277118109571530412272611)
                ·
                  refine ⟨43915677164357295618408917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29277118109571530412272611 43915677164357295618408917)
                  ·
                    refine ⟨1029273683539624116056459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43915677164357295618408917 1029273683539624116056459)
                    ·
                      rfl

theorem cell23_6013510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_6013510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013510 prefixEnd_6013510 := by exact prefixLift 6013510
  have htrace : WordTrace (prefixWord ++ tailWord_6013510) baseStart_6013510 baseEnd_6013510 := by
    simpa [prefixWord, tailWord_6013510, baseEnd_6013510] using wordTrace_append hprefix tailTrace_6013510
  have hstable : (prefixWord ++ tailWord_6013510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013510).length < 2 ^ (prefixWord ++ tailWord_6013510).sum := by decide
  have hdescent : baseEnd_6013510 < baseStart_6013510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013536 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 8]
def baseStart_6013536 : Nat := 118140960795 + 6013536 * 2 ^ 59
def prefixEnd_6013536 : Nat := 4983230072969 + 3 ^ 40 * 6013536 * 2
def baseEnd_6013536 : Nat := 343092711235098805160473

theorem tailTrace_6013536 : CollatzResearch.WordTrace tailWord_6013536 prefixEnd_6013536 343092711235098805160473 := by
  unfold tailWord_6013536
  simp only [CollatzResearch.WordTrace]
  refine ⟨109665838370996788513930231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146221117827995718018573641 109665838370996788513930231)
  ·
    refine ⟨164498757556495182770895347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109665838370996788513930231 164498757556495182770895347)
    ·
      refine ⟨246748136334742774156343021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164498757556495182770895347 246748136334742774156343021)
      ·
        refine ⟨92530551125528540308628633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246748136334742774156343021 92530551125528540308628633)
        ·
          refine ⟨69397913344146405231471475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92530551125528540308628633 69397913344146405231471475)
          ·
            refine ⟨104096870016219607847207213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69397913344146405231471475 104096870016219607847207213)
            ·
              refine ⟨39036326256082352942702705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104096870016219607847207213 39036326256082352942702705)
              ·
                refine ⟨29277244692061764707027029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39036326256082352942702705 29277244692061764707027029)
                ·
                  refine ⟨343092711235098805160473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29277244692061764707027029 343092711235098805160473)
                  ·
                    rfl

theorem cell23_6013536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_6013536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013536 prefixEnd_6013536 := by exact prefixLift 6013536
  have htrace : WordTrace (prefixWord ++ tailWord_6013536) baseStart_6013536 baseEnd_6013536 := by
    simpa [prefixWord, tailWord_6013536, baseEnd_6013536] using wordTrace_append hprefix tailTrace_6013536
  have hstable : (prefixWord ++ tailWord_6013536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013536).length < 2 ^ (prefixWord ++ tailWord_6013536).sum := by decide
  have hdescent : baseEnd_6013536 < baseStart_6013536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013550 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_6013550 : Nat := 118140960795 + 6013550 * 2 ^ 59
def prefixEnd_6013550 : Nat := 4983230072969 + 3 ^ 40 * 6013550 * 2
def baseEnd_6013550 : Nat := 3087841589845052191669193

theorem tailTrace_6013550 : CollatzResearch.WordTrace tailWord_6013550 prefixEnd_6013550 3087841589845052191669193 := by
  unfold tailWord_6013550
  simp only [CollatzResearch.WordTrace]
  refine ⟨27416523420492857177358763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146221458242628571612580069 27416523420492857177358763)
  ·
    refine ⟨41124785130739285766038145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27416523420492857177358763 41124785130739285766038145)
    ·
      refine ⟨30843588848054464324528609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41124785130739285766038145 30843588848054464324528609)
      ·
        refine ⟨23132691636040848243396457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30843588848054464324528609 23132691636040848243396457)
        ·
          refine ⟨17349518727030636182547343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23132691636040848243396457 17349518727030636182547343)
          ·
            refine ⟨26024278090545954273821015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17349518727030636182547343 26024278090545954273821015)
            ·
              refine ⟨39036417135818931410731523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26024278090545954273821015 39036417135818931410731523)
              ·
                refine ⟨58554625703728397116097285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39036417135818931410731523 58554625703728397116097285)
                ·
                  refine ⟨10978992319449074459268241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58554625703728397116097285 10978992319449074459268241)
                  ·
                    refine ⟨8234244239586805844451181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10978992319449074459268241 8234244239586805844451181)
                    ·
                      refine ⟨3087841589845052191669193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234244239586805844451181 3087841589845052191669193)
                      ·
                        rfl

theorem cell23_6013550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_6013550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013550 prefixEnd_6013550 := by exact prefixLift 6013550
  have htrace : WordTrace (prefixWord ++ tailWord_6013550) baseStart_6013550 baseEnd_6013550 := by
    simpa [prefixWord, tailWord_6013550, baseEnd_6013550] using wordTrace_append hprefix tailTrace_6013550
  have hstable : (prefixWord ++ tailWord_6013550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013550).length < 2 ^ (prefixWord ++ tailWord_6013550).sum := by decide
  have hdescent : baseEnd_6013550 < baseStart_6013550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013630 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_6013630 : Nat := 118140960795 + 6013630 * 2 ^ 59
def prefixEnd_6013630 : Nat := 4983230072969 + 3 ^ 40 * 6013630 * 2
def baseEnd_6013630 : Nat := 1029294222765803959556275

theorem tailTrace_6013630 : CollatzResearch.WordTrace tailWord_6013630 prefixEnd_6013630 1029294222765803959556275 := by
  unfold tailWord_6013630
  simp only [CollatzResearch.WordTrace]
  refine ⟨27416888150456628885222793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146223403469102020721188229 27416888150456628885222793)
  ·
    refine ⟨20562666112842471663917095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27416888150456628885222793 20562666112842471663917095)
    ·
      refine ⟨30843999169263707495875643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20562666112842471663917095 30843999169263707495875643)
      ·
        refine ⟨46265998753895561243813465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30843999169263707495875643 46265998753895561243813465)
        ·
          refine ⟨34699499065421670932860099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46265998753895561243813465 34699499065421670932860099)
          ·
            refine ⟨52049248598132506399290149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34699499065421670932860099 52049248598132506399290149)
            ·
              refine ⟨9759234112149844949866903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52049248598132506399290149 9759234112149844949866903)
              ·
                refine ⟨14638851168224767424800355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759234112149844949866903 14638851168224767424800355)
                ·
                  refine ⟨21958276752337151137200533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14638851168224767424800355 21958276752337151137200533)
                  ·
                    refine ⟨1029294222765803959556275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21958276752337151137200533 1029294222765803959556275)
                    ·
                      rfl

theorem cell23_6013630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_6013630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013630 prefixEnd_6013630 := by exact prefixLift 6013630
  have htrace : WordTrace (prefixWord ++ tailWord_6013630) baseStart_6013630 baseEnd_6013630 := by
    simpa [prefixWord, tailWord_6013630, baseEnd_6013630] using wordTrace_append hprefix tailTrace_6013630
  have hstable : (prefixWord ++ tailWord_6013630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013630).length < 2 ^ (prefixWord ++ tailWord_6013630).sum := by decide
  have hdescent : baseEnd_6013630 < baseStart_6013630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013640 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_6013640 : Nat := 118140960795 + 6013640 * 2 ^ 59
def prefixEnd_6013640 : Nat := 4983230072969 + 3 ^ 40 * 6013640 * 2
def baseEnd_6013640 : Nat := 3087887803103956839543779

theorem tailTrace_6013640 : CollatzResearch.WordTrace tailWord_6013640 prefixEnd_6013640 3087887803103956839543779 := by
  unfold tailWord_6013640
  simp only [CollatzResearch.WordTrace]
  refine ⟨109667734966808401394823187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146223646622411201859764249 109667734966808401394823187)
  ·
    refine ⟨164501602450212602092234781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109667734966808401394823187 164501602450212602092234781)
    ·
      refine ⟨61688100918829725784588043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164501602450212602092234781 61688100918829725784588043)
      ·
        refine ⟨92532151378244588676882065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61688100918829725784588043 92532151378244588676882065)
        ·
          refine ⟨69399113533683441507661549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92532151378244588676882065 69399113533683441507661549)
          ·
            refine ⟨26024667575131290565373081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69399113533683441507661549 26024667575131290565373081)
            ·
              refine ⟨19518500681348467924029811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26024667575131290565373081 19518500681348467924029811)
              ·
                refine ⟨29277751022022701886044717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19518500681348467924029811 29277751022022701886044717)
                ·
                  refine ⟨10979156633258513207266769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29277751022022701886044717 10979156633258513207266769)
                  ·
                    refine ⟨8234367474943884905450077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10979156633258513207266769 8234367474943884905450077)
                    ·
                      refine ⟨3087887803103956839543779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234367474943884905450077 3087887803103956839543779)
                      ·
                        rfl

theorem cell23_6013640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_6013640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013640 prefixEnd_6013640 := by exact prefixLift 6013640
  have htrace : WordTrace (prefixWord ++ tailWord_6013640) baseStart_6013640 baseEnd_6013640 := by
    simpa [prefixWord, tailWord_6013640, baseEnd_6013640] using wordTrace_append hprefix tailTrace_6013640
  have hstable : (prefixWord ++ tailWord_6013640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013640).length < 2 ^ (prefixWord ++ tailWord_6013640).sum := by decide
  have hdescent : baseEnd_6013640 < baseStart_6013640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013660 : List Nat := [2, 2, 5, 1, 1, 2, 10]
def baseStart_6013660 : Nat := 118140960795 + 6013660 * 2 ^ 59
def prefixEnd_6013660 : Nat := 4983230072969 + 3 ^ 40 * 6013660 * 2
def baseEnd_6013660 : Nat := 38122198428605515571527

theorem tailTrace_6013660 : CollatzResearch.WordTrace tailWord_6013660 prefixEnd_6013660 38122198428605515571527 := by
  unfold tailWord_6013660
  simp only [CollatzResearch.WordTrace]
  refine ⟨109668099696772173102687217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146224132929029564136916289 109668099696772173102687217)
  ·
    refine ⟨82251074772579129827015413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109668099696772173102687217 82251074772579129827015413)
    ·
      refine ⟨7711038259929293421282695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82251074772579129827015413 7711038259929293421282695)
      ·
        refine ⟨11566557389893940131924043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711038259929293421282695 11566557389893940131924043)
        ·
          refine ⟨17349836084840910197886065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566557389893940131924043 17349836084840910197886065)
          ·
            refine ⟨13012377063630682648414549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17349836084840910197886065 13012377063630682648414549)
            ·
              refine ⟨38122198428605515571527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13012377063630682648414549 38122198428605515571527)
              ·
                rfl

theorem cell23_6013660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 10].length) (baseStart_6013660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013660 prefixEnd_6013660 := by exact prefixLift 6013660
  have htrace : WordTrace (prefixWord ++ tailWord_6013660) baseStart_6013660 baseEnd_6013660 := by
    simpa [prefixWord, tailWord_6013660, baseEnd_6013660] using wordTrace_append hprefix tailTrace_6013660
  have hstable : (prefixWord ++ tailWord_6013660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013660).length < 2 ^ (prefixWord ++ tailWord_6013660).sum := by decide
  have hdescent : baseEnd_6013660 < baseStart_6013660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013684 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6013684 : Nat := 118140960795 + 6013684 * 2 ^ 59
def prefixEnd_6013684 : Nat := 4983230072969 + 3 ^ 40 * 6013684 * 2
def baseEnd_6013684 : Nat := 3087910396252754667393577

theorem tailTrace_6013684 : CollatzResearch.WordTrace tailWord_6013684 prefixEnd_6013684 3087910396252754667393577 := by
  unfold tailWord_6013684
  simp only [CollatzResearch.WordTrace]
  refine ⟨109668537372728699152124053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146224716496971598869498737 109668537372728699152124053)
  ·
    refine ⟨5140712689346657772755815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109668537372728699152124053 5140712689346657772755815)
    ·
      refine ⟨7711069034019986659133723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140712689346657772755815 7711069034019986659133723)
      ·
        refine ⟨11566603551029979988700585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711069034019986659133723 11566603551029979988700585)
        ·
          refine ⟨8674952663272484991525439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11566603551029979988700585 8674952663272484991525439)
          ·
            refine ⟨13012428994908727487288159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8674952663272484991525439 13012428994908727487288159)
            ·
              refine ⟨19518643492363091230932239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13012428994908727487288159 19518643492363091230932239)
              ·
                refine ⟨29277965238544636846398359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19518643492363091230932239 29277965238544636846398359)
                ·
                  refine ⟨43916947857816955269597539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29277965238544636846398359 43916947857816955269597539)
                  ·
                    refine ⟨65875421786725432904396309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43916947857816955269597539 65875421786725432904396309)
                    ·
                      refine ⟨3087910396252754667393577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65875421786725432904396309 3087910396252754667393577)
                      ·
                        rfl

theorem cell23_6013684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6013684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013684 prefixEnd_6013684 := by exact prefixLift 6013684
  have htrace : WordTrace (prefixWord ++ tailWord_6013684) baseStart_6013684 baseEnd_6013684 := by
    simpa [prefixWord, tailWord_6013684, baseEnd_6013684] using wordTrace_append hprefix tailTrace_6013684
  have hstable : (prefixWord ++ tailWord_6013684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013684).length < 2 ^ (prefixWord ++ tailWord_6013684).sum := by decide
  have hdescent : baseEnd_6013684 < baseStart_6013684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013713 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_6013713 : Nat := 118140960795 + 6013713 * 2 ^ 59
def prefixEnd_6013713 : Nat := 4983230072969 + 3 ^ 40 * 6013713 * 2
def baseEnd_6013713 : Nat := 3087925287191735053930943

theorem tailTrace_6013713 : CollatzResearch.WordTrace tailWord_6013713 prefixEnd_6013713 3087925287191735053930943 := by
  unfold tailWord_6013713
  simp only [CollatzResearch.WordTrace]
  refine ⟨219338132462352336257053793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146225421641568224171369195 219338132462352336257053793)
  ·
    refine ⟨164503599346764252192790345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219338132462352336257053793 164503599346764252192790345)
    ·
      refine ⟨123377699510073189144592759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164503599346764252192790345 123377699510073189144592759)
      ·
        refine ⟨185066549265109783716889139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123377699510073189144592759 185066549265109783716889139)
        ·
          refine ⟨277599823897664675575333709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185066549265109783716889139 277599823897664675575333709)
          ·
            refine ⟨104099933961624253340750141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277599823897664675575333709 104099933961624253340750141)
            ·
              refine ⟨39037475235609095002781303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104099933961624253340750141 39037475235609095002781303)
              ·
                refine ⟨58556212853413642504171955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39037475235609095002781303 58556212853413642504171955)
                ·
                  refine ⟨87834319280120463756257933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58556212853413642504171955 87834319280120463756257933)
                  ·
                    refine ⟨32937869730045173908596725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87834319280120463756257933 32937869730045173908596725)
                    ·
                      refine ⟨3087925287191735053930943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32937869730045173908596725 3087925287191735053930943)
                      ·
                        rfl

theorem cell23_6013713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_6013713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013713 prefixEnd_6013713 := by exact prefixLift 6013713
  have htrace : WordTrace (prefixWord ++ tailWord_6013713) baseStart_6013713 baseEnd_6013713 := by
    simpa [prefixWord, tailWord_6013713, baseEnd_6013713] using wordTrace_append hprefix tailTrace_6013713
  have hstable : (prefixWord ++ tailWord_6013713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013713).length < 2 ^ (prefixWord ++ tailWord_6013713).sum := by decide
  have hdescent : baseEnd_6013713 < baseStart_6013713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013748 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6013748 : Nat := 118140960795 + 6013748 * 2 ^ 59
def prefixEnd_6013748 : Nat := 4983230072969 + 3 ^ 40 * 6013748 * 2
def baseEnd_6013748 : Nat := 3087943259014642416993283

theorem tailTrace_6013748 : CollatzResearch.WordTrace tailWord_6013748 prefixEnd_6013748 3087943259014642416993283 := by
  unfold tailWord_6013748
  simp only [CollatzResearch.WordTrace]
  refine ⟨109669704508612768617288949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146226272678150358156385265 109669704508612768617288949)
  ·
    refine ⟨10281534797682447057870839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109669704508612768617288949 10281534797682447057870839)
    ·
      refine ⟨15422302196523670586806259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281534797682447057870839 15422302196523670586806259)
      ·
        refine ⟨23133453294785505880209389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422302196523670586806259 23133453294785505880209389)
        ·
          refine ⟨8675044985544564705078521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23133453294785505880209389 8675044985544564705078521)
          ·
            refine ⟨6506283739158423528808891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8675044985544564705078521 6506283739158423528808891)
            ·
              refine ⟨9759425608737635293213337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506283739158423528808891 9759425608737635293213337)
              ·
                refine ⟨7319569206553226469910003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9759425608737635293213337 7319569206553226469910003)
                ·
                  refine ⟨10979353809829839704865005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319569206553226469910003 10979353809829839704865005)
                  ·
                    refine ⟨4117257678686189889324377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10979353809829839704865005 4117257678686189889324377)
                    ·
                      refine ⟨3087943259014642416993283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117257678686189889324377 3087943259014642416993283)
                      ·
                        rfl

theorem cell23_6013748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6013748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013748 prefixEnd_6013748 := by exact prefixLift 6013748
  have htrace : WordTrace (prefixWord ++ tailWord_6013748) baseStart_6013748 baseEnd_6013748 := by
    simpa [prefixWord, tailWord_6013748, baseEnd_6013748] using wordTrace_append hprefix tailTrace_6013748
  have hstable : (prefixWord ++ tailWord_6013748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013748).length < 2 ^ (prefixWord ++ tailWord_6013748).sum := by decide
  have hdescent : baseEnd_6013748 < baseStart_6013748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013761 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6013761 : Nat := 118140960795 + 6013761 * 2 ^ 59
def prefixEnd_6013761 : Nat := 4983230072969 + 3 ^ 40 * 6013761 * 2
def baseEnd_6013761 : Nat := 3087949934263150866130723

theorem tailTrace_6013761 : CollatzResearch.WordTrace tailWord_6013761 prefixEnd_6013761 3087949934263150866130723 := by
  unfold tailWord_6013761
  simp only [CollatzResearch.WordTrace]
  refine ⟨219339883166178440454801137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146226588777452293636534091 219339883166178440454801137)
  ·
    refine ⟨164504912374633830341100853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219339883166178440454801137 164504912374633830341100853)
    ·
      refine ⟨15422335535121921594478205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164504912374633830341100853 15422335535121921594478205)
      ·
        refine ⟨5783375825670720597929327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15422335535121921594478205 5783375825670720597929327)
        ·
          refine ⟨8675063738506080896893991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783375825670720597929327 8675063738506080896893991)
          ·
            refine ⟨13012595607759121345340987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675063738506080896893991 13012595607759121345340987)
            ·
              refine ⟨19518893411638682018011481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13012595607759121345340987 19518893411638682018011481)
              ·
                refine ⟨14639170058729011513508611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19518893411638682018011481 14639170058729011513508611)
                ·
                  refine ⟨21958755088093517270262917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14639170058729011513508611 21958755088093517270262917)
                  ·
                    refine ⟨4117266579017534488174297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21958755088093517270262917 4117266579017534488174297)
                    ·
                      refine ⟨3087949934263150866130723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117266579017534488174297 3087949934263150866130723)
                      ·
                        rfl

theorem cell23_6013761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6013761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013761 prefixEnd_6013761 := by exact prefixLift 6013761
  have htrace : WordTrace (prefixWord ++ tailWord_6013761) baseStart_6013761 baseEnd_6013761 := by
    simpa [prefixWord, tailWord_6013761, baseEnd_6013761] using wordTrace_append hprefix tailTrace_6013761
  have hstable : (prefixWord ++ tailWord_6013761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013761).length < 2 ^ (prefixWord ++ tailWord_6013761).sum := by decide
  have hdescent : baseEnd_6013761 < baseStart_6013761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013794 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6013794 : Nat := 118140960795 + 6013794 * 2 ^ 59
def prefixEnd_6013794 : Nat := 4983230072969 + 3 ^ 40 * 6013794 * 2
def baseEnd_6013794 : Nat := 3087966879124749237018071

theorem tailTrace_6013794 : CollatzResearch.WordTrace tailWord_6013794 prefixEnd_6013794 3087966879124749237018071 := by
  unfold tailWord_6013794
  simp only [CollatzResearch.WordTrace]
  refine ⟨54835271693764721772688109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146227391183372591393834957 54835271693764721772688109)
  ·
    refine ⟨20563226885161770664758041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54835271693764721772688109 20563226885161770664758041)
    ·
      refine ⟨15422420163871327998568531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20563226885161770664758041 15422420163871327998568531)
      ·
        refine ⟨23133630245806991997852797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422420163871327998568531 23133630245806991997852797)
        ·
          refine ⟨8675111342177621999194799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23133630245806991997852797 8675111342177621999194799)
          ·
            refine ⟨13012667013266432998792199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675111342177621999194799 13012667013266432998792199)
            ·
              refine ⟨19519000519899649498188299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13012667013266432998792199 19519000519899649498188299)
              ·
                refine ⟨29278500779849474247282449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19519000519899649498188299 29278500779849474247282449)
                ·
                  refine ⟨21958875584887105685461837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29278500779849474247282449 21958875584887105685461837)
                  ·
                    refine ⟨8234578344332664632048189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21958875584887105685461837 8234578344332664632048189)
                    ·
                      refine ⟨3087966879124749237018071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234578344332664632048189 3087966879124749237018071)
                      ·
                        rfl

theorem cell23_6013794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6013794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013794 prefixEnd_6013794 := by exact prefixLift 6013794
  have htrace : WordTrace (prefixWord ++ tailWord_6013794) baseStart_6013794 baseEnd_6013794 := by
    simpa [prefixWord, tailWord_6013794, baseEnd_6013794] using wordTrace_append hprefix tailTrace_6013794
  have hstable : (prefixWord ++ tailWord_6013794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013794).length < 2 ^ (prefixWord ++ tailWord_6013794).sum := by decide
  have hdescent : baseEnd_6013794 < baseStart_6013794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013814 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6013814 : Nat := 118140960795 + 6013814 * 2 ^ 59
def prefixEnd_6013814 : Nat := 4983230072969 + 3 ^ 40 * 6013814 * 2
def baseEnd_6013814 : Nat := 1029325716245946386255993

theorem tailTrace_6013814 : CollatzResearch.WordTrace tailWord_6013814 prefixEnd_6013814 1029325716245946386255993 := by
  unfold tailWord_6013814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708863514686651906655031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146227877489990953670986997 13708863514686651906655031)
  ·
    refine ⟨20563295272029977859982547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13708863514686651906655031 20563295272029977859982547)
    ·
      refine ⟨30844942908044966789973821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20563295272029977859982547 30844942908044966789973821)
      ·
        refine ⟨11566853590516862546240183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30844942908044966789973821 11566853590516862546240183)
        ·
          refine ⟨17350280385775293819360275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566853590516862546240183 17350280385775293819360275)
          ·
            refine ⟨26025420578662940729040413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17350280385775293819360275 26025420578662940729040413)
            ·
              refine ⟨9759532716998602773390155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26025420578662940729040413 9759532716998602773390155)
              ·
                refine ⟨14639299075497904160085233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759532716998602773390155 14639299075497904160085233)
                ·
                  refine ⟨10979474306623428120063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14639299075497904160085233 10979474306623428120063925)
                  ·
                    refine ⟨1029325716245946386255993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10979474306623428120063925 1029325716245946386255993)
                    ·
                      rfl

theorem cell23_6013814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6013814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013814 prefixEnd_6013814 := by exact prefixLift 6013814
  have htrace : WordTrace (prefixWord ++ tailWord_6013814) baseStart_6013814 baseEnd_6013814 := by
    simpa [prefixWord, tailWord_6013814, baseEnd_6013814] using wordTrace_append hprefix tailTrace_6013814
  have hstable : (prefixWord ++ tailWord_6013814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013814).length < 2 ^ (prefixWord ++ tailWord_6013814).sum := by decide
  have hdescent : baseEnd_6013814 < baseStart_6013814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013817 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_6013817 : Nat := 118140960795 + 6013817 * 2 ^ 59
def prefixEnd_6013817 : Nat := 4983230072969 + 3 ^ 40 * 6013817 * 2
def baseEnd_6013817 : Nat := 3087978689179802647030465

theorem tailTrace_6013817 : CollatzResearch.WordTrace tailWord_6013817 prefixEnd_6013817 3087978689179802647030465 := by
  unfold tailWord_6013817
  simp only [CollatzResearch.WordTrace]
  refine ⟨219341925653975562018839705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146227950435983708012559803 219341925653975562018839705)
  ·
    refine ⟨164506444240481671514129779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219341925653975562018839705 164506444240481671514129779)
    ·
      refine ⟨246759666360722507271194669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164506444240481671514129779 246759666360722507271194669)
      ·
        refine ⟨92534874885270940226698001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246759666360722507271194669 92534874885270940226698001)
        ·
          refine ⟨69401156163953205170023501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92534874885270940226698001 69401156163953205170023501)
          ·
            refine ⟨26025433561482451938758813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69401156163953205170023501 26025433561482451938758813)
            ·
              refine ⟨9759537585555919477034555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26025433561482451938758813 9759537585555919477034555)
              ·
                refine ⟨14639306378333879215551833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759537585555919477034555 14639306378333879215551833)
                ·
                  refine ⟨10979479783750409411663875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14639306378333879215551833 10979479783750409411663875)
                  ·
                    refine ⟨16469219675625614117495813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10979479783750409411663875 16469219675625614117495813)
                    ·
                      refine ⟨3087978689179802647030465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16469219675625614117495813 3087978689179802647030465)
                      ·
                        rfl

theorem cell23_6013817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_6013817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013817 prefixEnd_6013817 := by exact prefixLift 6013817
  have htrace : WordTrace (prefixWord ++ tailWord_6013817) baseStart_6013817 baseEnd_6013817 := by
    simpa [prefixWord, tailWord_6013817, baseEnd_6013817] using wordTrace_append hprefix tailTrace_6013817
  have hstable : (prefixWord ++ tailWord_6013817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013817).length < 2 ^ (prefixWord ++ tailWord_6013817).sum := by decide
  have hdescent : baseEnd_6013817 < baseStart_6013817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013834 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6013834 : Nat := 118140960795 + 6013834 * 2 ^ 59
def prefixEnd_6013834 : Nat := 4983230072969 + 3 ^ 40 * 6013834 * 2
def baseEnd_6013834 : Nat := 3087987418350929080517887

theorem tailTrace_6013834 : CollatzResearch.WordTrace tailWord_6013834 prefixEnd_6013834 3087987418350929080517887 := by
  unfold tailWord_6013834
  simp only [CollatzResearch.WordTrace]
  refine ⟨54835636423728493480552139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146228363796609315948139037 54835636423728493480552139)
  ·
    refine ⟨82253454635592740220828209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54835636423728493480552139 82253454635592740220828209)
    ·
      refine ⟨61690090976694555165621157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82253454635592740220828209 61690090976694555165621157)
      ·
        refine ⟨11566892058130229093553967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61690090976694555165621157 11566892058130229093553967)
        ·
          refine ⟨17350338087195343640330951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566892058130229093553967 17350338087195343640330951)
          ·
            refine ⟨26025507130793015460496427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17350338087195343640330951 26025507130793015460496427)
            ·
              refine ⟨39038260696189523190744641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26025507130793015460496427 39038260696189523190744641)
              ·
                refine ⟨29278695522142142393058481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39038260696189523190744641 29278695522142142393058481)
                ·
                  refine ⟨21959021641606606794793861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29278695522142142393058481 21959021641606606794793861)
                  ·
                    refine ⟨4117316557801238774023849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21959021641606606794793861 4117316557801238774023849)
                    ·
                      refine ⟨3087987418350929080517887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117316557801238774023849 3087987418350929080517887)
                      ·
                        rfl

theorem cell23_6013834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6013834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013834 prefixEnd_6013834 := by exact prefixLift 6013834
  have htrace : WordTrace (prefixWord ++ tailWord_6013834) baseStart_6013834 baseEnd_6013834 := by
    simpa [prefixWord, tailWord_6013834, baseEnd_6013834] using wordTrace_append hprefix tailTrace_6013834
  have hstable : (prefixWord ++ tailWord_6013834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013834).length < 2 ^ (prefixWord ++ tailWord_6013834).sum := by decide
  have hdescent : baseEnd_6013834 < baseStart_6013834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013844 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_6013844 : Nat := 118140960795 + 6013844 * 2 ^ 59
def prefixEnd_6013844 : Nat := 4983230072969 + 3 ^ 40 * 6013844 * 2
def baseEnd_6013844 : Nat := 1029330851052491347130947

theorem tailTrace_6013844 : CollatzResearch.WordTrace tailWord_6013844 prefixEnd_6013844 1029330851052491347130947 := by
  unfold tailWord_6013844
  simp only [CollatzResearch.WordTrace]
  refine ⟨109671455212438872815036293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146228606949918497086715057 109671455212438872815036293)
  ·
    refine ⟨20563397852332288652819305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109671455212438872815036293 20563397852332288652819305)
    ·
      refine ⟨15422548389249216489614479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20563397852332288652819305 15422548389249216489614479)
      ·
        refine ⟨23133822583873824734421719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422548389249216489614479 23133822583873824734421719)
        ·
          refine ⟨34700733875810737101632579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23133822583873824734421719 34700733875810737101632579)
          ·
            refine ⟨52051100813716105652448869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34700733875810737101632579 52051100813716105652448869)
            ·
              refine ⟨9759581402571769809834163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52051100813716105652448869 9759581402571769809834163)
              ·
                refine ⟨14639372103857654714751245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759581402571769809834163 14639372103857654714751245)
                ·
                  refine ⟨5489764538946620518031717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14639372103857654714751245 5489764538946620518031717)
                  ·
                    refine ⟨1029330851052491347130947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5489764538946620518031717 1029330851052491347130947)
                    ·
                      rfl

theorem cell23_6013844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_6013844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013844 prefixEnd_6013844 := by exact prefixLift 6013844
  have htrace : WordTrace (prefixWord ++ tailWord_6013844) baseStart_6013844 baseEnd_6013844 := by
    simpa [prefixWord, tailWord_6013844, baseEnd_6013844] using wordTrace_append hprefix tailTrace_6013844
  have hstable : (prefixWord ++ tailWord_6013844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013844).length < 2 ^ (prefixWord ++ tailWord_6013844).sum := by decide
  have hdescent : baseEnd_6013844 < baseStart_6013844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013860 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_6013860 : Nat := 118140960795 + 6013860 * 2 ^ 59
def prefixEnd_6013860 : Nat := 4983230072969 + 3 ^ 40 * 6013860 * 2
def baseEnd_6013860 : Nat := 3088000768847945978792767

theorem tailTrace_6013860 : CollatzResearch.WordTrace tailWord_6013860 prefixEnd_6013860 3088000768847945978792767 := by
  unfold tailWord_6013860
  simp only [CollatzResearch.WordTrace]
  refine ⟨109671746996409890181327517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146228995995213186908436689 109671746996409890181327517)
  ·
    refine ⟨41126905123653708817997819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109671746996409890181327517 41126905123653708817997819)
    ·
      refine ⟨61690357685480563226996729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41126905123653708817997819 61690357685480563226996729)
      ·
        refine ⟨46267768264110422420247547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61690357685480563226996729 46267768264110422420247547)
        ·
          refine ⟨69401652396165633630371321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46267768264110422420247547 69401652396165633630371321)
          ·
            refine ⟨52051239297124225222778491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69401652396165633630371321 52051239297124225222778491)
            ·
              refine ⟨78076858945686337834167737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52051239297124225222778491 78076858945686337834167737)
              ·
                refine ⟨58557644209264753375625803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78076858945686337834167737 58557644209264753375625803)
                ·
                  refine ⟨87836466313897130063438705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58557644209264753375625803 87836466313897130063438705)
                  ·
                    refine ⟨65877349735422847547579029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87836466313897130063438705 65877349735422847547579029)
                    ·
                      refine ⟨3088000768847945978792767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65877349735422847547579029 3088000768847945978792767)
                      ·
                        rfl

theorem cell23_6013860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_6013860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013860 prefixEnd_6013860 := by exact prefixLift 6013860
  have htrace : WordTrace (prefixWord ++ tailWord_6013860) baseStart_6013860 baseEnd_6013860 := by
    simpa [prefixWord, tailWord_6013860, baseEnd_6013860] using wordTrace_append hprefix tailTrace_6013860
  have hstable : (prefixWord ++ tailWord_6013860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013860).length < 2 ^ (prefixWord ++ tailWord_6013860).sum := by decide
  have hdescent : baseEnd_6013860 < baseStart_6013860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013934 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_6013934 : Nat := 118140960795 + 6013934 * 2 ^ 59
def prefixEnd_6013934 : Nat := 4983230072969 + 3 ^ 40 * 6013934 * 2
def baseEnd_6013934 : Nat := 1029346255472126229755809

theorem tailTrace_6013934 : CollatzResearch.WordTrace tailWord_6013934 prefixEnd_6013934 1029346255472126229755809 := by
  unfold tailWord_6013934
  simp only [CollatzResearch.WordTrace]
  refine ⟨27418274124318961375106107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146230795329701127333899237 27418274124318961375106107)
  ·
    refine ⟨41127411186478442062659161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27418274124318961375106107 41127411186478442062659161)
    ·
      refine ⟨30845558389858831546994371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41127411186478442062659161 30845558389858831546994371)
      ·
        refine ⟨46268337584788247320491557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30845558389858831546994371 46268337584788247320491557)
        ·
          refine ⟨8675313297147796372592167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46268337584788247320491557 8675313297147796372592167)
          ·
            refine ⟨13012969945721694558888251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675313297147796372592167 13012969945721694558888251)
            ·
              refine ⟨19519454918582541838332377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13012969945721694558888251 19519454918582541838332377)
              ·
                refine ⟨14639591188936906378749283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19519454918582541838332377 14639591188936906378749283)
                ·
                  refine ⟨21959386783405359568123925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14639591188936906378749283 21959386783405359568123925)
                  ·
                    refine ⟨1029346255472126229755809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21959386783405359568123925 1029346255472126229755809)
                    ·
                      rfl

theorem cell23_6013934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_6013934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013934 prefixEnd_6013934 := by exact prefixLift 6013934
  have htrace : WordTrace (prefixWord ++ tailWord_6013934) baseStart_6013934 baseEnd_6013934 := by
    simpa [prefixWord, tailWord_6013934, baseEnd_6013934] using wordTrace_append hprefix tailTrace_6013934
  have hstable : (prefixWord ++ tailWord_6013934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013934).length < 2 ^ (prefixWord ++ tailWord_6013934).sum := by decide
  have hdescent : baseEnd_6013934 < baseStart_6013934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013937 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_6013937 : Nat := 118140960795 + 6013937 * 2 ^ 59
def prefixEnd_6013937 : Nat := 4983230072969 + 3 ^ 40 * 6013937 * 2
def baseEnd_6013937 : Nat := 3088040306858342177529913

theorem tailTrace_6013937 : CollatzResearch.WordTrace tailWord_6013937 prefixEnd_6013937 3088040306858342177529913 := by
  unfold tailWord_6013937
  simp only [CollatzResearch.WordTrace]
  refine ⟨219346302413540822513208065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146230868275693881675472043 219346302413540822513208065)
  ·
    refine ⟨164509726810155616884906049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219346302413540822513208065 164509726810155616884906049)
    ·
      refine ⟨123382295107616712663679537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164509726810155616884906049 123382295107616712663679537)
      ·
        refine ⟨92536721330712534497759653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123382295107616712663679537 92536721330712534497759653)
        ·
          refine ⟨17350635249508600218329935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92536721330712534497759653 17350635249508600218329935)
          ·
            refine ⟨26025952874262900327494903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17350635249508600218329935 26025952874262900327494903)
            ·
              refine ⟨39038929311394350491242355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26025952874262900327494903 39038929311394350491242355)
              ·
                refine ⟨58558393967091525736863533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39038929311394350491242355 58558393967091525736863533)
                ·
                  refine ⟨21959397737659322151323825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58558393967091525736863533 21959397737659322151323825)
                  ·
                    refine ⟨16469548303244491613492869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21959397737659322151323825 16469548303244491613492869)
                    ·
                      refine ⟨3088040306858342177529913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16469548303244491613492869 3088040306858342177529913)
                      ·
                        rfl

theorem cell23_6013937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_6013937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013937 prefixEnd_6013937 := by exact prefixLift 6013937
  have htrace : WordTrace (prefixWord ++ tailWord_6013937) baseStart_6013937 baseEnd_6013937 := by
    simpa [prefixWord, tailWord_6013937, baseEnd_6013937] using wordTrace_append hprefix tailTrace_6013937
  have hstable : (prefixWord ++ tailWord_6013937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013937).length < 2 ^ (prefixWord ++ tailWord_6013937).sum := by decide
  have hdescent : baseEnd_6013937 < baseStart_6013937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013938 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_6013938 : Nat := 118140960795 + 6013938 * 2 ^ 59
def prefixEnd_6013938 : Nat := 4983230072969 + 3 ^ 40 * 6013938 * 2
def baseEnd_6013938 : Nat := 1029346940112998891205803

theorem tailTrace_6013938 : CollatzResearch.WordTrace tailWord_6013938 prefixEnd_6013938 1029346940112998891205803 := by
  unfold tailWord_6013938
  simp only [CollatzResearch.WordTrace]
  refine ⟨54836584721634299920998617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146230892591024799789329645 54836584721634299920998617)
  ·
    refine ⟨41127438541225724940748963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54836584721634299920998617 41127438541225724940748963)
    ·
      refine ⟨61691157811838587411123445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41127438541225724940748963 61691157811838587411123445)
      ·
        refine ⟨5783546044859867569792823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61691157811838587411123445 5783546044859867569792823)
        ·
          refine ⟨8675319067289801354689235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783546044859867569792823 8675319067289801354689235)
          ·
            refine ⟨13012978600934702032033853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675319067289801354689235 13012978600934702032033853)
            ·
              refine ⟨4879866975350513262012695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13012978600934702032033853 4879866975350513262012695)
              ·
                refine ⟨7319800463025769893019043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879866975350513262012695 7319800463025769893019043)
                ·
                  refine ⟨10979700694538654839528565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319800463025769893019043 10979700694538654839528565)
                  ·
                    refine ⟨1029346940112998891205803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10979700694538654839528565 1029346940112998891205803)
                    ·
                      rfl

theorem cell23_6013938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_6013938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013938 prefixEnd_6013938 := by exact prefixLift 6013938
  have htrace : WordTrace (prefixWord ++ tailWord_6013938) baseStart_6013938 baseEnd_6013938 := by
    simpa [prefixWord, tailWord_6013938, baseEnd_6013938] using wordTrace_append hprefix tailTrace_6013938
  have hstable : (prefixWord ++ tailWord_6013938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013938).length < 2 ^ (prefixWord ++ tailWord_6013938).sum := by decide
  have hdescent : baseEnd_6013938 < baseStart_6013938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013957 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_6013957 : Nat := 118140960795 + 6013957 * 2 ^ 59
def prefixEnd_6013957 : Nat := 4983230072969 + 3 ^ 40 * 6013957 * 2
def baseEnd_6013957 : Nat := 3088050576471432099279821

theorem tailTrace_6013957 : CollatzResearch.WordTrace tailWord_6013957 prefixEnd_6013957 3088050576471432099279821 := by
  unfold tailWord_6013957
  simp only [CollatzResearch.WordTrace]
  refine ⟨219347031873468365928936125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146231354582312243952624083 219347031873468365928936125)
  ·
    refine ⟨82255136952550637223351047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219347031873468365928936125 82255136952550637223351047)
    ·
      refine ⟨123382705428825955835026571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82255136952550637223351047 123382705428825955835026571)
      ·
        refine ⟨185074058143238933752539857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123382705428825955835026571 185074058143238933752539857)
        ·
          refine ⟨138805543607429200314404893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185074058143238933752539857 138805543607429200314404893)
          ·
            refine ⟨52052078852785950117901835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138805543607429200314404893 52052078852785950117901835)
            ·
              refine ⟨78078118279178925176852753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52052078852785950117901835 78078118279178925176852753)
              ·
                refine ⟨58558588709384193882639565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78078118279178925176852753 58558588709384193882639565)
                ·
                  refine ⟨21959470766019072705989837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58558588709384193882639565 21959470766019072705989837)
                  ·
                    refine ⟨8234801537257152264746189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21959470766019072705989837 8234801537257152264746189)
                    ·
                      refine ⟨3088050576471432099279821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234801537257152264746189 3088050576471432099279821)
                      ·
                        rfl

theorem cell23_6013957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_6013957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013957 prefixEnd_6013957 := by exact prefixLift 6013957
  have htrace : WordTrace (prefixWord ++ tailWord_6013957) baseStart_6013957 baseEnd_6013957 := by
    simpa [prefixWord, tailWord_6013957, baseEnd_6013957] using wordTrace_append hprefix tailTrace_6013957
  have hstable : (prefixWord ++ tailWord_6013957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013957).length < 2 ^ (prefixWord ++ tailWord_6013957).sum := by decide
  have hdescent : baseEnd_6013957 < baseStart_6013957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6013991 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6013991 : Nat := 118140960795 + 6013991 * 2 ^ 59
def prefixEnd_6013991 : Nat := 4983230072969 + 3 ^ 40 * 6013991 * 2
def baseEnd_6013991 : Nat := 3088068034813684966254665

theorem tailTrace_6013991 : CollatzResearch.WordTrace tailWord_6013991 prefixEnd_6013991 3088068034813684966254665 := by
  unfold tailWord_6013991
  simp only [CollatzResearch.WordTrace]
  refine ⟨219348271955345189735673827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146232181303563459823782551 219348271955345189735673827)
  ·
    refine ⟨329022407933017784603510741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219348271955345189735673827 329022407933017784603510741)
    ·
      refine ⟨7711462685930104326644783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 329022407933017784603510741 7711462685930104326644783)
      ·
        refine ⟨11567194028895156489967175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711462685930104326644783 11567194028895156489967175)
        ·
          refine ⟨17350791043342734734950763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11567194028895156489967175 17350791043342734734950763)
          ·
            refine ⟨26026186565014102102426145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17350791043342734734950763 26026186565014102102426145)
            ·
              refine ⟨19519639923760576576819609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26026186565014102102426145 19519639923760576576819609)
              ·
                refine ⟨14639729942820432432614707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19519639923760576576819609 14639729942820432432614707)
                ·
                  refine ⟨21959594914230648648922061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14639729942820432432614707 21959594914230648648922061)
                  ·
                    refine ⟨8234848092836493243345773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21959594914230648648922061 8234848092836493243345773)
                    ·
                      refine ⟨3088068034813684966254665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234848092836493243345773 3088068034813684966254665)
                      ·
                        rfl

theorem cell23_6013991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6013991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6013991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6013991 prefixEnd_6013991 := by exact prefixLift 6013991
  have htrace : WordTrace (prefixWord ++ tailWord_6013991) baseStart_6013991 baseEnd_6013991 := by
    simpa [prefixWord, tailWord_6013991, baseEnd_6013991] using wordTrace_append hprefix tailTrace_6013991
  have hstable : (prefixWord ++ tailWord_6013991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6013991).length < 2 ^ (prefixWord ++ tailWord_6013991).sum := by decide
  have hdescent : baseEnd_6013991 < baseStart_6013991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6013991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014001 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_6014001 : Nat := 118140960795 + 6014001 * 2 ^ 59
def prefixEnd_6014001 : Nat := 4983230072969 + 3 ^ 40 * 6014001 * 2
def baseEnd_6014001 : Nat := 3088073169620229927129619

theorem tailTrace_6014001 : CollatzResearch.WordTrace tailWord_6014001 prefixEnd_6014001 3088073169620229927129619 := by
  unfold tailWord_6014001
  simp only [CollatzResearch.WordTrace]
  refine ⟨219348636685308961443537857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146232424456872640962358571 219348636685308961443537857)
  ·
    refine ⟨164511477513981721082653393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219348636685308961443537857 164511477513981721082653393)
    ·
      refine ⟨123383608135486290811990045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164511477513981721082653393 123383608135486290811990045)
      ·
        refine ⟨46268853050807359054496267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123383608135486290811990045 46268853050807359054496267)
        ·
          refine ⟨69403279576211038581744401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46268853050807359054496267 69403279576211038581744401)
          ·
            refine ⟨52052459682158278936308301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69403279576211038581744401 52052459682158278936308301)
            ·
              refine ⟨19519672380809354601115613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52052459682158278936308301 19519672380809354601115613)
              ·
                refine ⟨7319877142803507975418355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19519672380809354601115613 7319877142803507975418355)
                ·
                  refine ⟨10979815714205261963127533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319877142803507975418355 10979815714205261963127533)
                  ·
                    refine ⟨4117430892826973236172825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10979815714205261963127533 4117430892826973236172825)
                    ·
                      refine ⟨3088073169620229927129619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117430892826973236172825 3088073169620229927129619)
                      ·
                        rfl

theorem cell23_6014001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_6014001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014001 prefixEnd_6014001 := by exact prefixLift 6014001
  have htrace : WordTrace (prefixWord ++ tailWord_6014001) baseStart_6014001 baseEnd_6014001 := by
    simpa [prefixWord, tailWord_6014001, baseEnd_6014001] using wordTrace_append hprefix tailTrace_6014001
  have hstable : (prefixWord ++ tailWord_6014001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014001).length < 2 ^ (prefixWord ++ tailWord_6014001).sum := by decide
  have hdescent : baseEnd_6014001 < baseStart_6014001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014008 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_6014008 : Nat := 118140960795 + 6014008 * 2 ^ 59
def prefixEnd_6014008 : Nat := 4983230072969 + 3 ^ 40 * 6014008 * 2
def baseEnd_6014008 : Nat := 3088076763984811399742087

theorem tailTrace_6014008 : CollatzResearch.WordTrace tailWord_6014008 prefixEnd_6014008 3088076763984811399742087 := by
  unfold tailWord_6014008
  simp only [CollatzResearch.WordTrace]
  refine ⟨109674445998141800819521339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146232594664189067759361785 109674445998141800819521339)
  ·
    refine ⟨164511668997212701229282009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109674445998141800819521339 164511668997212701229282009)
    ·
      refine ⟨123383751747909525921961507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164511668997212701229282009 123383751747909525921961507)
      ·
        refine ⟨185075627621864288882942261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123383751747909525921961507 185075627621864288882942261)
        ·
          refine ⟨17350840089549777082775837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185075627621864288882942261 17350840089549777082775837)
          ·
            refine ⟨6506565033581166406040939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17350840089549777082775837 6506565033581166406040939)
            ·
              refine ⟨9759847550371749609061409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506565033581166406040939 9759847550371749609061409)
              ·
                refine ⟨7319885662778812206796057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9759847550371749609061409 7319885662778812206796057)
                ·
                  refine ⟨5489914247084109155097043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7319885662778812206796057 5489914247084109155097043)
                  ·
                    refine ⟨8234871370626163732645565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5489914247084109155097043 8234871370626163732645565)
                    ·
                      refine ⟨3088076763984811399742087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8234871370626163732645565 3088076763984811399742087)
                      ·
                        rfl

theorem cell23_6014008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_6014008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014008 prefixEnd_6014008 := by exact prefixLift 6014008
  have htrace : WordTrace (prefixWord ++ tailWord_6014008) baseStart_6014008 baseEnd_6014008 := by
    simpa [prefixWord, tailWord_6014008, baseEnd_6014008] using wordTrace_append hprefix tailTrace_6014008
  have hstable : (prefixWord ++ tailWord_6014008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014008).length < 2 ^ (prefixWord ++ tailWord_6014008).sum := by decide
  have hdescent : baseEnd_6014008 < baseStart_6014008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014037 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 7]
def baseStart_6014037 : Nat := 118140960795 + 6014037 * 2 ^ 59
def prefixEnd_6014037 : Nat := 4983230072969 + 3 ^ 40 * 6014037 * 2
def baseEnd_6014037 : Nat := 343121294991532420697717

theorem tailTrace_6014037 : CollatzResearch.WordTrace tailWord_6014037 prefixEnd_6014037 343121294991532420697717 := by
  unfold tailWord_6014037
  simp only [CollatzResearch.WordTrace]
  refine ⟨219349949713178539591848365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146233299808785693061232243 219349949713178539591848365)
  ·
    refine ⟨82256231142441952346943137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219349949713178539591848365 82256231142441952346943137)
    ·
      refine ⟨61692173356831464260207353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82256231142441952346943137 61692173356831464260207353)
      ·
        refine ⟨46269130017623598195155515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61692173356831464260207353 46269130017623598195155515)
        ·
          refine ⟨69403695026435397292733273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46269130017623598195155515 69403695026435397292733273)
          ·
            refine ⟨52052771269826547969549955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69403695026435397292733273 52052771269826547969549955)
            ·
              refine ⟨78079156904739821954324933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52052771269826547969549955 78079156904739821954324933)
              ·
                refine ⟨14639841919638716616435925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78079156904739821954324933 14639841919638716616435925)
                ·
                  refine ⟨343121294991532420697717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14639841919638716616435925 343121294991532420697717)
                  ·
                    rfl

theorem cell23_6014037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_6014037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014037 prefixEnd_6014037 := by exact prefixLift 6014037
  have htrace : WordTrace (prefixWord ++ tailWord_6014037) baseStart_6014037 baseEnd_6014037 := by
    simpa [prefixWord, tailWord_6014037, baseEnd_6014037] using wordTrace_append hprefix tailTrace_6014037
  have hstable : (prefixWord ++ tailWord_6014037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014037).length < 2 ^ (prefixWord ++ tailWord_6014037).sum := by decide
  have hdescent : baseEnd_6014037 < baseStart_6014037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014071 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 5]
def baseStart_6014071 : Nat := 118140960795 + 6014071 * 2 ^ 59
def prefixEnd_6014071 : Nat := 4983230072969 + 3 ^ 40 * 6014071 * 2
def baseEnd_6014071 : Nat := 343123234807338294806033

theorem tailTrace_6014071 : CollatzResearch.WordTrace tailWord_6014071 prefixEnd_6014071 343123234807338294806033 := by
  unfold tailWord_6014071
  simp only [CollatzResearch.WordTrace]
  refine ⟨219351189795055363398586067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146234126530036908932390711 219351189795055363398586067)
  ·
    refine ⟨329026784692583045097879101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219351189795055363398586067 329026784692583045097879101)
    ·
      refine ⟨123385044259718641911704663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329026784692583045097879101 123385044259718641911704663)
      ·
        refine ⟨185077566389577962867556995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123385044259718641911704663 185077566389577962867556995)
        ·
          refine ⟨277616349584366944301335493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185077566389577962867556995 277616349584366944301335493)
          ·
            refine ⟨52053065547068802056500405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277616349584366944301335493 52053065547068802056500405)
            ·
              refine ⟨4879974895037700192796913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52053065547068802056500405 4879974895037700192796913)
              ·
                refine ⟨3659981171278275144597685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879974895037700192796913 3659981171278275144597685)
                ·
                  refine ⟨343123234807338294806033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3659981171278275144597685 343123234807338294806033)
                  ·
                    rfl

theorem cell23_6014071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 5].length) (baseStart_6014071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014071 prefixEnd_6014071 := by exact prefixLift 6014071
  have htrace : WordTrace (prefixWord ++ tailWord_6014071) baseStart_6014071 baseEnd_6014071 := by
    simpa [prefixWord, tailWord_6014071, baseEnd_6014071] using wordTrace_append hprefix tailTrace_6014071
  have hstable : (prefixWord ++ tailWord_6014071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014071).length < 2 ^ (prefixWord ++ tailWord_6014071).sum := by decide
  have hdescent : baseEnd_6014071 < baseStart_6014071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014124 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_6014124 : Nat := 118140960795 + 6014124 * 2 ^ 59
def prefixEnd_6014124 : Nat := 4983230072969 + 3 ^ 40 * 6014124 * 2
def baseEnd_6014124 : Nat := 3088136327740732945891553

theorem tailTrace_6014124 : CollatzResearch.WordTrace tailWord_6014124 prefixEnd_6014124 3088136327740732945891553 := by
  unfold tailWord_6014124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109676561431931676725132713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146235415242575568966843617 109676561431931676725132713)
  ·
    refine ⟨82257421073948757543849535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109676561431931676725132713 82257421073948757543849535)
    ·
      refine ⟨123386131610923136315774303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82257421073948757543849535 123386131610923136315774303)
      ·
        refine ⟨185079197416384704473661455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123386131610923136315774303 185079197416384704473661455)
        ·
          refine ⟨277618796124577056710492183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185079197416384704473661455 277618796124577056710492183)
          ·
            refine ⟨416428194186865585065738275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277618796124577056710492183 416428194186865585065738275)
            ·
              refine ⟨624642291280298377598607413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416428194186865585065738275 624642291280298377598607413)
              ·
                refine ⟨58560214807527972899869445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624642291280298377598607413 58560214807527972899869445)
                ·
                  refine ⟨10980040276411494918725521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58560214807527972899869445 10980040276411494918725521)
                  ·
                    refine ⟨8235030207308621189044141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10980040276411494918725521 8235030207308621189044141)
                    ·
                      refine ⟨3088136327740732945891553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235030207308621189044141 3088136327740732945891553)
                      ·
                        rfl

theorem cell23_6014124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_6014124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014124 prefixEnd_6014124 := by exact prefixLift 6014124
  have htrace : WordTrace (prefixWord ++ tailWord_6014124) baseStart_6014124 baseEnd_6014124 := by
    simpa [prefixWord, tailWord_6014124, baseEnd_6014124] using wordTrace_append hprefix tailTrace_6014124
  have hstable : (prefixWord ++ tailWord_6014124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014124).length < 2 ^ (prefixWord ++ tailWord_6014124).sum := by decide
  have hdescent : baseEnd_6014124 < baseStart_6014124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014127 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 8]
def baseStart_6014127 : Nat := 118140960795 + 6014127 * 2 ^ 59
def prefixEnd_6014127 : Nat := 4983230072969 + 3 ^ 40 * 6014127 * 2
def baseEnd_6014127 : Nat := 343126429798077381572671

theorem tailTrace_6014127 : CollatzResearch.WordTrace tailWord_6014127 prefixEnd_6014127 343126429798077381572671 := by
  unfold tailWord_6014127
  simp only [CollatzResearch.WordTrace]
  refine ⟨219353232282852484962624635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146235488188568323308416423 219353232282852484962624635)
  ·
    refine ⟨329029848424278727443936953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219353232282852484962624635 329029848424278727443936953)
    ·
      refine ⟨246772386318209045582952715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329029848424278727443936953 246772386318209045582952715)
      ·
        refine ⟨370158579477313568374429073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246772386318209045582952715 370158579477313568374429073)
        ·
          refine ⟨277618934607985176280821805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370158579477313568374429073 277618934607985176280821805)
          ·
            refine ⟨104107100477994441105308177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277618934607985176280821805 104107100477994441105308177)
            ·
              refine ⟨78080325358495830828981133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104107100477994441105308177 78080325358495830828981133)
              ·
                refine ⟨29280122009435936560867925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78080325358495830828981133 29280122009435936560867925)
                ·
                  refine ⟨343126429798077381572671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29280122009435936560867925 343126429798077381572671)
                  ·
                    rfl

theorem cell23_6014127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 8].length) (baseStart_6014127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014127 prefixEnd_6014127 := by exact prefixLift 6014127
  have htrace : WordTrace (prefixWord ++ tailWord_6014127) baseStart_6014127 baseEnd_6014127 := by
    simpa [prefixWord, tailWord_6014127, baseEnd_6014127] using wordTrace_append hprefix tailTrace_6014127
  have hstable : (prefixWord ++ tailWord_6014127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014127).length < 2 ^ (prefixWord ++ tailWord_6014127).sum := by decide
  have hdescent : baseEnd_6014127 < baseStart_6014127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014147 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_6014147 : Nat := 118140960795 + 6014147 * 2 ^ 59
def prefixEnd_6014147 : Nat := 4983230072969 + 3 ^ 40 * 6014147 * 2
def baseEnd_6014147 : Nat := 3088148137795786355903947

theorem tailTrace_6014147 : CollatzResearch.WordTrace tailWord_6014147 prefixEnd_6014147 3088148137795786355903947 := by
  unfold tailWord_6014147
  simp only [CollatzResearch.WordTrace]
  refine ⟨219353961742780028378352695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146235974495186685585568463 219353961742780028378352695)
  ·
    refine ⟨329030942614170042567529043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219353961742780028378352695 329030942614170042567529043)
    ·
      refine ⟨493546413921255063851293565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329030942614170042567529043 493546413921255063851293565)
      ·
        refine ⟨185079905220470648944235087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493546413921255063851293565 185079905220470648944235087)
        ·
          refine ⟨277619857830705973416352631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185079905220470648944235087 277619857830705973416352631)
          ·
            refine ⟨416429786746058960124528947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277619857830705973416352631 416429786746058960124528947)
            ·
              refine ⟨624644680119088440186793421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416429786746058960124528947 624644680119088440186793421)
              ·
                refine ⟨234241755044658165070047533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624644680119088440186793421 234241755044658165070047533)
                ·
                  refine ⟨87840658141746811901267825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234241755044658165070047533 87840658141746811901267825)
                  ·
                    refine ⟨65880493606310108925950869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87840658141746811901267825 65880493606310108925950869)
                    ·
                      refine ⟨3088148137795786355903947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65880493606310108925950869 3088148137795786355903947)
                      ·
                        rfl

theorem cell23_6014147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_6014147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014147 prefixEnd_6014147 := by exact prefixLift 6014147
  have htrace : WordTrace (prefixWord ++ tailWord_6014147) baseStart_6014147 baseEnd_6014147 := by
    simpa [prefixWord, tailWord_6014147, baseEnd_6014147] using wordTrace_append hprefix tailTrace_6014147
  have hstable : (prefixWord ++ tailWord_6014147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014147).length < 2 ^ (prefixWord ++ tailWord_6014147).sum := by decide
  have hdescent : baseEnd_6014147 < baseStart_6014147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014148 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6014148 : Nat := 118140960795 + 6014148 * 2 ^ 59
def prefixEnd_6014148 : Nat := 4983230072969 + 3 ^ 40 * 6014148 * 2
def baseEnd_6014148 : Nat := 1029382883758813617330481

theorem tailTrace_6014148 : CollatzResearch.WordTrace tailWord_6014148 prefixEnd_6014148 1029382883758813617330481 := by
  unfold tailWord_6014148
  simp only [CollatzResearch.WordTrace]
  refine ⟨109676999107888202774569549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146235998810517603699426065 109676999107888202774569549)
  ·
    refine ⟨41128874665458076040463581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109676999107888202774569549 41128874665458076040463581)
    ·
      refine ⟨15423327999546778515173843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41128874665458076040463581 15423327999546778515173843)
      ·
        refine ⟨23134991999320167772760765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15423327999546778515173843 23134991999320167772760765)
        ·
          refine ⟨8675621999745062914785287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23134991999320167772760765 8675621999745062914785287)
          ·
            refine ⟨13013432999617594372177931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675621999745062914785287 13013432999617594372177931)
            ·
              refine ⟨19520149499426391558266897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13013432999617594372177931 19520149499426391558266897)
              ·
                refine ⟨14640112124569793668700173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19520149499426391558266897 14640112124569793668700173)
                ·
                  refine ⟨5490042046713672625762565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14640112124569793668700173 5490042046713672625762565)
                  ·
                    refine ⟨1029382883758813617330481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5490042046713672625762565 1029382883758813617330481)
                    ·
                      rfl

theorem cell23_6014148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6014148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014148 prefixEnd_6014148 := by exact prefixLift 6014148
  have htrace : WordTrace (prefixWord ++ tailWord_6014148) baseStart_6014148 baseEnd_6014148 := by
    simpa [prefixWord, tailWord_6014148, baseEnd_6014148] using wordTrace_append hprefix tailTrace_6014148
  have hstable : (prefixWord ++ tailWord_6014148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014148).length < 2 ^ (prefixWord ++ tailWord_6014148).sum := by decide
  have hdescent : baseEnd_6014148 < baseStart_6014148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014165 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_6014165 : Nat := 118140960795 + 6014165 * 2 ^ 59
def prefixEnd_6014165 : Nat := 4983230072969 + 3 ^ 40 * 6014165 * 2
def baseEnd_6014165 : Nat := 1029385793482522428492955

theorem tailTrace_6014165 : CollatzResearch.WordTrace tailWord_6014165 prefixEnd_6014165 1029385793482522428492955 := by
  unfold tailWord_6014165
  simp only [CollatzResearch.WordTrace]
  refine ⟨219354618256714817452507949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146236412171143211635005299 219354618256714817452507949)
  ·
    refine ⟨82257981846268056544690481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219354618256714817452507949 82257981846268056544690481)
    ·
      refine ⟨61693486384701042408517861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82257981846268056544690481 61693486384701042408517861)
      ·
        refine ⟨11567528697131445451597099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61693486384701042408517861 11567528697131445451597099)
        ·
          refine ⟨17351293045697168177395649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11567528697131445451597099 17351293045697168177395649)
          ·
            refine ⟨13013469784272876133046737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17351293045697168177395649 13013469784272876133046737)
            ·
              refine ⟨9760102338204657099785053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13013469784272876133046737 9760102338204657099785053)
              ·
                refine ⟨3660038376826746412419395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9760102338204657099785053 3660038376826746412419395)
                ·
                  refine ⟨5490057565240119618629093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660038376826746412419395 5490057565240119618629093)
                  ·
                    refine ⟨1029385793482522428492955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5490057565240119618629093 1029385793482522428492955)
                    ·
                      rfl

theorem cell23_6014165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_6014165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014165 prefixEnd_6014165 := by exact prefixLift 6014165
  have htrace : WordTrace (prefixWord ++ tailWord_6014165) baseStart_6014165 baseEnd_6014165 := by
    simpa [prefixWord, tailWord_6014165, baseEnd_6014165] using wordTrace_append hprefix tailTrace_6014165
  have hstable : (prefixWord ++ tailWord_6014165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014165).length < 2 ^ (prefixWord ++ tailWord_6014165).sum := by decide
  have hdescent : baseEnd_6014165 < baseStart_6014165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014188 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_6014188 : Nat := 118140960795 + 6014188 * 2 ^ 59
def prefixEnd_6014188 : Nat := 4983230072969 + 3 ^ 40 * 6014188 * 2
def baseEnd_6014188 : Nat := 3088169190502620695491259

theorem tailTrace_6014188 : CollatzResearch.WordTrace tailWord_6014188 prefixEnd_6014188 3088169190502620695491259 := by
  unfold tailWord_6014188
  simp only [CollatzResearch.WordTrace]
  refine ⟨109677728567815746190297609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146236971423754328253730145 109677728567815746190297609)
  ·
    refine ⟨82258296425861809642723207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109677728567815746190297609 82258296425861809642723207)
    ·
      refine ⟨123387444638792714464084811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82258296425861809642723207 123387444638792714464084811)
      ·
        refine ⟨185081166958189071696127217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123387444638792714464084811 185081166958189071696127217)
        ·
          refine ⟨138810875218641803772095413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185081166958189071696127217 138810875218641803772095413)
          ·
            refine ⟨13013519551747669103633945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138810875218641803772095413 13013519551747669103633945)
            ·
              refine ⟨9760139663810751827725459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13013519551747669103633945 9760139663810751827725459)
              ·
                refine ⟨14640209495716127741588189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9760139663810751827725459 14640209495716127741588189)
                ·
                  refine ⟨5490078560893547903095571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14640209495716127741588189 5490078560893547903095571)
                  ·
                    refine ⟨8235117841340321854643357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490078560893547903095571 8235117841340321854643357)
                    ·
                      refine ⟨3088169190502620695491259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235117841340321854643357 3088169190502620695491259)
                      ·
                        rfl

theorem cell23_6014188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_6014188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014188 prefixEnd_6014188 := by exact prefixLift 6014188
  have htrace : WordTrace (prefixWord ++ tailWord_6014188) baseStart_6014188 baseEnd_6014188 := by
    simpa [prefixWord, tailWord_6014188, baseEnd_6014188] using wordTrace_append hprefix tailTrace_6014188
  have hstable : (prefixWord ++ tailWord_6014188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014188).length < 2 ^ (prefixWord ++ tailWord_6014188).sum := by decide
  have hdescent : baseEnd_6014188 < baseStart_6014188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014211 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 4]
def baseStart_6014211 : Nat := 118140960795 + 6014211 * 2 ^ 59
def prefixEnd_6014211 : Nat := 4983230072969 + 3 ^ 40 * 6014211 * 2
def baseEnd_6014211 : Nat := 3088181000557674105503653

theorem tailTrace_6014211 : CollatzResearch.WordTrace tailWord_6014211 prefixEnd_6014211 3088181000557674105503653 := by
  unfold tailWord_6014211
  simp only [CollatzResearch.WordTrace]
  refine ⟨219356296014548167308682487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146237530676365444872454991 219356296014548167308682487)
  ·
    refine ⟨329034444021822250963023731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219356296014548167308682487 329034444021822250963023731)
    ·
      refine ⟨493551666032733376444535597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329034444021822250963023731 493551666032733376444535597)
      ·
        refine ⟨185081874762275016166700849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493551666032733376444535597 185081874762275016166700849)
        ·
          refine ⟨138811406071706262125025637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185081874762275016166700849 138811406071706262125025637)
          ·
            refine ⟨26027138638444924148442307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138811406071706262125025637 26027138638444924148442307)
            ·
              refine ⟨39040707957667386222663461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26027138638444924148442307 39040707957667386222663461)
              ·
                refine ⟨7320132742062634916749399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39040707957667386222663461 7320132742062634916749399)
                ·
                  refine ⟨10980199113093952375124099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7320132742062634916749399 10980199113093952375124099)
                  ·
                    refine ⟨16470298669640928562686149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10980199113093952375124099 16470298669640928562686149)
                    ·
                      refine ⟨3088181000557674105503653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16470298669640928562686149 3088181000557674105503653)
                      ·
                        rfl

theorem cell23_6014211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_6014211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014211 prefixEnd_6014211 := by exact prefixLift 6014211
  have htrace : WordTrace (prefixWord ++ tailWord_6014211) baseStart_6014211 baseEnd_6014211 := by
    simpa [prefixWord, tailWord_6014211, baseEnd_6014211] using wordTrace_append hprefix tailTrace_6014211
  have hstable : (prefixWord ++ tailWord_6014211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014211).length < 2 ^ (prefixWord ++ tailWord_6014211).sum := by decide
  have hdescent : baseEnd_6014211 < baseStart_6014211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014222 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_6014222 : Nat := 118140960795 + 6014222 * 2 ^ 59
def prefixEnd_6014222 : Nat := 4983230072969 + 3 ^ 40 * 6014222 * 2
def baseEnd_6014222 : Nat := 3088186648844873562466103

theorem tailTrace_6014222 : CollatzResearch.WordTrace tailWord_6014222 prefixEnd_6014222 3088186648844873562466103 := by
  unfold tailWord_6014222
  simp only [CollatzResearch.WordTrace]
  refine ⟨27419587152188539523416615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146237798145005544124888613 27419587152188539523416615)
  ·
    refine ⟨41129380728282809285124923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27419587152188539523416615 41129380728282809285124923)
    ·
      refine ⟨61694071092424213927687385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41129380728282809285124923 61694071092424213927687385)
      ·
        refine ⟨46270553319318160445765539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61694071092424213927687385 46270553319318160445765539)
        ·
          refine ⟨69405829978977240668648309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46270553319318160445765539 69405829978977240668648309)
          ·
            refine ⟨6506796560529116312685779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69405829978977240668648309 6506796560529116312685779)
            ·
              refine ⟨9760194840793674469028669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506796560529116312685779 9760194840793674469028669)
              ·
                refine ⟨3660073065297627925885751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9760194840793674469028669 3660073065297627925885751)
                ·
                  refine ⟨5490109597946441888828627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660073065297627925885751 5490109597946441888828627)
                  ·
                    refine ⟨8235164396919662833242941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490109597946441888828627 8235164396919662833242941)
                    ·
                      refine ⟨3088186648844873562466103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235164396919662833242941 3088186648844873562466103)
                      ·
                        rfl

theorem cell23_6014222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_6014222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014222 prefixEnd_6014222 := by exact prefixLift 6014222
  have htrace : WordTrace (prefixWord ++ tailWord_6014222) baseStart_6014222 baseEnd_6014222 := by
    simpa [prefixWord, tailWord_6014222, baseEnd_6014222] using wordTrace_append hprefix tailTrace_6014222
  have hstable : (prefixWord ++ tailWord_6014222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014222).length < 2 ^ (prefixWord ++ tailWord_6014222).sum := by decide
  have hdescent : baseEnd_6014222 < baseStart_6014222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014231 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6014231 : Nat := 118140960795 + 6014231 * 2 ^ 59
def prefixEnd_6014231 : Nat := 4983230072969 + 3 ^ 40 * 6014231 * 2
def baseEnd_6014231 : Nat := 3088191270170764027253561

theorem tailTrace_6014231 : CollatzResearch.WordTrace tailWord_6014231 prefixEnd_6014231 3088191270170764027253561 := by
  unfold tailWord_6014231
  simp only [CollatzResearch.WordTrace]
  refine ⟨219357025474475710724410547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146238016982983807149607031 219357025474475710724410547)
  ·
    refine ⟨329035538211713566086615821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219357025474475710724410547 329035538211713566086615821)
    ·
      refine ⟨123388326829392587282480933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329035538211713566086615821 123388326829392587282480933)
      ·
        refine ⟨23135311280511110115465175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123388326829392587282480933 23135311280511110115465175)
        ·
          refine ⟨34702966920766665173197763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23135311280511110115465175 34702966920766665173197763)
          ·
            refine ⟨52054450381149997759796645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34702966920766665173197763 52054450381149997759796645)
            ·
              refine ⟨9760209446465624579961871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52054450381149997759796645 9760209446465624579961871)
              ·
                refine ⟨14640314169698436869942807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9760209446465624579961871 14640314169698436869942807)
                ·
                  refine ⟨21960471254547655304914211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14640314169698436869942807 21960471254547655304914211)
                  ·
                    refine ⟨32940706881821482957371317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21960471254547655304914211 32940706881821482957371317)
                    ·
                      refine ⟨3088191270170764027253561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32940706881821482957371317 3088191270170764027253561)
                      ·
                        rfl

theorem cell23_6014231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6014231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014231 prefixEnd_6014231 := by exact prefixLift 6014231
  have htrace : WordTrace (prefixWord ++ tailWord_6014231) baseStart_6014231 baseEnd_6014231 := by
    simpa [prefixWord, tailWord_6014231, baseEnd_6014231] using wordTrace_append hprefix tailTrace_6014231
  have hstable : (prefixWord ++ tailWord_6014231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014231).length < 2 ^ (prefixWord ++ tailWord_6014231).sum := by decide
  have hdescent : baseEnd_6014231 < baseStart_6014231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014234 : List Nat := [3, 1, 1, 3, 3, 1, 11]
def baseStart_6014234 : Nat := 118140960795 + 6014234 * 2 ^ 59
def prefixEnd_6014234 : Nat := 4983230072969 + 3 ^ 40 * 6014234 * 2
def baseEnd_6014234 : Nat := 38125837168058364389087

theorem tailTrace_6014234 : CollatzResearch.WordTrace tailWord_6014234 prefixEnd_6014234 38125837168058364389087 := by
  unfold tailWord_6014234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54839283723366210559192439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146238089928976561491179837 54839283723366210559192439)
  ·
    refine ⟨82258925585049315838788659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54839283723366210559192439 82258925585049315838788659)
    ·
      refine ⟨123388388377573973758182989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82258925585049315838788659 123388388377573973758182989)
      ·
        refine ⟨46270645641590240159318621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123388388377573973758182989 46270645641590240159318621)
        ·
          refine ⟨17351492115596340059744483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46270645641590240159318621 17351492115596340059744483)
          ·
            refine ⟨26027238173394510089616725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17351492115596340059744483 26027238173394510089616725)
            ·
              refine ⟨38125837168058364389087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26027238173394510089616725 38125837168058364389087)
              ·
                rfl

theorem cell23_6014234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 11].length) (baseStart_6014234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014234 prefixEnd_6014234 := by exact prefixLift 6014234
  have htrace : WordTrace (prefixWord ++ tailWord_6014234) baseStart_6014234 baseEnd_6014234 := by
    simpa [prefixWord, tailWord_6014234, baseEnd_6014234] using wordTrace_append hprefix tailTrace_6014234
  have hstable : (prefixWord ++ tailWord_6014234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014234).length < 2 ^ (prefixWord ++ tailWord_6014234).sum := by decide
  have hdescent : baseEnd_6014234 < baseStart_6014234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014245 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_6014245 : Nat := 118140960795 + 6014245 * 2 ^ 59
def prefixEnd_6014245 : Nat := 4983230072969 + 3 ^ 40 * 6014245 * 2
def baseEnd_6014245 : Nat := 3088198458899926972478497

theorem tailTrace_6014245 : CollatzResearch.WordTrace tailWord_6014245 prefixEnd_6014245 3088198458899926972478497 := by
  unfold tailWord_6014245
  simp only [CollatzResearch.WordTrace]
  refine ⟨219357536096424991115420189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146238357397616660743613459 219357536096424991115420189)
  ·
    refine ⟨82259076036159371668282571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219357536096424991115420189 82259076036159371668282571)
    ·
      refine ⟨123388614054239057502423857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82259076036159371668282571 123388614054239057502423857)
      ·
        refine ⟨92541460540679293126817893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123388614054239057502423857 92541460540679293126817893)
        ·
          refine ⟨17351523851377367461278355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92541460540679293126817893 17351523851377367461278355)
          ·
            refine ⟨26027285777066051191917533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17351523851377367461278355 26027285777066051191917533)
            ·
              refine ⟨9760232166399769196969075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26027285777066051191917533 9760232166399769196969075)
              ·
                refine ⟨14640348249599653795453613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9760232166399769196969075 14640348249599653795453613)
                ·
                  refine ⟨5490130593599870173295105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14640348249599653795453613 5490130593599870173295105)
                  ·
                    refine ⟨4117597945199902629971329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5490130593599870173295105 4117597945199902629971329)
                    ·
                      refine ⟨3088198458899926972478497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117597945199902629971329 3088198458899926972478497)
                      ·
                        rfl

theorem cell23_6014245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_6014245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014245 prefixEnd_6014245 := by exact prefixLift 6014245
  have htrace : WordTrace (prefixWord ++ tailWord_6014245) baseStart_6014245 baseEnd_6014245 := by
    simpa [prefixWord, tailWord_6014245, baseEnd_6014245] using wordTrace_append hprefix tailTrace_6014245
  have hstable : (prefixWord ++ tailWord_6014245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014245).length < 2 ^ (prefixWord ++ tailWord_6014245).sum := by decide
  have hdescent : baseEnd_6014245 < baseStart_6014245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014295 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_6014295 : Nat := 118140960795 + 6014295 * 2 ^ 59
def prefixEnd_6014295 : Nat := 4983230072969 + 3 ^ 40 * 6014295 * 2
def baseEnd_6014295 : Nat := 3088224132932651776853267

theorem tailTrace_6014295 : CollatzResearch.WordTrace tailWord_6014295 prefixEnd_6014295 3088224132932651776853267 := by
  unfold tailWord_6014295
  simp only [CollatzResearch.WordTrace]
  refine ⟨219359359746243849654740339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146239573164162566436493559 219359359746243849654740339)
  ·
    refine ⟨329039039619365774482110509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219359359746243849654740339 329039039619365774482110509)
    ·
      refine ⟨123389639857262165430791441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329039039619365774482110509 123389639857262165430791441)
      ·
        refine ⟨92542229892946624073093581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123389639857262165430791441 92542229892946624073093581)
        ·
          refine ⟨34703336209854984027410093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92542229892946624073093581 34703336209854984027410093)
          ·
            refine ⟨13013751078695619010278785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34703336209854984027410093 13013751078695619010278785)
            ·
              refine ⟨9760313309021714257709089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13013751078695619010278785 9760313309021714257709089)
              ·
                refine ⟨7320234981766285693281817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760313309021714257709089 7320234981766285693281817)
                ·
                  refine ⟨5490176236324714269961363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7320234981766285693281817 5490176236324714269961363)
                  ·
                    refine ⟨8235264354487071404942045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490176236324714269961363 8235264354487071404942045)
                    ·
                      refine ⟨3088224132932651776853267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235264354487071404942045 3088224132932651776853267)
                      ·
                        rfl

theorem cell23_6014295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_6014295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014295 prefixEnd_6014295 := by exact prefixLift 6014295
  have htrace : WordTrace (prefixWord ++ tailWord_6014295) baseStart_6014295 baseEnd_6014295 := by
    simpa [prefixWord, tailWord_6014295, baseEnd_6014295] using wordTrace_append hprefix tailTrace_6014295
  have hstable : (prefixWord ++ tailWord_6014295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014295).length < 2 ^ (prefixWord ++ tailWord_6014295).sum := by decide
  have hdescent : baseEnd_6014295 < baseStart_6014295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014391 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_6014391 : Nat := 118140960795 + 6014391 * 2 ^ 59
def prefixEnd_6014391 : Nat := 4983230072969 + 3 ^ 40 * 6014391 * 2
def baseEnd_6014391 : Nat := 3088273427075483401252825

theorem tailTrace_6014391 : CollatzResearch.WordTrace tailWord_6014391 prefixEnd_6014391 3088273427075483401252825 := by
  unfold tailWord_6014391
  simp only [CollatzResearch.WordTrace]
  refine ⟨219362861153896058050235027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146241907435930705366823351 219362861153896058050235027)
  ·
    refine ⟨329044291730844087075352541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219362861153896058050235027 329044291730844087075352541)
    ·
      refine ⟨123391609399066532653257203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329044291730844087075352541 123391609399066532653257203)
      ·
        refine ⟨185087414098599798979885805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123391609399066532653257203 185087414098599798979885805)
        ·
          refine ⟨69407780286974924617457177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185087414098599798979885805 69407780286974924617457177)
          ·
            refine ⟨52055835215231193463092883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69407780286974924617457177 52055835215231193463092883)
            ·
              refine ⟨78083752822846790194639325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52055835215231193463092883 78083752822846790194639325)
              ·
                refine ⟨29281407308567546322989747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78083752822846790194639325 29281407308567546322989747)
                ·
                  refine ⟨43922110962851319484484621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29281407308567546322989747 43922110962851319484484621)
                  ·
                    refine ⟨16470791611069244806681733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43922110962851319484484621 16470791611069244806681733)
                    ·
                      refine ⟨3088273427075483401252825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16470791611069244806681733 3088273427075483401252825)
                      ·
                        rfl

theorem cell23_6014391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_6014391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014391 prefixEnd_6014391 := by exact prefixLift 6014391
  have htrace : WordTrace (prefixWord ++ tailWord_6014391) baseStart_6014391 baseEnd_6014391 := by
    simpa [prefixWord, tailWord_6014391, baseEnd_6014391] using wordTrace_append hprefix tailTrace_6014391
  have hstable : (prefixWord ++ tailWord_6014391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014391).length < 2 ^ (prefixWord ++ tailWord_6014391).sum := by decide
  have hdescent : baseEnd_6014391 < baseStart_6014391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014408 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_6014408 : Nat := 118140960795 + 6014408 * 2 ^ 59
def prefixEnd_6014408 : Nat := 4983230072969 + 3 ^ 40 * 6014408 * 2
def baseEnd_6014408 : Nat := 3088282156246609834740247

theorem tailTrace_6014408 : CollatzResearch.WordTrace tailWord_6014408 prefixEnd_6014408 3088282156246609834740247 := by
  unfold tailWord_6014408
  simp only [CollatzResearch.WordTrace]
  refine ⟨109681740597417234976801939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146242320796556313302402585 109681740597417234976801939)
  ·
    refine ⟨164522610896125852465202909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109681740597417234976801939 164522610896125852465202909)
    ·
      refine ⟨61695979086047194674451091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164522610896125852465202909 61695979086047194674451091)
      ·
        refine ⟨92543968629070792011676637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61695979086047194674451091 92543968629070792011676637)
        ·
          refine ⟨34703988235901547004378739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92543968629070792011676637 34703988235901547004378739)
          ·
            refine ⟨52055982353852320506568109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34703988235901547004378739 52055982353852320506568109)
            ·
              refine ⟨19520993382694620189963041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52055982353852320506568109 19520993382694620189963041)
              ·
                refine ⟨14640745037020965142472281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19520993382694620189963041 14640745037020965142472281)
                ·
                  refine ⟨10980558777765723856854211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14640745037020965142472281 10980558777765723856854211)
                  ·
                    refine ⟨16470838166648585785281317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10980558777765723856854211 16470838166648585785281317)
                    ·
                      refine ⟨3088282156246609834740247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16470838166648585785281317 3088282156246609834740247)
                      ·
                        rfl

theorem cell23_6014408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_6014408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014408 prefixEnd_6014408 := by exact prefixLift 6014408
  have htrace : WordTrace (prefixWord ++ tailWord_6014408) baseStart_6014408 baseEnd_6014408 := by
    simpa [prefixWord, tailWord_6014408, baseEnd_6014408] using wordTrace_append hprefix tailTrace_6014408
  have hstable : (prefixWord ++ tailWord_6014408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014408).length < 2 ^ (prefixWord ++ tailWord_6014408).sum := by decide
  have hdescent : baseEnd_6014408 < baseStart_6014408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014465 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 6]
def baseStart_6014465 : Nat := 118140960795 + 6014465 * 2 ^ 59
def prefixEnd_6014465 : Nat := 4983230072969 + 3 ^ 40 * 6014465 * 2
def baseEnd_6014465 : Nat := 343145713849324012414165

theorem tailTrace_6014465 : CollatzResearch.WordTrace tailWord_6014465 prefixEnd_6014465 343145713849324012414165 := by
  unfold tailWord_6014465
  simp only [CollatzResearch.WordTrace]
  refine ⟨219365560155627968688428849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146243706770418645792285899 219365560155627968688428849)
  ·
    refine ⟨164524170116720976516321637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219365560155627968688428849 164524170116720976516321637)
    ·
      refine ⟨30848281896885183096810307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164524170116720976516321637 30848281896885183096810307)
      ·
        refine ⟨46272422845327774645215461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30848281896885183096810307 46272422845327774645215461)
        ·
          refine ⟨8676079283498957745977899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46272422845327774645215461 8676079283498957745977899)
          ·
            refine ⟨13014118925248436618966849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676079283498957745977899 13014118925248436618966849)
            ·
              refine ⟨9760589193936327464225137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13014118925248436618966849 9760589193936327464225137)
              ·
                refine ⟨7320441895452245598168853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760589193936327464225137 7320441895452245598168853)
                ·
                  refine ⟨343145713849324012414165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7320441895452245598168853 343145713849324012414165)
                  ·
                    rfl

theorem cell23_6014465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_6014465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014465 prefixEnd_6014465 := by exact prefixLift 6014465
  have htrace : WordTrace (prefixWord ++ tailWord_6014465) baseStart_6014465 baseEnd_6014465 := by
    simpa [prefixWord, tailWord_6014465, baseEnd_6014465] using wordTrace_append hprefix tailTrace_6014465
  have hstable : (prefixWord ++ tailWord_6014465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014465).length < 2 ^ (prefixWord ++ tailWord_6014465).sum := by decide
  have hdescent : baseEnd_6014465 < baseStart_6014465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014515 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 4]
def baseStart_6014515 : Nat := 118140960795 + 6014515 * 2 ^ 59
def prefixEnd_6014515 : Nat := 4983230072969 + 3 ^ 40 * 6014515 * 2
def baseEnd_6014515 : Nat := 3088337098676640916102255

theorem tailTrace_6014515 : CollatzResearch.WordTrace tailWord_6014515 prefixEnd_6014515 3088337098676640916102255 := by
  unfold tailWord_6014515
  simp only [CollatzResearch.WordTrace]
  refine ⟨219367383805446827227748999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146244922536964551485165999 219367383805446827227748999)
  ·
    refine ⟨329051075708170240841623499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219367383805446827227748999 329051075708170240841623499)
    ·
      refine ⟨493576613562255361262435249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329051075708170240841623499 493576613562255361262435249)
      ·
        refine ⟨370182460171691520946826437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493576613562255361262435249 370182460171691520946826437)
        ·
          refine ⟨69409211282192160177529957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370182460171691520946826437 69409211282192160177529957)
          ·
            refine ⟨13014227115411030033286867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69409211282192160177529957 13014227115411030033286867)
            ·
              refine ⟨19521340673116545049930301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13014227115411030033286867 19521340673116545049930301)
              ·
                refine ⟨7320502752418704393723863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19521340673116545049930301 7320502752418704393723863)
                ·
                  refine ⟨10980754128628056590585795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7320502752418704393723863 10980754128628056590585795)
                  ·
                    refine ⟨16471131192942084885878693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10980754128628056590585795 16471131192942084885878693)
                    ·
                      refine ⟨3088337098676640916102255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16471131192942084885878693 3088337098676640916102255)
                      ·
                        rfl

theorem cell23_6014515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_6014515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014515 prefixEnd_6014515 := by exact prefixLift 6014515
  have htrace : WordTrace (prefixWord ++ tailWord_6014515) baseStart_6014515 baseEnd_6014515 := by
    simpa [prefixWord, tailWord_6014515, baseEnd_6014515] using wordTrace_append hprefix tailTrace_6014515
  have hstable : (prefixWord ++ tailWord_6014515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014515).length < 2 ^ (prefixWord ++ tailWord_6014515).sum := by decide
  have hdescent : baseEnd_6014515 < baseStart_6014515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014531 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_6014531 : Nat := 118140960795 + 6014531 * 2 ^ 59
def prefixEnd_6014531 : Nat := 4983230072969 + 3 ^ 40 * 6014531 * 2
def baseEnd_6014531 : Nat := 3088345314367112853502181

theorem tailTrace_6014531 : CollatzResearch.WordTrace tailWord_6014531 prefixEnd_6014531 3088345314367112853502181 := by
  unfold tailWord_6014531
  simp only [CollatzResearch.WordTrace]
  refine ⟨219367967373388861960331447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146245311582259241306887631 219367967373388861960331447)
  ·
    refine ⟨329051951060083292940497171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219367967373388861960331447 329051951060083292940497171)
    ·
      refine ⟨493577926590124939410745757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329051951060083292940497171 493577926590124939410745757)
      ·
        refine ⟨185091722471296852279029659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493577926590124939410745757 185091722471296852279029659)
        ·
          refine ⟨277637583706945278418544489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185091722471296852279029659 277637583706945278418544489)
          ·
            refine ⟨208228187780208958813908367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277637583706945278418544489 208228187780208958813908367)
            ·
              refine ⟨312342281670313438220862551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208228187780208958813908367 312342281670313438220862551)
              ·
                refine ⟨468513422505470157331293827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312342281670313438220862551 468513422505470157331293827)
                ·
                  refine ⟨702770133758205235996940741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468513422505470157331293827 702770133758205235996940741)
                  ·
                    refine ⟨131769400079663481749426389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702770133758205235996940741 131769400079663481749426389)
                    ·
                      refine ⟨3088345314367112853502181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131769400079663481749426389 3088345314367112853502181)
                      ·
                        rfl

theorem cell23_6014531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_6014531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014531 prefixEnd_6014531 := by exact prefixLift 6014531
  have htrace : WordTrace (prefixWord ++ tailWord_6014531) baseStart_6014531 baseEnd_6014531 := by
    simpa [prefixWord, tailWord_6014531, baseEnd_6014531] using wordTrace_append hprefix tailTrace_6014531
  have hstable : (prefixWord ++ tailWord_6014531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014531).length < 2 ^ (prefixWord ++ tailWord_6014531).sum := by decide
  have hdescent : baseEnd_6014531 < baseStart_6014531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014535 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_6014535 : Nat := 118140960795 + 6014535 * 2 ^ 59
def prefixEnd_6014535 : Nat := 4983230072969 + 3 ^ 40 * 6014535 * 2
def baseEnd_6014535 : Nat := 3088347368289730837852163

theorem tailTrace_6014535 : CollatzResearch.WordTrace tailWord_6014535 prefixEnd_6014535 3088347368289730837852163 := by
  unfold tailWord_6014535
  simp only [CollatzResearch.WordTrace]
  refine ⟨219368113265374370643477059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146245408843582913762318039 219368113265374370643477059)
  ·
    refine ⟨329052169898061555965215589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219368113265374370643477059 329052169898061555965215589)
    ·
      refine ⟨61697281855886541743477923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329052169898061555965215589 61697281855886541743477923)
      ·
        refine ⟨92545922783829812615216885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61697281855886541743477923 92545922783829812615216885)
        ·
          refine ⟨8676180260984044932676583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92545922783829812615216885 8676180260984044932676583)
          ·
            refine ⟨13014270391476067399014875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676180260984044932676583 13014270391476067399014875)
            ·
              refine ⟨19521405587214101098522313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13014270391476067399014875 19521405587214101098522313)
              ·
                refine ⟨14641054190410575823891735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19521405587214101098522313 14641054190410575823891735)
                ·
                  refine ⟨21961581285615863735837603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14641054190410575823891735 21961581285615863735837603)
                  ·
                    refine ⟨32942371928423795603756405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21961581285615863735837603 32942371928423795603756405)
                    ·
                      refine ⟨3088347368289730837852163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32942371928423795603756405 3088347368289730837852163)
                      ·
                        rfl

theorem cell23_6014535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_6014535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014535 prefixEnd_6014535 := by exact prefixLift 6014535
  have htrace : WordTrace (prefixWord ++ tailWord_6014535) baseStart_6014535 baseEnd_6014535 := by
    simpa [prefixWord, tailWord_6014535, baseEnd_6014535] using wordTrace_append hprefix tailTrace_6014535
  have hstable : (prefixWord ++ tailWord_6014535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014535).length < 2 ^ (prefixWord ++ tailWord_6014535).sum := by decide
  have hdescent : baseEnd_6014535 < baseStart_6014535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014575 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 5, 3, 2]
def baseStart_6014575 : Nat := 118140960795 + 6014575 * 2 ^ 59
def prefixEnd_6014575 : Nat := 4983230072969 + 3 ^ 40 * 6014575 * 2
def baseEnd_6014575 : Nat := 3088367907515910681351979

theorem tailTrace_6014575 : CollatzResearch.WordTrace tailWord_6014575 prefixEnd_6014575 3088367907515910681351979 := by
  unfold tailWord_6014575
  simp only [CollatzResearch.WordTrace]
  refine ⟨219369572185229457474933179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146246381456819638316622119 219369572185229457474933179)
  ·
    refine ⟨329054358277844186212399769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219369572185229457474933179 329054358277844186212399769)
    ·
      refine ⟨246790768708383139659299827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329054358277844186212399769 246790768708383139659299827)
      ·
        refine ⟨370186153062574709488949741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246790768708383139659299827 370186153062574709488949741)
        ·
          refine ⟨138819807398465516058356153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370186153062574709488949741 138819807398465516058356153)
          ·
            refine ⟨104114855548849137043767115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138819807398465516058356153 104114855548849137043767115)
            ·
              refine ⟨156172283323273705565650673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104114855548849137043767115 156172283323273705565650673)
              ·
                refine ⟨117129212492455279174238005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156172283323273705565650673 117129212492455279174238005)
                ·
                  refine ⟨10980863671167682422584813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117129212492455279174238005 10980863671167682422584813)
                  ·
                    refine ⟨4117823876687880908469305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10980863671167682422584813 4117823876687880908469305)
                    ·
                      refine ⟨3088367907515910681351979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117823876687880908469305 3088367907515910681351979)
                      ·
                        rfl

theorem cell23_6014575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3, 2].length) (baseStart_6014575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014575 prefixEnd_6014575 := by exact prefixLift 6014575
  have htrace : WordTrace (prefixWord ++ tailWord_6014575) baseStart_6014575 baseEnd_6014575 := by
    simpa [prefixWord, tailWord_6014575, baseEnd_6014575] using wordTrace_append hprefix tailTrace_6014575
  have hstable : (prefixWord ++ tailWord_6014575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014575).length < 2 ^ (prefixWord ++ tailWord_6014575).sum := by decide
  have hdescent : baseEnd_6014575 < baseStart_6014575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014588 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_6014588 : Nat := 118140960795 + 6014588 * 2 ^ 59
def prefixEnd_6014588 : Nat := 4983230072969 + 3 ^ 40 * 6014588 * 2
def baseEnd_6014588 : Nat := 3088374582764419130489419

theorem tailTrace_6014588 : CollatzResearch.WordTrace tailWord_6014588 prefixEnd_6014588 3088374582764419130489419 := by
  unfold tailWord_6014588
  simp only [CollatzResearch.WordTrace]
  refine ⟨109685023167091180347578209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146246697556121573796770945 109685023167091180347578209)
  ·
    refine ⟨82263767375318385260683657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109685023167091180347578209 82263767375318385260683657)
    ·
      refine ⟨61697825531488788945512743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82263767375318385260683657 61697825531488788945512743)
      ·
        refine ⟨92546738297233183418269115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61697825531488788945512743 92546738297233183418269115)
        ·
          refine ⟨138820107445849775127403673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92546738297233183418269115 138820107445849775127403673)
          ·
            refine ⟨104115080584387331345552755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138820107445849775127403673 104115080584387331345552755)
            ·
              refine ⟨156172620876580997018329133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104115080584387331345552755 156172620876580997018329133)
              ·
                refine ⟨58564732828717873881873425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156172620876580997018329133 58564732828717873881873425)
                ·
                  refine ⟨43923549621538405411405069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58564732828717873881873425 43923549621538405411405069)
                  ·
                    refine ⟨16471331108076902029276901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43923549621538405411405069 16471331108076902029276901)
                    ·
                      refine ⟨3088374582764419130489419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16471331108076902029276901 3088374582764419130489419)
                      ·
                        rfl

theorem cell23_6014588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_6014588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014588 prefixEnd_6014588 := by exact prefixLift 6014588
  have htrace : WordTrace (prefixWord ++ tailWord_6014588) baseStart_6014588 baseEnd_6014588 := by
    simpa [prefixWord, tailWord_6014588, baseEnd_6014588] using wordTrace_append hprefix tailTrace_6014588
  have hstable : (prefixWord ++ tailWord_6014588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014588).length < 2 ^ (prefixWord ++ tailWord_6014588).sum := by decide
  have hdescent : baseEnd_6014588 < baseStart_6014588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014599 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_6014599 : Nat := 118140960795 + 6014599 * 2 ^ 59
def prefixEnd_6014599 : Nat := 4983230072969 + 3 ^ 40 * 6014599 * 2
def baseEnd_6014599 : Nat := 3088380231051618587451869

theorem tailTrace_6014599 : CollatzResearch.WordTrace tailWord_6014599 prefixEnd_6014599 3088380231051618587451869 := by
  unfold tailWord_6014599
  simp only [CollatzResearch.WordTrace]
  refine ⟨219370447537142509573806851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146246965024761673049204567 219370447537142509573806851)
  ·
    refine ⟨329055671305713764360710277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219370447537142509573806851 329055671305713764360710277)
    ·
      refine ⟨61697938369821330817633177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329055671305713764360710277 61697938369821330817633177)
      ·
        refine ⟨46273453777365998113224883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61697938369821330817633177 46273453777365998113224883)
        ·
          refine ⟨69410180666048997169837325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46273453777365998113224883 69410180666048997169837325)
          ·
            refine ⟨26028817749768373938688997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69410180666048997169837325 26028817749768373938688997)
            ·
              refine ⟨4880403328081570113504187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26028817749768373938688997 4880403328081570113504187)
              ·
                refine ⟨7320604992122355170256281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880403328081570113504187 7320604992122355170256281)
                ·
                  refine ⟨5490453744091766377692211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7320604992122355170256281 5490453744091766377692211)
                  ·
                    refine ⟨8235680616137649566538317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490453744091766377692211 8235680616137649566538317)
                    ·
                      refine ⟨3088380231051618587451869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235680616137649566538317 3088380231051618587451869)
                      ·
                        rfl

theorem cell23_6014599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_6014599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014599 prefixEnd_6014599 := by exact prefixLift 6014599
  have htrace : WordTrace (prefixWord ++ tailWord_6014599) baseStart_6014599 baseEnd_6014599 := by
    simpa [prefixWord, tailWord_6014599, baseEnd_6014599] using wordTrace_append hprefix tailTrace_6014599
  have hstable : (prefixWord ++ tailWord_6014599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014599).length < 2 ^ (prefixWord ++ tailWord_6014599).sum := by decide
  have hdescent : baseEnd_6014599 < baseStart_6014599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014625 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6014625 : Nat := 118140960795 + 6014625 * 2 ^ 59
def prefixEnd_6014625 : Nat := 4983230072969 + 3 ^ 40 * 6014625 * 2
def baseEnd_6014625 : Nat := 3088393581548635485726749

theorem tailTrace_6014625 : CollatzResearch.WordTrace tailWord_6014625 prefixEnd_6014625 3088393581548635485726749 := by
  unfold tailWord_6014625
  simp only [CollatzResearch.WordTrace]
  refine ⟨219371395835048316014253329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146247597223365544009502219 219371395835048316014253329)
  ·
    refine ⟨164528546876286237010689997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219371395835048316014253329 164528546876286237010689997)
    ·
      refine ⟨61698205078607338879008749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164528546876286237010689997 61698205078607338879008749)
      ·
        refine ⟨23136826904477752079628281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61698205078607338879008749 23136826904477752079628281)
        ·
          refine ⟨17352620178358314059721211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23136826904477752079628281 17352620178358314059721211)
          ·
            refine ⟨26028930267537471089581817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17352620178358314059721211 26028930267537471089581817)
            ·
              refine ⟨19521697700653103317186363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26028930267537471089581817 19521697700653103317186363)
              ·
                refine ⟨29282546550979654975779545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19521697700653103317186363 29282546550979654975779545)
                ·
                  refine ⟨21961909913234741231834659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29282546550979654975779545 21961909913234741231834659)
                  ·
                    refine ⟨32942864869852111847751989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21961909913234741231834659 32942864869852111847751989)
                    ·
                      refine ⟨3088393581548635485726749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32942864869852111847751989 3088393581548635485726749)
                      ·
                        rfl

theorem cell23_6014625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6014625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014625 prefixEnd_6014625 := by exact prefixLift 6014625
  have htrace : WordTrace (prefixWord ++ tailWord_6014625) baseStart_6014625 baseEnd_6014625 := by
    simpa [prefixWord, tailWord_6014625, baseEnd_6014625] using wordTrace_append hprefix tailTrace_6014625
  have hstable : (prefixWord ++ tailWord_6014625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014625).length < 2 ^ (prefixWord ++ tailWord_6014625).sum := by decide
  have hdescent : baseEnd_6014625 < baseStart_6014625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014639 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 2, 2, 2]
def baseStart_6014639 : Nat := 118140960795 + 6014639 * 2 ^ 59
def prefixEnd_6014639 : Nat := 4983230072969 + 3 ^ 40 * 6014639 * 2
def baseEnd_6014639 : Nat := 3088400770277798430951685

theorem tailTrace_6014639 : CollatzResearch.WordTrace tailWord_6014639 prefixEnd_6014639 3088400770277798430951685 := by
  unfold tailWord_6014639
  simp only [CollatzResearch.WordTrace]
  refine ⟨219371906456997596405262971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146247937637998397603508647 219371906456997596405262971)
  ·
    refine ⟨329057859685496394607894457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219371906456997596405262971 329057859685496394607894457)
    ·
      refine ⟨246793394764122295955920843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329057859685496394607894457 246793394764122295955920843)
      ·
        refine ⟨370190092146183443933881265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246793394764122295955920843 370190092146183443933881265)
        ·
          refine ⟨277642569109637582950410949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370190092146183443933881265 277642569109637582950410949)
          ·
            refine ⟨52057981708057046803202053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277642569109637582950410949 52057981708057046803202053)
            ·
              refine ⟨9760871570260696275600385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52057981708057046803202053 9760871570260696275600385)
              ·
                refine ⟨7320653677695522206700289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760871570260696275600385 7320653677695522206700289)
                ·
                  refine ⟨5490490258271641655025217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7320653677695522206700289 5490490258271641655025217)
                  ·
                    refine ⟨4117867693703731241268913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5490490258271641655025217 4117867693703731241268913)
                    ·
                      refine ⟨3088400770277798430951685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117867693703731241268913 3088400770277798430951685)
                      ·
                        rfl

theorem cell23_6014639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2, 2].length) (baseStart_6014639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014639 prefixEnd_6014639 := by exact prefixLift 6014639
  have htrace : WordTrace (prefixWord ++ tailWord_6014639) baseStart_6014639 baseEnd_6014639 := by
    simpa [prefixWord, tailWord_6014639, baseEnd_6014639] using wordTrace_append hprefix tailTrace_6014639
  have hstable : (prefixWord ++ tailWord_6014639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014639).length < 2 ^ (prefixWord ++ tailWord_6014639).sum := by decide
  have hdescent : baseEnd_6014639 < baseStart_6014639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014655 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_6014655 : Nat := 118140960795 + 6014655 * 2 ^ 59
def prefixEnd_6014655 : Nat := 4983230072969 + 3 ^ 40 * 6014655 * 2
def baseEnd_6014655 : Nat := 3088408985968270368351611

theorem tailTrace_6014655 : CollatzResearch.WordTrace tailWord_6014655 prefixEnd_6014655 3088408985968270368351611 := by
  unfold tailWord_6014655
  simp only [CollatzResearch.WordTrace]
  refine ⟨219372490024939631137845419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146248326683293087425230279 219372490024939631137845419)
  ·
    refine ⟨329058735037409446706768129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219372490024939631137845419 329058735037409446706768129)
    ·
      refine ⟨246794051278057085030076097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329058735037409446706768129 246794051278057085030076097)
      ·
        refine ⟨185095538458542813772557073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246794051278057085030076097 185095538458542813772557073)
        ·
          refine ⟨138821653843907110329417805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185095538458542813772557073 138821653843907110329417805)
          ·
            refine ⟨52058120191465166373531677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138821653843907110329417805 52058120191465166373531677)
            ·
              refine ⟨19521795071799437390074379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52058120191465166373531677 19521795071799437390074379)
              ·
                refine ⟨29282692607699156085111569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19521795071799437390074379 29282692607699156085111569)
                ·
                  refine ⟨21962019455774367063833677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29282692607699156085111569 21962019455774367063833677)
                  ·
                    refine ⟨8235757295915387648937629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21962019455774367063833677 8235757295915387648937629)
                    ·
                      refine ⟨3088408985968270368351611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235757295915387648937629 3088408985968270368351611)
                      ·
                        rfl

theorem cell23_6014655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_6014655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014655 prefixEnd_6014655 := by exact prefixLift 6014655
  have htrace : WordTrace (prefixWord ++ tailWord_6014655) baseStart_6014655 baseEnd_6014655 := by
    simpa [prefixWord, tailWord_6014655, baseEnd_6014655] using wordTrace_append hprefix tailTrace_6014655
  have hstable : (prefixWord ++ tailWord_6014655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014655).length < 2 ^ (prefixWord ++ tailWord_6014655).sum := by decide
  have hdescent : baseEnd_6014655 < baseStart_6014655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014715 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3]
def baseStart_6014715 : Nat := 118140960795 + 6014715 * 2 ^ 59
def prefixEnd_6014715 : Nat := 4983230072969 + 3 ^ 40 * 6014715 * 2
def baseEnd_6014715 : Nat := 3088439794807540133601335

theorem tailTrace_6014715 : CollatzResearch.WordTrace tailWord_6014715 prefixEnd_6014715 3088439794807540133601335 := by
  unfold tailWord_6014715
  simp only [CollatzResearch.WordTrace]
  refine ⟨219374678404722261385029599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146249785603148174256686399 219374678404722261385029599)
  ·
    refine ⟨329062017607083392077544399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219374678404722261385029599 329062017607083392077544399)
    ·
      refine ⟨493593026410625088116316599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329062017607083392077544399 493593026410625088116316599)
      ·
        refine ⟨740389539615937632174474899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493593026410625088116316599 740389539615937632174474899)
        ·
          refine ⟨1110584309423906448261712349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740389539615937632174474899 1110584309423906448261712349)
          ·
            refine ⟨416469116033964918098142131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1110584309423906448261712349 416469116033964918098142131)
            ·
              refine ⟨624703674050947377147213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416469116033964918098142131 624703674050947377147213197)
              ·
                refine ⟨234263877769105266430204949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624703674050947377147213197 234263877769105266430204949)
                ·
                  refine ⟨10981119270426809363915857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 234263877769105266430204949 10981119270426809363915857)
                  ·
                    refine ⟨8235839452820107022936893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10981119270426809363915857 8235839452820107022936893)
                    ·
                      refine ⟨3088439794807540133601335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8235839452820107022936893 3088439794807540133601335)
                      ·
                        rfl

theorem cell23_6014715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3].length) (baseStart_6014715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014715 prefixEnd_6014715 := by exact prefixLift 6014715
  have htrace : WordTrace (prefixWord ++ tailWord_6014715) baseStart_6014715 baseEnd_6014715 := by
    simpa [prefixWord, tailWord_6014715, baseEnd_6014715] using wordTrace_append hprefix tailTrace_6014715
  have hstable : (prefixWord ++ tailWord_6014715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014715).length < 2 ^ (prefixWord ++ tailWord_6014715).sum := by decide
  have hdescent : baseEnd_6014715 < baseStart_6014715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014769 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 6]
def baseStart_6014769 : Nat := 118140960795 + 6014769 * 2 ^ 59
def prefixEnd_6014769 : Nat := 4983230072969 + 3 ^ 40 * 6014769 * 2
def baseEnd_6014769 : Nat := 343163058084764769147343

theorem tailTrace_6014769 : CollatzResearch.WordTrace tailWord_6014769 prefixEnd_6014769 343163058084764769147343 := by
  unfold tailWord_6014769
  simp only [CollatzResearch.WordTrace]
  refine ⟨219376647946526628607495361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146251098631017752404996907 219376647946526628607495361)
  ·
    refine ⟨164532485959894971455621521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219376647946526628607495361 164532485959894971455621521)
    ·
      refine ⟨123399364469921228591716141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164532485959894971455621521 123399364469921228591716141)
      ·
        refine ⟨46274761676220460721893553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123399364469921228591716141 46274761676220460721893553)
        ·
          refine ⟨34706071257165345541420165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46274761676220460721893553 34706071257165345541420165)
          ·
            refine ⟨6507388360718502289016281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34706071257165345541420165 6507388360718502289016281)
            ·
              refine ⟨4880541270538876716762211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6507388360718502289016281 4880541270538876716762211)
              ·
                refine ⟨7320811905808315075143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880541270538876716762211 7320811905808315075143317)
                ·
                  refine ⟨343163058084764769147343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7320811905808315075143317 343163058084764769147343)
                  ·
                    rfl

theorem cell23_6014769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 6].length) (baseStart_6014769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014769 prefixEnd_6014769 := by exact prefixLift 6014769
  have htrace : WordTrace (prefixWord ++ tailWord_6014769) baseStart_6014769 baseEnd_6014769 := by
    simpa [prefixWord, tailWord_6014769, baseEnd_6014769] using wordTrace_append hprefix tailTrace_6014769
  have hstable : (prefixWord ++ tailWord_6014769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014769).length < 2 ^ (prefixWord ++ tailWord_6014769).sum := by decide
  have hdescent : baseEnd_6014769 < baseStart_6014769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014789 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_6014789 : Nat := 118140960795 + 6014789 * 2 ^ 59
def prefixEnd_6014789 : Nat := 4983230072969 + 3 ^ 40 * 6014789 * 2
def baseEnd_6014789 : Nat := 3088477792375972844075995

theorem tailTrace_6014789 : CollatzResearch.WordTrace tailWord_6014789 prefixEnd_6014789 3088477792375972844075995 := by
  unfold tailWord_6014789
  simp only [CollatzResearch.WordTrace]
  refine ⟨219377377406454172023223421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146251584937636114682148947 219377377406454172023223421)
  ·
    refine ⟨82266516527420314508708783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219377377406454172023223421 82266516527420314508708783)
    ·
      refine ⟨123399774791130471763063175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82266516527420314508708783 123399774791130471763063175)
      ·
        refine ⟨185099662186695707644594763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123399774791130471763063175 185099662186695707644594763)
        ·
          refine ⟨277649493280043561466892145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185099662186695707644594763 277649493280043561466892145)
          ·
            refine ⟨208237119960032671100169109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277649493280043561466892145 208237119960032671100169109)
            ·
              refine ⟨9761114998126531457820427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208237119960032671100169109 9761114998126531457820427)
              ·
                refine ⟨14641672497189797186730641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761114998126531457820427 14641672497189797186730641)
                ·
                  refine ⟨10981254372892347890047981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14641672497189797186730641 10981254372892347890047981)
                  ·
                    refine ⟨4117970389834630458767993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10981254372892347890047981 4117970389834630458767993)
                    ·
                      refine ⟨3088477792375972844075995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4117970389834630458767993 3088477792375972844075995)
                      ·
                        rfl

theorem cell23_6014789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_6014789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014789 prefixEnd_6014789 := by exact prefixLift 6014789
  have htrace : WordTrace (prefixWord ++ tailWord_6014789) baseStart_6014789 baseEnd_6014789 := by
    simpa [prefixWord, tailWord_6014789, baseEnd_6014789] using wordTrace_append hprefix tailTrace_6014789
  have hstable : (prefixWord ++ tailWord_6014789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014789).length < 2 ^ (prefixWord ++ tailWord_6014789).sum := by decide
  have hdescent : baseEnd_6014789 < baseStart_6014789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014829 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6014829 : Nat := 118140960795 + 6014829 * 2 ^ 59
def prefixEnd_6014829 : Nat := 4983230072969 + 3 ^ 40 * 6014829 * 2
def baseEnd_6014829 : Nat := 1029499443867384229191937

theorem tailTrace_6014829 : CollatzResearch.WordTrace tailWord_6014829 prefixEnd_6014829 1029499443867384229191937 := by
  unfold tailWord_6014829
  simp only [CollatzResearch.WordTrace]
  refine ⟨219378836326309258854679541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146252557550872839236453027 219378836326309258854679541)
  ·
    refine ⟨20566765905591493017626207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219378836326309258854679541 20566765905591493017626207)
    ·
      refine ⟨30850148858387239526439311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20566765905591493017626207 30850148858387239526439311)
      ·
        refine ⟨46275223287580859289658967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30850148858387239526439311 46275223287580859289658967)
        ·
          refine ⟨69412834931371288934488451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46275223287580859289658967 69412834931371288934488451)
          ·
            refine ⟨104119252397056933401732677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69412834931371288934488451 104119252397056933401732677)
            ·
              refine ⟨19522359824448175012824877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104119252397056933401732677 19522359824448175012824877)
              ·
                refine ⟨7320884934168065629809329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19522359824448175012824877 7320884934168065629809329)
                ·
                  refine ⟨5490663700626049222356997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7320884934168065629809329 5490663700626049222356997)
                  ·
                    refine ⟨1029499443867384229191937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5490663700626049222356997 1029499443867384229191937)
                    ·
                      rfl

theorem cell23_6014829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6014829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014829 prefixEnd_6014829 := by exact prefixLift 6014829
  have htrace : WordTrace (prefixWord ++ tailWord_6014829) baseStart_6014829 baseEnd_6014829 := by
    simpa [prefixWord, tailWord_6014829, baseEnd_6014829] using wordTrace_append hprefix tailTrace_6014829
  have hstable : (prefixWord ++ tailWord_6014829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014829).length < 2 ^ (prefixWord ++ tailWord_6014829).sum := by decide
  have hdescent : baseEnd_6014829 < baseStart_6014829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014853 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 1, 2, 2]
def baseStart_6014853 : Nat := 118140960795 + 6014853 * 2 ^ 59
def prefixEnd_6014853 : Nat := 4983230072969 + 3 ^ 40 * 6014853 * 2
def baseEnd_6014853 : Nat := 3088510655137860593675701

theorem tailTrace_6014853 : CollatzResearch.WordTrace tailWord_6014853 prefixEnd_6014853 3088510655137860593675701 := by
  unfold tailWord_6014853
  simp only [CollatzResearch.WordTrace]
  refine ⟨219379711678222310953553213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146253141118814873969035475 219379711678222310953553213)
  ·
    refine ⟨82267391879333366607582455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219379711678222310953553213 82267391879333366607582455)
    ·
      refine ⟨123401087819000049911373683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82267391879333366607582455 123401087819000049911373683)
      ·
        refine ⟨185101631728500074867060525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123401087819000049911373683 185101631728500074867060525)
        ·
          refine ⟨69413111898187528075147697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185101631728500074867060525 69413111898187528075147697)
          ·
            refine ⟨52059833923640646056360773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69413111898187528075147697 52059833923640646056360773)
            ·
              refine ⟨9761218860682621135567645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52059833923640646056360773 9761218860682621135567645)
              ·
                refine ⟨3660457072755982925837867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9761218860682621135567645 3660457072755982925837867)
                ·
                  refine ⟨5490685609133974388756801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660457072755982925837867 5490685609133974388756801)
                  ·
                    refine ⟨4118014206850480791567601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5490685609133974388756801 4118014206850480791567601)
                    ·
                      refine ⟨3088510655137860593675701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118014206850480791567601 3088510655137860593675701)
                      ·
                        rfl

theorem cell23_6014853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_6014853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014853 prefixEnd_6014853 := by exact prefixLift 6014853
  have htrace : WordTrace (prefixWord ++ tailWord_6014853) baseStart_6014853 baseEnd_6014853 := by
    simpa [prefixWord, tailWord_6014853, baseEnd_6014853] using wordTrace_append hprefix tailTrace_6014853
  have hstable : (prefixWord ++ tailWord_6014853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014853).length < 2 ^ (prefixWord ++ tailWord_6014853).sum := by decide
  have hdescent : baseEnd_6014853 < baseStart_6014853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014856 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_6014856 : Nat := 118140960795 + 6014856 * 2 ^ 59
def prefixEnd_6014856 : Nat := 4983230072969 + 3 ^ 40 * 6014856 * 2
def baseEnd_6014856 : Nat := 3088512195579824081938187

theorem tailTrace_6014856 : CollatzResearch.WordTrace tailWord_6014856 prefixEnd_6014856 3088512195579824081938187 := by
  unfold tailWord_6014856
  simp only [CollatzResearch.WordTrace]
  refine ⟨109689910548605721232956211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146253214064807628310608281 109689910548605721232956211)
  ·
    refine ⟨164534865822908581849434317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109689910548605721232956211 164534865822908581849434317)
    ·
      refine ⟨61700574683590718193537869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164534865822908581849434317 61700574683590718193537869)
      ·
        refine ⟨23137715506346519322576701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61700574683590718193537869 23137715506346519322576701)
        ·
          refine ⟨8676643314879944745966263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23137715506346519322576701 8676643314879944745966263)
          ·
            refine ⟨13014964972319917118949395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676643314879944745966263 13014964972319917118949395)
            ·
              refine ⟨19522447458479875678424093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13014964972319917118949395 19522447458479875678424093)
              ·
                refine ⟨7320917796929953379409035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19522447458479875678424093 7320917796929953379409035)
                ·
                  refine ⟨10981376695394930069113553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7320917796929953379409035 10981376695394930069113553)
                  ·
                    refine ⟨8236032521546197551835165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10981376695394930069113553 8236032521546197551835165)
                    ·
                      refine ⟨3088512195579824081938187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236032521546197551835165 3088512195579824081938187)
                      ·
                        rfl

theorem cell23_6014856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_6014856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014856 prefixEnd_6014856 := by exact prefixLift 6014856
  have htrace : WordTrace (prefixWord ++ tailWord_6014856) baseStart_6014856 baseEnd_6014856 := by
    simpa [prefixWord, tailWord_6014856, baseEnd_6014856] using wordTrace_append hprefix tailTrace_6014856
  have hstable : (prefixWord ++ tailWord_6014856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014856).length < 2 ^ (prefixWord ++ tailWord_6014856).sum := by decide
  have hdescent : baseEnd_6014856 < baseStart_6014856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014869 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_6014869 : Nat := 118140960795 + 6014869 * 2 ^ 59
def prefixEnd_6014869 : Nat := 4983230072969 + 3 ^ 40 * 6014869 * 2
def baseEnd_6014869 : Nat := 3088518870828332531075627

theorem tailTrace_6014869 : CollatzResearch.WordTrace tailWord_6014869 prefixEnd_6014869 3088518870828332531075627 := by
  unfold tailWord_6014869
  simp only [CollatzResearch.WordTrace]
  refine ⟨219380295246164345686135661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146253530164109563790757107 219380295246164345686135661)
  ·
    refine ⟨82267610717311629632300873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219380295246164345686135661 82267610717311629632300873)
    ·
      refine ⟨61700708037983722224225655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82267610717311629632300873 61700708037983722224225655)
      ·
        refine ⟨92551062056975583336338483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61700708037983722224225655 92551062056975583336338483)
        ·
          refine ⟨138826593085463375004507725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92551062056975583336338483 138826593085463375004507725)
          ·
            refine ⟨52059972407048765626690397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138826593085463375004507725 52059972407048765626690397)
            ·
              refine ⟨19522489652643287110008899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52059972407048765626690397 19522489652643287110008899)
              ·
                refine ⟨29283734478964930665013349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19522489652643287110008899 29283734478964930665013349)
                ·
                  refine ⟨5490700214805924499690003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29283734478964930665013349 5490700214805924499690003)
                  ·
                    refine ⟨8236050322208886749535005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490700214805924499690003 8236050322208886749535005)
                    ·
                      refine ⟨3088518870828332531075627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236050322208886749535005 3088518870828332531075627)
                      ·
                        rfl

theorem cell23_6014869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_6014869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014869 prefixEnd_6014869 := by exact prefixLift 6014869
  have htrace : WordTrace (prefixWord ++ tailWord_6014869) baseStart_6014869 baseEnd_6014869 := by
    simpa [prefixWord, tailWord_6014869, baseEnd_6014869] using wordTrace_append hprefix tailTrace_6014869
  have hstable : (prefixWord ++ tailWord_6014869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014869).length < 2 ^ (prefixWord ++ tailWord_6014869).sum := by decide
  have hdescent : baseEnd_6014869 < baseStart_6014869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014912 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_6014912 : Nat := 118140960795 + 6014912 * 2 ^ 59
def prefixEnd_6014912 : Nat := 4983230072969 + 3 ^ 40 * 6014912 * 2
def baseEnd_6014912 : Nat := 3088540950496475862837929

theorem tailTrace_6014912 : CollatzResearch.WordTrace tailWord_6014912 prefixEnd_6014912 3088540950496475862837929 := by
  unfold tailWord_6014912
  simp only [CollatzResearch.WordTrace]
  refine ⟨109690931792504282014975495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146254575723339042686633993 109690931792504282014975495)
  ·
    refine ⟨164536397688756423022463243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109690931792504282014975495 164536397688756423022463243)
    ·
      refine ⟨246804596533134634533694865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164536397688756423022463243 246804596533134634533694865)
      ·
        refine ⟨185103447399850975900271149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246804596533134634533694865 185103447399850975900271149)
        ·
          refine ⟨69413792774944115962601681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185103447399850975900271149 69413792774944115962601681)
          ·
            refine ⟨52060344581208086971951261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69413792774944115962601681 52060344581208086971951261)
            ·
              refine ⟨19522629217953032614481723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52060344581208086971951261 19522629217953032614481723)
              ·
                refine ⟨29283943826929548921722585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19522629217953032614481723 29283943826929548921722585)
                ·
                  refine ⟨21962957870197161691291939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29283943826929548921722585 21962957870197161691291939)
                  ·
                    refine ⟨32944436805295742536937909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21962957870197161691291939 32944436805295742536937909)
                    ·
                      refine ⟨3088540950496475862837929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32944436805295742536937909 3088540950496475862837929)
                      ·
                        rfl

theorem cell23_6014912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_6014912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014912 prefixEnd_6014912 := by exact prefixLift 6014912
  have htrace : WordTrace (prefixWord ++ tailWord_6014912) baseStart_6014912 baseEnd_6014912 := by
    simpa [prefixWord, tailWord_6014912, baseEnd_6014912] using wordTrace_append hprefix tailTrace_6014912
  have hstable : (prefixWord ++ tailWord_6014912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014912).length < 2 ^ (prefixWord ++ tailWord_6014912).sum := by decide
  have hdescent : baseEnd_6014912 < baseStart_6014912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014922 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6014922 : Nat := 118140960795 + 6014922 * 2 ^ 59
def prefixEnd_6014922 : Nat := 4983230072969 + 3 ^ 40 * 6014922 * 2
def baseEnd_6014922 : Nat := 3088546085303020823712883

theorem tailTrace_6014922 : CollatzResearch.WordTrace tailWord_6014922 prefixEnd_6014922 3088546085303020823712883 := by
  unfold tailWord_6014922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54845557078743083934453755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146254818876648223825210013 54845557078743083934453755)
  ·
    refine ⟨82268335618114625901680633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54845557078743083934453755 82268335618114625901680633)
    ·
      refine ⟨61701251713585969426260475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82268335618114625901680633 61701251713585969426260475)
      ·
        refine ⟨92551877570378954139390713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61701251713585969426260475 92551877570378954139390713)
        ·
          refine ⟨69413908177784215604543035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92551877570378954139390713 69413908177784215604543035)
          ·
            refine ⟨104120862266676323406814553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69413908177784215604543035 104120862266676323406814553)
            ·
              refine ⟨78090646700007242555110915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104120862266676323406814553 78090646700007242555110915)
              ·
                refine ⟨117135970050010863832666373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78090646700007242555110915 117135970050010863832666373)
                ·
                  refine ⟨21962994384377036968624945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117135970050010863832666373 21962994384377036968624945)
                  ·
                    refine ⟨16472245788282777726468709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21962994384377036968624945 16472245788282777726468709)
                    ·
                      refine ⟨3088546085303020823712883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16472245788282777726468709 3088546085303020823712883)
                      ·
                        rfl

theorem cell23_6014922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6014922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014922 prefixEnd_6014922 := by exact prefixLift 6014922
  have htrace : WordTrace (prefixWord ++ tailWord_6014922) baseStart_6014922 baseEnd_6014922 := by
    simpa [prefixWord, tailWord_6014922, baseEnd_6014922] using wordTrace_append hprefix tailTrace_6014922
  have hstable : (prefixWord ++ tailWord_6014922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014922).length < 2 ^ (prefixWord ++ tailWord_6014922).sum := by decide
  have hdescent : baseEnd_6014922 < baseStart_6014922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014926 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_6014926 : Nat := 118140960795 + 6014926 * 2 ^ 59
def prefixEnd_6014926 : Nat := 4983230072969 + 3 ^ 40 * 6014926 * 2
def baseEnd_6014926 : Nat := 3088548139225638808062865

theorem tailTrace_6014926 : CollatzResearch.WordTrace tailWord_6014926 prefixEnd_6014926 3088548139225638808062865 := by
  unfold tailWord_6014926
  simp only [CollatzResearch.WordTrace]
  refine ⟨27422796775869730552620079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146254916137971896280640421 27422796775869730552620079)
  ·
    refine ⟨41134195163804595828930119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27422796775869730552620079 41134195163804595828930119)
    ·
      refine ⟨61701292745706893743395179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41134195163804595828930119 61701292745706893743395179)
      ·
        refine ⟨92551939118560340615092769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61701292745706893743395179 92551939118560340615092769)
        ·
          refine ⟨69413954338920255461319577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92551939118560340615092769 69413954338920255461319577)
          ·
            refine ⟨52060465754190191595989683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69413954338920255461319577 52060465754190191595989683)
            ·
              refine ⟨78090698631285287393984525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52060465754190191595989683 78090698631285287393984525)
              ·
                refine ⟨29284011986731982772744197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78090698631285287393984525 29284011986731982772744197)
                ·
                  refine ⟨5490752247512246769889537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29284011986731982772744197 5490752247512246769889537)
                  ·
                    refine ⟨4118064185634185077417153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5490752247512246769889537 4118064185634185077417153)
                    ·
                      refine ⟨3088548139225638808062865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118064185634185077417153 3088548139225638808062865)
                      ·
                        rfl

theorem cell23_6014926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_6014926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014926 prefixEnd_6014926 := by exact prefixLift 6014926
  have htrace : WordTrace (prefixWord ++ tailWord_6014926) baseStart_6014926 baseEnd_6014926 := by
    simpa [prefixWord, tailWord_6014926, baseEnd_6014926] using wordTrace_append hprefix tailTrace_6014926
  have hstable : (prefixWord ++ tailWord_6014926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014926).length < 2 ^ (prefixWord ++ tailWord_6014926).sum := by decide
  have hdescent : baseEnd_6014926 < baseStart_6014926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014943 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 2, 2, 2]
def baseStart_6014943 : Nat := 118140960795 + 6014943 * 2 ^ 59
def prefixEnd_6014943 : Nat := 4983230072969 + 3 ^ 40 * 6014943 * 2
def baseEnd_6014943 : Nat := 3088556868396765241550287

theorem tailTrace_6014943 : CollatzResearch.WordTrace tailWord_6014943 prefixEnd_6014943 3088556868396765241550287 := by
  unfold tailWord_6014943
  simp only [CollatzResearch.WordTrace]
  refine ⟨219382994247896256324329483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146255329498597504216219655 219382994247896256324329483)
  ·
    refine ⟨329074491371844384486494225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219382994247896256324329483 329074491371844384486494225)
    ·
      refine ⟨246805868528883288364870669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329074491371844384486494225 246805868528883288364870669)
      ·
        refine ⟨92552200698331233136826501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246805868528883288364870669 92552200698331233136826501)
        ·
          refine ⟨17353537630937106213154969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92552200698331233136826501 17353537630937106213154969)
          ·
            refine ⟨13015153223202829659866227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17353537630937106213154969 13015153223202829659866227)
            ·
              refine ⟨19522729834804244489799341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015153223202829659866227 19522729834804244489799341)
              ·
                refine ⟨7321023688051591683674753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19522729834804244489799341 7321023688051591683674753)
                ·
                  refine ⟨5490767766038693762756065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321023688051591683674753 5490767766038693762756065)
                  ·
                    refine ⟨4118075824529020322067049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5490767766038693762756065 4118075824529020322067049)
                    ·
                      refine ⟨3088556868396765241550287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118075824529020322067049 3088556868396765241550287)
                      ·
                        rfl

theorem cell23_6014943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_6014943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014943 prefixEnd_6014943 := by exact prefixLift 6014943
  have htrace : WordTrace (prefixWord ++ tailWord_6014943) baseStart_6014943 baseEnd_6014943 := by
    simpa [prefixWord, tailWord_6014943, baseEnd_6014943] using wordTrace_append hprefix tailTrace_6014943
  have hstable : (prefixWord ++ tailWord_6014943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014943).length < 2 ^ (prefixWord ++ tailWord_6014943).sum := by decide
  have hdescent : baseEnd_6014943 < baseStart_6014943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014972 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_6014972 : Nat := 118140960795 + 6014972 * 2 ^ 59
def prefixEnd_6014972 : Nat := 4983230072969 + 3 ^ 40 * 6014972 * 2
def baseEnd_6014972 : Nat := 3088571759335745628087653

theorem tailTrace_6014972 : CollatzResearch.WordTrace tailWord_6014972 prefixEnd_6014972 3088571759335745628087653 := by
  unfold tailWord_6014972
  simp only [CollatzResearch.WordTrace]
  refine ⟨109692025982395597138567585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146256034643194129518090113 109692025982395597138567585)
  ·
    refine ⟨82269019486796697853925689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109692025982395597138567585 82269019486796697853925689)
    ·
      refine ⟨61701764615097523390444267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82269019486796697853925689 61701764615097523390444267)
      ·
        refine ⟨92552646922646285085666401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61701764615097523390444267 92552646922646285085666401)
        ·
          refine ⟨69414485191984713814249801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92552646922646285085666401 69414485191984713814249801)
          ·
            refine ⟨52060863893988535360687351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69414485191984713814249801 52060863893988535360687351)
            ·
              refine ⟨78091295840982803041031027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52060863893988535360687351 78091295840982803041031027)
              ·
                refine ⟨117136943761474204561546541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78091295840982803041031027 117136943761474204561546541)
                ·
                  refine ⟨43926353910552826710579953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117136943761474204561546541 43926353910552826710579953)
                  ·
                    refine ⟨32944765432914620032934965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43926353910552826710579953 32944765432914620032934965)
                    ·
                      refine ⟨3088571759335745628087653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32944765432914620032934965 3088571759335745628087653)
                      ·
                        rfl

theorem cell23_6014972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_6014972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014972 prefixEnd_6014972 := by exact prefixLift 6014972
  have htrace : WordTrace (prefixWord ++ tailWord_6014972) baseStart_6014972 baseEnd_6014972 := by
    simpa [prefixWord, tailWord_6014972, baseEnd_6014972] using wordTrace_append hprefix tailTrace_6014972
  have hstable : (prefixWord ++ tailWord_6014972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014972).length < 2 ^ (prefixWord ++ tailWord_6014972).sum := by decide
  have hdescent : baseEnd_6014972 < baseStart_6014972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014983 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 5]
def baseStart_6014983 : Nat := 118140960795 + 6014983 * 2 ^ 59
def prefixEnd_6014983 : Nat := 4983230072969 + 3 ^ 40 * 6014983 * 2
def baseEnd_6014983 : Nat := 343175267513660565005567

theorem tailTrace_6014983 : CollatzResearch.WordTrace tailWord_6014983 prefixEnd_6014983 343175267513660565005567 := by
  unfold tailWord_6014983
  simp only [CollatzResearch.WordTrace]
  refine ⟨219384453167751343155785603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146256302111834228770523735 219384453167751343155785603)
  ·
    refine ⟨329076679751627014733678405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219384453167751343155785603 329076679751627014733678405)
    ·
      refine ⟨61701877453430065262564701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329076679751627014733678405 61701877453430065262564701)
      ·
        refine ⟨23138204045036274473461763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61701877453430065262564701 23138204045036274473461763)
        ·
          refine ⟨34707306067554411710192645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23138204045036274473461763 34707306067554411710192645)
          ·
            refine ⟨6507619887666452195661121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34707306067554411710192645 6507619887666452195661121)
            ·
              refine ⟨4880714915749839146745841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6507619887666452195661121 4880714915749839146745841)
              ·
                refine ⟨3660536186812379360059381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880714915749839146745841 3660536186812379360059381)
                ·
                  refine ⟨343175267513660565005567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3660536186812379360059381 343175267513660565005567)
                  ·
                    rfl

theorem cell23_6014983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 5].length) (baseStart_6014983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6014983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6014983 prefixEnd_6014983 := by exact prefixLift 6014983
  have htrace : WordTrace (prefixWord ++ tailWord_6014983) baseStart_6014983 baseEnd_6014983 := by
    simpa [prefixWord, tailWord_6014983, baseEnd_6014983] using wordTrace_append hprefix tailTrace_6014983
  have hstable : (prefixWord ++ tailWord_6014983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014983).length < 2 ^ (prefixWord ++ tailWord_6014983).sum := by decide
  have hdescent : baseEnd_6014983 < baseStart_6014983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015019 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3]
def baseStart_6015019 : Nat := 118140960795 + 6015019 * 2 ^ 59
def prefixEnd_6015019 : Nat := 4983230072969 + 3 ^ 40 * 6015019 * 2
def baseEnd_6015019 : Nat := 3088595892926506944199937

theorem tailTrace_6015019 : CollatzResearch.WordTrace tailWord_6015019 prefixEnd_6015019 3088595892926506944199937 := by
  unfold tailWord_6015019
  simp only [CollatzResearch.WordTrace]
  refine ⟨219385766195620921304096111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146257177463747280869397407 219385766195620921304096111)
  ·
    refine ⟨329078649293431381956144167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219385766195620921304096111 329078649293431381956144167)
    ·
      refine ⟨493617973940147072934216251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329078649293431381956144167 493617973940147072934216251)
      ·
        refine ⟨740426960910220609401324377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493617973940147072934216251 740426960910220609401324377)
        ·
          refine ⟨555320220682665457050993283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740426960910220609401324377 555320220682665457050993283)
          ·
            refine ⟨832980331023998185576489925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555320220682665457050993283 832980331023998185576489925)
            ·
              refine ⟨156183812066999659795591861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 832980331023998185576489925 156183812066999659795591861)
              ·
                refine ⟨14642232381281218105836737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156183812066999659795591861 14642232381281218105836737)
                ·
                  refine ⟨10981674285960913579377553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14642232381281218105836737 10981674285960913579377553)
                  ·
                    refine ⟨8236255714470685184533165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10981674285960913579377553 8236255714470685184533165)
                    ·
                      refine ⟨3088595892926506944199937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236255714470685184533165 3088595892926506944199937)
                      ·
                        rfl

theorem cell23_6015019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3].length) (baseStart_6015019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015019 prefixEnd_6015019 := by exact prefixLift 6015019
  have htrace : WordTrace (prefixWord ++ tailWord_6015019) baseStart_6015019 baseEnd_6015019 := by
    simpa [prefixWord, tailWord_6015019, baseEnd_6015019] using wordTrace_append hprefix tailTrace_6015019
  have hstable : (prefixWord ++ tailWord_6015019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015019).length < 2 ^ (prefixWord ++ tailWord_6015019).sum := by decide
  have hdescent : baseEnd_6015019 < baseStart_6015019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015039 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 6]
def baseStart_6015039 : Nat := 118140960795 + 6015039 * 2 ^ 59
def prefixEnd_6015039 : Nat := 4983230072969 + 3 ^ 40 * 6015039 * 2
def baseEnd_6015039 : Nat := 343178462504399651772205

theorem tailTrace_6015039 : CollatzResearch.WordTrace tailWord_6015039 prefixEnd_6015039 343178462504399651772205 := by
  unfold tailWord_6015039
  simp only [CollatzResearch.WordTrace]
  refine ⟨219386495655548464719824171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146257663770365643146549447 219386495655548464719824171)
  ·
    refine ⟨329079743483322697079736257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219386495655548464719824171 329079743483322697079736257)
    ·
      refine ⟨246809807612492022809802193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329079743483322697079736257 246809807612492022809802193)
      ·
        refine ⟨185107355709369017107351645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246809807612492022809802193 185107355709369017107351645)
        ·
          refine ⟨69415258391013381415256867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185107355709369017107351645 69415258391013381415256867)
          ·
            refine ⟨104122887586520072122885301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69415258391013381415256867 104122887586520072122885301)
            ·
              refine ⟨9761520711236256761520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104122887586520072122885301 9761520711236256761520497)
              ·
                refine ⟨7321140533427192571140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761520711236256761520497 7321140533427192571140373)
                ·
                  refine ⟨343178462504399651772205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7321140533427192571140373 343178462504399651772205)
                  ·
                    rfl

theorem cell23_6015039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 6].length) (baseStart_6015039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015039 prefixEnd_6015039 := by exact prefixLift 6015039
  have htrace : WordTrace (prefixWord ++ tailWord_6015039) baseStart_6015039 baseEnd_6015039 := by
    simpa [prefixWord, tailWord_6015039, baseEnd_6015039] using wordTrace_append hprefix tailTrace_6015039
  have hstable : (prefixWord ++ tailWord_6015039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015039).length < 2 ^ (prefixWord ++ tailWord_6015039).sum := by decide
  have hdescent : baseEnd_6015039 < baseStart_6015039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015046 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6015046 : Nat := 118140960795 + 6015046 * 2 ^ 59
def prefixEnd_6015046 : Nat := 4983230072969 + 3 ^ 40 * 6015046 * 2
def baseEnd_6015046 : Nat := 3088609756904178338562313

theorem tailTrace_6015046 : CollatzResearch.WordTrace tailWord_6015046 prefixEnd_6015046 3088609756904178338562313 := by
  unfold tailWord_6015046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6855835967703847028604031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146257833977682069943552661 6855835967703847028604031)
  ·
    refine ⟨10283753951555770542906047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6855835967703847028604031 10283753951555770542906047)
    ·
      refine ⟨15425630927333655814359071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10283753951555770542906047 15425630927333655814359071)
      ·
        refine ⟨23138446391000483721538607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15425630927333655814359071 23138446391000483721538607)
        ·
          refine ⟨34707669586500725582307911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23138446391000483721538607 34707669586500725582307911)
          ·
            refine ⟨52061504379751088373461867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34707669586500725582307911 52061504379751088373461867)
            ·
              refine ⟨78092256569626632560192801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52061504379751088373461867 78092256569626632560192801)
              ·
                refine ⟨58569192427219974420144601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78092256569626632560192801 58569192427219974420144601)
                ·
                  refine ⟨43926894320414980815108451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58569192427219974420144601 43926894320414980815108451)
                  ·
                    refine ⟨65890341480622471222662677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43926894320414980815108451 65890341480622471222662677)
                    ·
                      refine ⟨3088609756904178338562313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65890341480622471222662677 3088609756904178338562313)
                      ·
                        rfl

theorem cell23_6015046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6015046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015046 prefixEnd_6015046 := by exact prefixLift 6015046
  have htrace : WordTrace (prefixWord ++ tailWord_6015046) baseStart_6015046 baseEnd_6015046 := by
    simpa [prefixWord, tailWord_6015046, baseEnd_6015046] using wordTrace_append hprefix tailTrace_6015046
  have hstable : (prefixWord ++ tailWord_6015046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015046).length < 2 ^ (prefixWord ++ tailWord_6015046).sum := by decide
  have hdescent : baseEnd_6015046 < baseStart_6015046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015066 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_6015066 : Nat := 118140960795 + 6015066 * 2 ^ 59
def prefixEnd_6015066 : Nat := 4983230072969 + 3 ^ 40 * 6015066 * 2
def baseEnd_6015066 : Nat := 3088620026517268260312221

theorem tailTrace_6015066 : CollatzResearch.WordTrace tailWord_6015066 prefixEnd_6015066 3088620026517268260312221 := by
  unfold tailWord_6015066
  simp only [CollatzResearch.WordTrace]
  refine ⟨54846870106612662082764263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146258320284300432220704701 54846870106612662082764263)
  ·
    refine ⟨82270305159918993124146395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54846870106612662082764263 82270305159918993124146395)
    ·
      refine ⟨123405457739878489686219593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82270305159918993124146395 123405457739878489686219593)
      ·
        refine ⟨92554093304908867264664695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123405457739878489686219593 92554093304908867264664695)
        ·
          refine ⟨138831139957363300896997043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92554093304908867264664695 138831139957363300896997043)
          ·
            refine ⟨208246709936044951345495565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138831139957363300896997043 208246709936044951345495565)
            ·
              refine ⟨78092516226016856754560837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208246709936044951345495565 78092516226016856754560837)
              ·
                refine ⟨14642346792378160641480157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78092516226016856754560837 14642346792378160641480157)
                ·
                  refine ⟨5490880047141810240555059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14642346792378160641480157 5490880047141810240555059)
                  ·
                    refine ⟨8236320070712715360832589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490880047141810240555059 8236320070712715360832589)
                    ·
                      refine ⟨3088620026517268260312221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236320070712715360832589 3088620026517268260312221)
                      ·
                        rfl

theorem cell23_6015066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_6015066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015066 prefixEnd_6015066 := by exact prefixLift 6015066
  have htrace : WordTrace (prefixWord ++ tailWord_6015066) baseStart_6015066 baseEnd_6015066 := by
    simpa [prefixWord, tailWord_6015066, baseEnd_6015066] using wordTrace_append hprefix tailTrace_6015066
  have hstable : (prefixWord ++ tailWord_6015066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015066).length < 2 ^ (prefixWord ++ tailWord_6015066).sum := by decide
  have hdescent : baseEnd_6015066 < baseStart_6015066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015076 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_6015076 : Nat := 118140960795 + 6015076 * 2 ^ 59
def prefixEnd_6015076 : Nat := 4983230072969 + 3 ^ 40 * 6015076 * 2
def baseEnd_6015076 : Nat := 3088625161323813221187175

theorem tailTrace_6015076 : CollatzResearch.WordTrace tailWord_6015076 prefixEnd_6015076 3088625161323813221187175 := by
  unfold tailWord_6015076
  simp only [CollatzResearch.WordTrace]
  refine ⟨109693922578207210019460541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146258563437609613359280721 109693922578207210019460541)
  ·
    refine ⟨41135220966827703757297703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109693922578207210019460541 41135220966827703757297703)
    ·
      refine ⟨61702831450241555635946555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41135220966827703757297703 61702831450241555635946555)
      ·
        refine ⟨92554247175362333453919833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61702831450241555635946555 92554247175362333453919833)
        ·
          refine ⟨69415685381521750090439875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92554247175362333453919833 69415685381521750090439875)
          ·
            refine ⟨104123528072282625135659813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69415685381521750090439875 104123528072282625135659813)
            ·
              refine ⟨19523161513552992212936215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104123528072282625135659813 19523161513552992212936215)
              ·
                refine ⟨29284742270329488319404323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19523161513552992212936215 29284742270329488319404323)
                ·
                  refine ⟨43927113405494232479106485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29284742270329488319404323 43927113405494232479106485)
                  ·
                    refine ⟨4118166881765084294916233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43927113405494232479106485 4118166881765084294916233)
                    ·
                      refine ⟨3088625161323813221187175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118166881765084294916233 3088625161323813221187175)
                      ·
                        rfl

theorem cell23_6015076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_6015076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015076 prefixEnd_6015076 := by exact prefixLift 6015076
  have htrace : WordTrace (prefixWord ++ tailWord_6015076) baseStart_6015076 baseEnd_6015076 := by
    simpa [prefixWord, tailWord_6015076, baseEnd_6015076] using wordTrace_append hprefix tailTrace_6015076
  have hstable : (prefixWord ++ tailWord_6015076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015076).length < 2 ^ (prefixWord ++ tailWord_6015076).sum := by decide
  have hdescent : baseEnd_6015076 < baseStart_6015076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015086 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_6015086 : Nat := 118140960795 + 6015086 * 2 ^ 59
def prefixEnd_6015086 : Nat := 4983230072969 + 3 ^ 40 * 6015086 * 2
def baseEnd_6015086 : Nat := 1029543432043452727354043

theorem tailTrace_6015086 : CollatzResearch.WordTrace tailWord_6015086 prefixEnd_6015086 1029543432043452727354043 := by
  unfold tailWord_6015086
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423526235797273968348139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146258806590918794497856741 27423526235797273968348139)
  ·
    refine ⟨41135289353695910952522209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27423526235797273968348139 41135289353695910952522209)
    ·
      refine ⟨30851467015271933214391657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41135289353695910952522209 30851467015271933214391657)
      ·
        refine ⟨23138600261453949910793743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30851467015271933214391657 23138600261453949910793743)
        ·
          refine ⟨34707900392180924866190615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23138600261453949910793743 34707900392180924866190615)
          ·
            refine ⟨52061850588271387299285923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34707900392180924866190615 52061850588271387299285923)
            ·
              refine ⟨78092775882407080948928885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52061850588271387299285923 78092775882407080948928885)
              ·
                refine ⟨7321197738975663838962083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78092775882407080948928885 7321197738975663838962083)
                ·
                  refine ⟨10981796608463495758443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321197738975663838962083 10981796608463495758443125)
                  ·
                    refine ⟨1029543432043452727354043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10981796608463495758443125 1029543432043452727354043)
                    ·
                      rfl

theorem cell23_6015086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_6015086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015086 prefixEnd_6015086 := by exact prefixLift 6015086
  have htrace : WordTrace (prefixWord ++ tailWord_6015086) baseStart_6015086 baseEnd_6015086 := by
    simpa [prefixWord, tailWord_6015086, baseEnd_6015086] using wordTrace_append hprefix tailTrace_6015086
  have hstable : (prefixWord ++ tailWord_6015086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015086).length < 2 ^ (prefixWord ++ tailWord_6015086).sum := by decide
  have hdescent : baseEnd_6015086 < baseStart_6015086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015136 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6015136 : Nat := 118140960795 + 6015136 * 2 ^ 59
def prefixEnd_6015136 : Nat := 4983230072969 + 3 ^ 40 * 6015136 * 2
def baseEnd_6015136 : Nat := 3088655970163082986436899

theorem tailTrace_6015136 : CollatzResearch.WordTrace tailWord_6015136 prefixEnd_6015136 3088655970163082986436899 := by
  unfold tailWord_6015136
  simp only [CollatzResearch.WordTrace]
  refine ⟨109695016768098525143052631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146260022357464700190736841 109695016768098525143052631)
  ·
    refine ⟨164542525152147787714578947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109695016768098525143052631 164542525152147787714578947)
    ·
      refine ⟨246813787728221681571868421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164542525152147787714578947 246813787728221681571868421)
      ·
        refine ⟨46277585199041565294725329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246813787728221681571868421 46277585199041565294725329)
        ·
          refine ⟨34708188899281173971043997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46277585199041565294725329 34708188899281173971043997)
          ·
            refine ⟨13015570837230440239141499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34708188899281173971043997 13015570837230440239141499)
            ·
              refine ⟨19523356255845660358712249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015570837230440239141499 19523356255845660358712249)
              ·
                refine ⟨14642517191884245269034187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19523356255845660358712249 14642517191884245269034187)
                ·
                  refine ⟨21963775787826367903551281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14642517191884245269034187 21963775787826367903551281)
                  ·
                    refine ⟨16472831840869775927663461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21963775787826367903551281 16472831840869775927663461)
                    ·
                      refine ⟨3088655970163082986436899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16472831840869775927663461 3088655970163082986436899)
                      ·
                        rfl

theorem cell23_6015136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6015136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015136 prefixEnd_6015136 := by exact prefixLift 6015136
  have htrace : WordTrace (prefixWord ++ tailWord_6015136) baseStart_6015136 baseEnd_6015136 := by
    simpa [prefixWord, tailWord_6015136, baseEnd_6015136] using wordTrace_append hprefix tailTrace_6015136
  have hstable : (prefixWord ++ tailWord_6015136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015136).length < 2 ^ (prefixWord ++ tailWord_6015136).sum := by decide
  have hdescent : baseEnd_6015136 < baseStart_6015136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015140 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_6015140 : Nat := 118140960795 + 6015140 * 2 ^ 59
def prefixEnd_6015140 : Nat := 4983230072969 + 3 ^ 40 * 6015140 * 2
def baseEnd_6015140 : Nat := 3088658024085700970786881

theorem tailTrace_6015140 : CollatzResearch.WordTrace tailWord_6015140 prefixEnd_6015140 3088658024085700970786881 := by
  unfold tailWord_6015140
  simp only [CollatzResearch.WordTrace]
  refine ⟨109695089714091279484625437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146260119618788372646167249 109695089714091279484625437)
  ·
    refine ⟨41135658642784229806734539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109695089714091279484625437 41135658642784229806734539)
    ·
      refine ⟨61703487964176344710101809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41135658642784229806734539 61703487964176344710101809)
      ·
        refine ⟨46277615973132258532576357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61703487964176344710101809 46277615973132258532576357)
        ·
          refine ⟨8677052994962298474858067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46277615973132258532576357 8677052994962298474858067)
          ·
            refine ⟨13015579492443447712287101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677052994962298474858067 13015579492443447712287101)
            ·
              refine ⟨4880842309666292892107663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13015579492443447712287101 4880842309666292892107663)
              ·
                refine ⟨7321263464499439338161495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880842309666292892107663 7321263464499439338161495)
                ·
                  refine ⟨10981895196749159007242243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321263464499439338161495 10981895196749159007242243)
                  ·
                    refine ⟨16472842795123738510863365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10981895196749159007242243 16472842795123738510863365)
                    ·
                      refine ⟨3088658024085700970786881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16472842795123738510863365 3088658024085700970786881)
                      ·
                        rfl

theorem cell23_6015140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_6015140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015140 prefixEnd_6015140 := by exact prefixLift 6015140
  have htrace : WordTrace (prefixWord ++ tailWord_6015140) baseStart_6015140 baseEnd_6015140 := by
    simpa [prefixWord, tailWord_6015140, baseEnd_6015140] using wordTrace_append hprefix tailTrace_6015140
  have hstable : (prefixWord ++ tailWord_6015140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015140).length < 2 ^ (prefixWord ++ tailWord_6015140).sum := by decide
  have hdescent : baseEnd_6015140 < baseStart_6015140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015146 : List Nat := [3, 1, 5, 1, 2, 11]
def baseStart_6015146 : Nat := 118140960795 + 6015146 * 2 ^ 59
def prefixEnd_6015146 : Nat := 4983230072969 + 3 ^ 40 * 6015146 * 2
def baseEnd_6015146 : Nat := 12710539526623983322271

theorem tailTrace_6015146 : CollatzResearch.WordTrace tailWord_6015146 prefixEnd_6015146 12710539526623983322271 := by
  unfold tailWord_6015146
  simp only [CollatzResearch.WordTrace]
  refine ⟨54847599566540205498492323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146260265510773881329312861 54847599566540205498492323)
  ·
    refine ⟨82271399349810308247738485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54847599566540205498492323 82271399349810308247738485)
    ·
      refine ⟨7712943689044716398225483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82271399349810308247738485 7712943689044716398225483)
      ·
        refine ⟨11569415533567074597338225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7712943689044716398225483 11569415533567074597338225)
        ·
          refine ⟨8677061650175305948003669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11569415533567074597338225 8677061650175305948003669)
          ·
            refine ⟨12710539526623983322271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8677061650175305948003669 12710539526623983322271)
            ·
              rfl

theorem cell23_6015146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 11].length) (baseStart_6015146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015146 prefixEnd_6015146 := by exact prefixLift 6015146
  have htrace : WordTrace (prefixWord ++ tailWord_6015146) baseStart_6015146 baseEnd_6015146 := by
    simpa [prefixWord, tailWord_6015146, baseEnd_6015146] using wordTrace_append hprefix tailTrace_6015146
  have hstable : (prefixWord ++ tailWord_6015146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015146).length < 2 ^ (prefixWord ++ tailWord_6015146).sum := by decide
  have hdescent : baseEnd_6015146 < baseStart_6015146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015159 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 7]
def baseStart_6015159 : Nat := 118140960795 + 6015159 * 2 ^ 59
def prefixEnd_6015159 : Nat := 4983230072969 + 3 ^ 40 * 6015159 * 2
def baseEnd_6015159 : Nat := 1029555926739378798816431

theorem tailTrace_6015159 : CollatzResearch.WordTrace tailWord_6015159 prefixEnd_6015159 1029555926739378798816431 := by
  unfold tailWord_6015159
  simp only [CollatzResearch.WordTrace]
  refine ⟨219390872415113725214192531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146260581610075816809461687 219390872415113725214192531)
  ·
    refine ⟨329086308622670587821288797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219390872415113725214192531 329086308622670587821288797)
    ·
      refine ⟨123407365733501470432983299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329086308622670587821288797 123407365733501470432983299)
      ·
        refine ⟨185111048600252205649474949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123407365733501470432983299 185111048600252205649474949)
        ·
          refine ⟨34708321612547288559276553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185111048600252205649474949 34708321612547288559276553)
          ·
            refine ⟨26031241209410466419457415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34708321612547288559276553 26031241209410466419457415)
            ·
              refine ⟨39046861814115699629186123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26031241209410466419457415 39046861814115699629186123)
              ·
                refine ⟨58570292721173549443779185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39046861814115699629186123 58570292721173549443779185)
                ·
                  refine ⟨43927719540880162082834389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58570292721173549443779185 43927719540880162082834389)
                  ·
                    refine ⟨1029555926739378798816431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43927719540880162082834389 1029555926739378798816431)
                    ·
                      rfl

theorem cell23_6015159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_6015159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015159 prefixEnd_6015159 := by exact prefixLift 6015159
  have htrace : WordTrace (prefixWord ++ tailWord_6015159) baseStart_6015159 baseEnd_6015159 := by
    simpa [prefixWord, tailWord_6015159, baseEnd_6015159] using wordTrace_append hprefix tailTrace_6015159
  have hstable : (prefixWord ++ tailWord_6015159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015159).length < 2 ^ (prefixWord ++ tailWord_6015159).sum := by decide
  have hdescent : baseEnd_6015159 < baseStart_6015159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015170 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6015170 : Nat := 118140960795 + 6015170 * 2 ^ 59
def prefixEnd_6015170 : Nat := 4983230072969 + 3 ^ 40 * 6015170 * 2
def baseEnd_6015170 : Nat := 3088673428505335853411743

theorem tailTrace_6015170 : CollatzResearch.WordTrace tailWord_6015170 prefixEnd_6015170 3088673428505335853411743 := by
  unfold tailWord_6015170
  simp only [CollatzResearch.WordTrace]
  refine ⟨54847818404518468523210741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146260849078715916061895309 54847818404518468523210741)
  ·
    refine ⟨5141982975423606424051007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54847818404518468523210741 5141982975423606424051007)
    ·
      refine ⟨7712974463135409636076511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5141982975423606424051007 7712974463135409636076511)
      ·
        refine ⟨11569461694703114454114767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7712974463135409636076511 11569461694703114454114767)
        ·
          refine ⟨17354192542054671681172151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11569461694703114454114767 17354192542054671681172151)
          ·
            refine ⟨26031288813082007521758227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17354192542054671681172151 26031288813082007521758227)
            ·
              refine ⟨39046933219623011282637341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26031288813082007521758227 39046933219623011282637341)
              ·
                refine ⟨14642599957358629230989003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39046933219623011282637341 14642599957358629230989003)
                ·
                  refine ⟨21963899936037943846483505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14642599957358629230989003 21963899936037943846483505)
                  ·
                    refine ⟨16472924952028457884862629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21963899936037943846483505 16472924952028457884862629)
                    ·
                      refine ⟨3088673428505335853411743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16472924952028457884862629 3088673428505335853411743)
                      ·
                        rfl

theorem cell23_6015170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6015170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015170 prefixEnd_6015170 := by exact prefixLift 6015170
  have htrace : WordTrace (prefixWord ++ tailWord_6015170) baseStart_6015170 baseEnd_6015170 := by
    simpa [prefixWord, tailWord_6015170, baseEnd_6015170] using wordTrace_append hprefix tailTrace_6015170
  have hstable : (prefixWord ++ tailWord_6015170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015170).length < 2 ^ (prefixWord ++ tailWord_6015170).sum := by decide
  have hdescent : baseEnd_6015170 < baseStart_6015170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015173 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_6015173 : Nat := 118140960795 + 6015173 * 2 ^ 59
def prefixEnd_6015173 : Nat := 4983230072969 + 3 ^ 40 * 6015173 * 2
def baseEnd_6015173 : Nat := 3088674968947299341674229

theorem tailTrace_6015173 : CollatzResearch.WordTrace tailWord_6015173 prefixEnd_6015173 3088674968947299341674229 := by
  unfold tailWord_6015173
  simp only [CollatzResearch.WordTrace]
  refine ⟨219391383037063005605202173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146260922024708670403468115 219391383037063005605202173)
  ·
    refine ⟨82271768638898627101950815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219391383037063005605202173 82271768638898627101950815)
    ·
      refine ⟨123407652958347940652926223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82271768638898627101950815 123407652958347940652926223)
      ·
        refine ⟨185111479437521910979389335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123407652958347940652926223 185111479437521910979389335)
        ·
          refine ⟨277667219156282866469084003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185111479437521910979389335 277667219156282866469084003)
          ·
            refine ⟨416500828734424299703626005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277667219156282866469084003 416500828734424299703626005)
            ·
              refine ⟨19523476346926139048607469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 416500828734424299703626005 19523476346926139048607469)
              ·
                refine ⟨7321303630097302143227801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19523476346926139048607469 7321303630097302143227801)
                ·
                  refine ⟨5490977722572976607420851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321303630097302143227801 5490977722572976607420851)
                  ·
                    refine ⟨8236466583859464911131277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490977722572976607420851 8236466583859464911131277)
                    ·
                      refine ⟨3088674968947299341674229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236466583859464911131277 3088674968947299341674229)
                      ·
                        rfl

theorem cell23_6015173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_6015173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015173 prefixEnd_6015173 := by exact prefixLift 6015173
  have htrace : WordTrace (prefixWord ++ tailWord_6015173) baseStart_6015173 baseEnd_6015173 := by
    simpa [prefixWord, tailWord_6015173, baseEnd_6015173] using wordTrace_append hprefix tailTrace_6015173
  have hstable : (prefixWord ++ tailWord_6015173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015173).length < 2 ^ (prefixWord ++ tailWord_6015173).sum := by decide
  have hdescent : baseEnd_6015173 < baseStart_6015173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015179 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_6015179 : Nat := 118140960795 + 6015179 * 2 ^ 59
def prefixEnd_6015179 : Nat := 4983230072969 + 3 ^ 40 * 6015179 * 2
def baseEnd_6015179 : Nat := 3088678049831226318199201

theorem tailTrace_6015179 : CollatzResearch.WordTrace tailWord_6015179 prefixEnd_6015179 3088678049831226318199201 := by
  unfold tailWord_6015179
  simp only [CollatzResearch.WordTrace]
  refine ⟨219391601875041268629920591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146261067916694179086613727 219391601875041268629920591)
  ·
    refine ⟨329087402812561902944880887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219391601875041268629920591 329087402812561902944880887)
    ·
      refine ⟨493631104218842854417321331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329087402812561902944880887 493631104218842854417321331)
      ·
        refine ⟨740446656328264281625981997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493631104218842854417321331 740446656328264281625981997)
        ·
          refine ⟨277667496123099105609743249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740446656328264281625981997 277667496123099105609743249)
          ·
            refine ⟨208250622092324329207307437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277667496123099105609743249 208250622092324329207307437)
            ·
              refine ⟨78093983284621623452740289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208250622092324329207307437 78093983284621623452740289)
              ·
                refine ⟨58570487463466217589555217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78093983284621623452740289 58570487463466217589555217)
                ·
                  refine ⟨43927865597599663192166413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58570487463466217589555217 43927865597599663192166413)
                  ·
                    refine ⟨16472949599099873697062405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43927865597599663192166413 16472949599099873697062405)
                    ·
                      refine ⟨3088678049831226318199201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16472949599099873697062405 3088678049831226318199201)
                      ·
                        rfl

theorem cell23_6015179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_6015179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015179 prefixEnd_6015179 := by exact prefixLift 6015179
  have htrace : WordTrace (prefixWord ++ tailWord_6015179) baseStart_6015179 baseEnd_6015179 := by
    simpa [prefixWord, tailWord_6015179, baseEnd_6015179] using wordTrace_append hprefix tailTrace_6015179
  have hstable : (prefixWord ++ tailWord_6015179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015179).length < 2 ^ (prefixWord ++ tailWord_6015179).sum := by decide
  have hdescent : baseEnd_6015179 < baseStart_6015179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015183 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 1, 3, 2]
def baseStart_6015183 : Nat := 118140960795 + 6015183 * 2 ^ 59
def prefixEnd_6015183 : Nat := 4983230072969 + 3 ^ 40 * 6015183 * 2
def baseEnd_6015183 : Nat := 3088680103753844302549183

theorem tailTrace_6015183 : CollatzResearch.WordTrace tailWord_6015183 prefixEnd_6015183 3088680103753844302549183 := by
  unfold tailWord_6015183
  simp only [CollatzResearch.WordTrace]
  refine ⟨219391747767026777313066203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146261165178017851542044135 219391747767026777313066203)
  ·
    refine ⟨329087621650540165969599305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219391747767026777313066203 329087621650540165969599305)
    ·
      refine ⟨246815716237905124477199479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329087621650540165969599305 246815716237905124477199479)
      ·
        refine ⟨370223574356857686715799219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246815716237905124477199479 370223574356857686715799219)
        ·
          refine ⟨555335361535286530073698829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370223574356857686715799219 555335361535286530073698829)
          ·
            refine ⟨208250760575732448777637061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555335361535286530073698829 208250760575732448777637061)
            ·
              refine ⟨39047017607949834145806949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208250760575732448777637061 39047017607949834145806949)
              ·
                refine ⟨7321315801490593902338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39047017607949834145806949 7321315801490593902338803)
                ·
                  refine ⟨10981973702235890853508205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321315801490593902338803 10981973702235890853508205)
                  ·
                    refine ⟨4118240138338459070065577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10981973702235890853508205 4118240138338459070065577)
                    ·
                      refine ⟨3088680103753844302549183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118240138338459070065577 3088680103753844302549183)
                      ·
                        rfl

theorem cell23_6015183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3, 2].length) (baseStart_6015183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015183 prefixEnd_6015183 := by exact prefixLift 6015183
  have htrace : WordTrace (prefixWord ++ tailWord_6015183) baseStart_6015183 baseEnd_6015183 := by
    simpa [prefixWord, tailWord_6015183, baseEnd_6015183] using wordTrace_append hprefix tailTrace_6015183
  have hstable : (prefixWord ++ tailWord_6015183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015183).length < 2 ^ (prefixWord ++ tailWord_6015183).sum := by decide
  have hdescent : baseEnd_6015183 < baseStart_6015183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015190 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6015190 : Nat := 118140960795 + 6015190 * 2 ^ 59
def prefixEnd_6015190 : Nat := 4983230072969 + 3 ^ 40 * 6015190 * 2
def baseEnd_6015190 : Nat := 3088683698118425775161651

theorem tailTrace_6015190 : CollatzResearch.WordTrace tailWord_6015190 prefixEnd_6015190 3088683698118425775161651 := by
  unfold tailWord_6015190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712000192375088594285689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146261335385334278339047349 13712000192375088594285689)
  ·
    refine ⟨10284000144281316445714267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13712000192375088594285689 10284000144281316445714267)
    ·
      refine ⟨15426000216421974668571401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10284000144281316445714267 15426000216421974668571401)
      ·
        refine ⟨11569500162316481001428551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15426000216421974668571401 11569500162316481001428551)
        ·
          refine ⟨17354250243474721502142827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11569500162316481001428551 17354250243474721502142827)
          ·
            refine ⟨26031375365212082253214241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17354250243474721502142827 26031375365212082253214241)
            ·
              refine ⟨19523531523909061689910681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26031375365212082253214241 19523531523909061689910681)
              ·
                refine ⟨14642648642931796267433011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19523531523909061689910681 14642648642931796267433011)
                ·
                  refine ⟨21963972964397694401149517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14642648642931796267433011 21963972964397694401149517)
                  ·
                    refine ⟨8236489861649135400431069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21963972964397694401149517 8236489861649135400431069)
                    ·
                      refine ⟨3088683698118425775161651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236489861649135400431069 3088683698118425775161651)
                      ·
                        rfl

theorem cell23_6015190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6015190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015190 prefixEnd_6015190 := by exact prefixLift 6015190
  have htrace : WordTrace (prefixWord ++ tailWord_6015190) baseStart_6015190 baseEnd_6015190 := by
    simpa [prefixWord, tailWord_6015190, baseEnd_6015190] using wordTrace_append hprefix tailTrace_6015190
  have hstable : (prefixWord ++ tailWord_6015190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015190).length < 2 ^ (prefixWord ++ tailWord_6015190).sum := by decide
  have hdescent : baseEnd_6015190 < baseStart_6015190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015199 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_6015199 : Nat := 118140960795 + 6015199 * 2 ^ 59
def prefixEnd_6015199 : Nat := 4983230072969 + 3 ^ 40 * 6015199 * 2
def baseEnd_6015199 : Nat := 3088688319444316239949109

theorem tailTrace_6015199 : CollatzResearch.WordTrace tailWord_6015199 prefixEnd_6015199 3088688319444316239949109 := by
  unfold tailWord_6015199
  simp only [CollatzResearch.WordTrace]
  refine ⟨219392331334968812045648651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146261554223312541363765767 219392331334968812045648651)
  ·
    refine ⟨329088497002453218068472977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219392331334968812045648651 329088497002453218068472977)
    ·
      refine ⟨246816372751839913551354733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329088497002453218068472977 246816372751839913551354733)
      ·
        refine ⟨92556139781939967581758025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246816372751839913551354733 92556139781939967581758025)
        ·
          refine ⟨69417104836454975686318519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92556139781939967581758025 69417104836454975686318519)
          ·
            refine ⟨104125657254682463529477779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69417104836454975686318519 104125657254682463529477779)
            ·
              refine ⟨156188485882023695294216669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104125657254682463529477779 156188485882023695294216669)
              ·
                refine ⟨58570682205758885735331251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156188485882023695294216669 58570682205758885735331251)
                ·
                  refine ⟨87856023308638328602996877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58570682205758885735331251 87856023308638328602996877)
                  ·
                    refine ⟨32946008740739373226123829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87856023308638328602996877 32946008740739373226123829)
                    ·
                      refine ⟨3088688319444316239949109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32946008740739373226123829 3088688319444316239949109)
                      ·
                        rfl

theorem cell23_6015199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_6015199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015199 prefixEnd_6015199 := by exact prefixLift 6015199
  have htrace : WordTrace (prefixWord ++ tailWord_6015199) baseStart_6015199 baseEnd_6015199 := by
    simpa [prefixWord, tailWord_6015199, baseEnd_6015199] using wordTrace_append hprefix tailTrace_6015199
  have hstable : (prefixWord ++ tailWord_6015199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015199).length < 2 ^ (prefixWord ++ tailWord_6015199).sum := by decide
  have hdescent : baseEnd_6015199 < baseStart_6015199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015207 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6015207 : Nat := 118140960795 + 6015207 * 2 ^ 59
def prefixEnd_6015207 : Nat := 4983230072969 + 3 ^ 40 * 6015207 * 2
def baseEnd_6015207 : Nat := 3088692427289552208649073

theorem tailTrace_6015207 : CollatzResearch.WordTrace tailWord_6015207 prefixEnd_6015207 3088692427289552208649073 := by
  unfold tailWord_6015207
  simp only [CollatzResearch.WordTrace]
  refine ⟨219392623118939829411939875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146261748745959886274626583 219392623118939829411939875)
  ·
    refine ⟨329088934678409744117909813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219392623118939829411939875 329088934678409744117909813)
    ·
      refine ⟨30852087626100913511054045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329088934678409744117909813 30852087626100913511054045)
      ·
        refine ⟨11569532859787842566645267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30852087626100913511054045 11569532859787842566645267)
        ·
          refine ⟨17354299289681763849967901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11569532859787842566645267 17354299289681763849967901)
          ·
            refine ⟨6507862233630661443737963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17354299289681763849967901 6507862233630661443737963)
            ·
              refine ⟨9761793350445992165606945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507862233630661443737963 9761793350445992165606945)
              ·
                refine ⟨7321345012834494124205209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761793350445992165606945 7321345012834494124205209)
                ·
                  refine ⟨5491008759625870593153907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321345012834494124205209 5491008759625870593153907)
                  ·
                    refine ⟨8236513139438805889730861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491008759625870593153907 8236513139438805889730861)
                    ·
                      refine ⟨3088692427289552208649073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236513139438805889730861 3088692427289552208649073)
                      ·
                        rfl

theorem cell23_6015207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6015207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015207 prefixEnd_6015207 := by exact prefixLift 6015207
  have htrace : WordTrace (prefixWord ++ tailWord_6015207) baseStart_6015207 baseEnd_6015207 := by
    simpa [prefixWord, tailWord_6015207, baseEnd_6015207] using wordTrace_append hprefix tailTrace_6015207
  have hstable : (prefixWord ++ tailWord_6015207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015207).length < 2 ^ (prefixWord ++ tailWord_6015207).sum := by decide
  have hdescent : baseEnd_6015207 < baseStart_6015207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015209 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_6015209 : Nat := 118140960795 + 6015209 * 2 ^ 59
def prefixEnd_6015209 : Nat := 4983230072969 + 3 ^ 40 * 6015209 * 2
def baseEnd_6015209 : Nat := 3088693454250861200824063

theorem tailTrace_6015209 : CollatzResearch.WordTrace tailWord_6015209 prefixEnd_6015209 3088693454250861200824063 := by
  unfold tailWord_6015209
  simp only [CollatzResearch.WordTrace]
  refine ⟨219392696064932583753512681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146261797376621722502341787 219392696064932583753512681)
  ·
    refine ⟨164544522048699437815134511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219392696064932583753512681 164544522048699437815134511)
    ·
      refine ⟨246816783073049156722701767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164544522048699437815134511 246816783073049156722701767)
      ·
        refine ⟨370225174609573735084052651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246816783073049156722701767 370225174609573735084052651)
        ·
          refine ⟨555337761914360602626078977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370225174609573735084052651 555337761914360602626078977)
          ·
            refine ⟨416503321435770451969559233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555337761914360602626078977 416503321435770451969559233)
            ·
              refine ⟨312377491076827838977169425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416503321435770451969559233 312377491076827838977169425)
              ·
                refine ⟨234283118307620879232877069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312377491076827838977169425 234283118307620879232877069)
                ·
                  refine ⟨87856169365357829712328901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234283118307620879232877069 87856169365357829712328901)
                  ·
                    refine ⟨16473031756004593071061669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87856169365357829712328901 16473031756004593071061669)
                    ·
                      refine ⟨3088693454250861200824063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16473031756004593071061669 3088693454250861200824063)
                      ·
                        rfl

theorem cell23_6015209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_6015209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015209 prefixEnd_6015209 := by exact prefixLift 6015209
  have htrace : WordTrace (prefixWord ++ tailWord_6015209) baseStart_6015209 baseEnd_6015209 := by
    simpa [prefixWord, tailWord_6015209, baseEnd_6015209] using wordTrace_append hprefix tailTrace_6015209
  have hstable : (prefixWord ++ tailWord_6015209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015209).length < 2 ^ (prefixWord ++ tailWord_6015209).sum := by decide
  have hdescent : baseEnd_6015209 < baseStart_6015209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015226 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_6015226 : Nat := 118140960795 + 6015226 * 2 ^ 59
def prefixEnd_6015226 : Nat := 4983230072969 + 3 ^ 40 * 6015226 * 2
def baseEnd_6015226 : Nat := 3088702183421987634311485

theorem tailTrace_6015226 : CollatzResearch.WordTrace tailWord_6015226 prefixEnd_6015226 3088702183421987634311485 := by
  unfold tailWord_6015226
  simp only [CollatzResearch.WordTrace]
  refine ⟨54848329026467748914220383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146262210737247330437921021 54848329026467748914220383)
  ·
    refine ⟨82272493539701623371330575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54848329026467748914220383 82272493539701623371330575)
    ·
      refine ⟨123408740309552435056995863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82272493539701623371330575 123408740309552435056995863)
      ·
        refine ⟨185113110464328652585493795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123408740309552435056995863 185113110464328652585493795)
        ·
          refine ⟨277669665696492978878240693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185113110464328652585493795 277669665696492978878240693)
          ·
            refine ⟨26031531159046216769835065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277669665696492978878240693 26031531159046216769835065)
            ·
              refine ⟨19523648369284662577376299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26031531159046216769835065 19523648369284662577376299)
              ·
                refine ⟨29285472553926993866064449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19523648369284662577376299 29285472553926993866064449)
                ·
                  refine ⟨21964104415445245399548337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29285472553926993866064449 21964104415445245399548337)
                  ·
                    refine ⟨16473078311583934049661253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21964104415445245399548337 16473078311583934049661253)
                    ·
                      refine ⟨3088702183421987634311485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16473078311583934049661253 3088702183421987634311485)
                      ·
                        rfl

theorem cell23_6015226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_6015226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015226 prefixEnd_6015226 := by exact prefixLift 6015226
  have htrace : WordTrace (prefixWord ++ tailWord_6015226) baseStart_6015226 baseEnd_6015226 := by
    simpa [prefixWord, tailWord_6015226, baseEnd_6015226] using wordTrace_append hprefix tailTrace_6015226
  have hstable : (prefixWord ++ tailWord_6015226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015226).length < 2 ^ (prefixWord ++ tailWord_6015226).sum := by decide
  have hdescent : baseEnd_6015226 < baseStart_6015226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015229 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_6015229 : Nat := 118140960795 + 6015229 * 2 ^ 59
def prefixEnd_6015229 : Nat := 4983230072969 + 3 ^ 40 * 6015229 * 2
def baseEnd_6015229 : Nat := 3088703723863951122573971

theorem tailTrace_6015229 : CollatzResearch.WordTrace tailWord_6015229 prefixEnd_6015229 3088703723863951122573971 := by
  unfold tailWord_6015229
  simp only [CollatzResearch.WordTrace]
  refine ⟨219393425524860127169240741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146262283683240084779493827 219393425524860127169240741)
  ·
    refine ⟨41136267285911273844232639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219393425524860127169240741 41136267285911273844232639)
    ·
      refine ⟨61704400928866910766348959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41136267285911273844232639 61704400928866910766348959)
      ·
        refine ⟨92556601393300366149523439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61704400928866910766348959 92556601393300366149523439)
        ·
          refine ⟨138834902089950549224285159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92556601393300366149523439 138834902089950549224285159)
          ·
            refine ⟨208252353134925823836427739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138834902089950549224285159 208252353134925823836427739)
            ·
              refine ⟨312378529702388735754641609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208252353134925823836427739 312378529702388735754641609)
              ·
                refine ⟨234283897276791551815981207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312378529702388735754641609 234283897276791551815981207)
                ·
                  refine ⟨351425845915187327723971811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234283897276791551815981207 351425845915187327723971811)
                  ·
                    refine ⟨527138768872780991585957717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 351425845915187327723971811 527138768872780991585957717)
                    ·
                      refine ⟨3088703723863951122573971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 527138768872780991585957717 3088703723863951122573971)
                      ·
                        rfl

theorem cell23_6015229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_6015229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015229 prefixEnd_6015229 := by exact prefixLift 6015229
  have htrace : WordTrace (prefixWord ++ tailWord_6015229) baseStart_6015229 baseEnd_6015229 := by
    simpa [prefixWord, tailWord_6015229, baseEnd_6015229] using wordTrace_append hprefix tailTrace_6015229
  have hstable : (prefixWord ++ tailWord_6015229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015229).length < 2 ^ (prefixWord ++ tailWord_6015229).sum := by decide
  have hdescent : baseEnd_6015229 < baseStart_6015229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015253 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 5]
def baseStart_6015253 : Nat := 118140960795 + 6015253 * 2 ^ 59
def prefixEnd_6015253 : Nat := 4983230072969 + 3 ^ 40 * 6015253 * 2
def baseEnd_6015253 : Nat := 343190671933295447630429

theorem tailTrace_6015253 : CollatzResearch.WordTrace tailWord_6015253 prefixEnd_6015253 343190671933295447630429 := by
  unfold tailWord_6015253
  simp only [CollatzResearch.WordTrace]
  refine ⟨219394300876773179268114413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146262867251182119512076275 219394300876773179268114413)
  ·
    refine ⟨82272862828789942225542905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219394300876773179268114413 82272862828789942225542905)
    ·
      refine ⟨61704647121592456669157179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82272862828789942225542905 61704647121592456669157179)
      ·
        refine ⟨92556970682388685003735769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61704647121592456669157179 92556970682388685003735769)
        ·
          refine ⟨69417728011791513752801827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92556970682388685003735769 69417728011791513752801827)
          ·
            refine ⟨104126592017687270629202741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69417728011791513752801827 104126592017687270629202741)
            ·
              refine ⟨9761868001658181621487757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104126592017687270629202741 9761868001658181621487757)
              ·
                refine ⟨3660700500621818108057909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9761868001658181621487757 3660700500621818108057909)
                ·
                  refine ⟨343190671933295447630429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3660700500621818108057909 343190671933295447630429)
                  ·
                    rfl

theorem cell23_6015253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_6015253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015253 prefixEnd_6015253 := by exact prefixLift 6015253
  have htrace : WordTrace (prefixWord ++ tailWord_6015253) baseStart_6015253 baseEnd_6015253 := by
    simpa [prefixWord, tailWord_6015253, baseEnd_6015253] using wordTrace_append hprefix tailTrace_6015253
  have hstable : (prefixWord ++ tailWord_6015253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015253).length < 2 ^ (prefixWord ++ tailWord_6015253).sum := by decide
  have hdescent : baseEnd_6015253 < baseStart_6015253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015281 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_6015281 : Nat := 118140960795 + 6015281 * 2 ^ 59
def prefixEnd_6015281 : Nat := 4983230072969 + 3 ^ 40 * 6015281 * 2
def baseEnd_6015281 : Nat := 3088730424857984919123733

theorem tailTrace_6015281 : CollatzResearch.WordTrace tailWord_6015281 prefixEnd_6015281 3088730424857984919123733 := by
  unfold tailWord_6015281
  simp only [CollatzResearch.WordTrace]
  refine ⟨219395322120671740050133697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146263548080447826700089131 219395322120671740050133697)
  ·
    refine ⟨164546491590503805037600273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219395322120671740050133697 164546491590503805037600273)
    ·
      refine ⟨123409868692877853778200205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164546491590503805037600273 123409868692877853778200205)
      ·
        refine ⟨46278700759829195166825077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123409868692877853778200205 46278700759829195166825077)
        ·
          refine ⟨4338628196233987046889851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46278700759829195166825077 4338628196233987046889851)
          ·
            refine ⟨6507942294350980570334777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338628196233987046889851 6507942294350980570334777)
            ·
              refine ⟨4880956720763235427751083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6507942294350980570334777 4880956720763235427751083)
              ·
                refine ⟨7321435081144853141626625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880956720763235427751083 7321435081144853141626625)
                ·
                  refine ⟨5491076310858639856219969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321435081144853141626625 5491076310858639856219969)
                  ·
                    refine ⟨4118307233143979892164977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491076310858639856219969 4118307233143979892164977)
                    ·
                      refine ⟨3088730424857984919123733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118307233143979892164977 3088730424857984919123733)
                      ·
                        rfl

theorem cell23_6015281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_6015281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015281 prefixEnd_6015281 := by exact prefixLift 6015281
  have htrace : WordTrace (prefixWord ++ tailWord_6015281) baseStart_6015281 baseEnd_6015281 := by
    simpa [prefixWord, tailWord_6015281, baseEnd_6015281] using wordTrace_append hprefix tailTrace_6015281
  have hstable : (prefixWord ++ tailWord_6015281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015281).length < 2 ^ (prefixWord ++ tailWord_6015281).sum := by decide
  have hdescent : baseEnd_6015281 < baseStart_6015281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015303 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_6015303 : Nat := 118140960795 + 6015303 * 2 ^ 59
def prefixEnd_6015303 : Nat := 4983230072969 + 3 ^ 40 * 6015303 * 2
def baseEnd_6015303 : Nat := 3088741721432383833048631

theorem tailTrace_6015303 : CollatzResearch.WordTrace tailWord_6015303 prefixEnd_6015303 3088741721432383833048631 := by
  unfold tailWord_6015303
  simp only [CollatzResearch.WordTrace]
  refine ⟨219396124526592037807434563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146264083017728025204956375 219396124526592037807434563)
  ·
    refine ⟨329094186789888056711151845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219396124526592037807434563 329094186789888056711151845)
    ·
      refine ⟨61705160023104010633340971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329094186789888056711151845 61705160023104010633340971)
      ·
        refine ⟨92557740034656015950011457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61705160023104010633340971 92557740034656015950011457)
        ·
          refine ⟨69418305025992011962508593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92557740034656015950011457 69418305025992011962508593)
          ·
            refine ⟨52063728769494008971881445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69418305025992011962508593 52063728769494008971881445)
            ·
              refine ⟨9761949144280126682227771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52063728769494008971881445 9761949144280126682227771)
              ·
                refine ⟨14642923716420190023341657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761949144280126682227771 14642923716420190023341657)
                ·
                  refine ⟨10982192787315142517506243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14642923716420190023341657 10982192787315142517506243)
                  ·
                    refine ⟨16473289180972713776259365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10982192787315142517506243 16473289180972713776259365)
                    ·
                      refine ⟨3088741721432383833048631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16473289180972713776259365 3088741721432383833048631)
                      ·
                        rfl

theorem cell23_6015303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_6015303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015303 prefixEnd_6015303 := by exact prefixLift 6015303
  have htrace : WordTrace (prefixWord ++ tailWord_6015303) baseStart_6015303 baseEnd_6015303 := by
    simpa [prefixWord, tailWord_6015303, baseEnd_6015303] using wordTrace_append hprefix tailTrace_6015303
  have hstable : (prefixWord ++ tailWord_6015303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015303).length < 2 ^ (prefixWord ++ tailWord_6015303).sum := by decide
  have hdescent : baseEnd_6015303 < baseStart_6015303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015410 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_6015410 : Nat := 118140960795 + 6015410 * 2 ^ 59
def prefixEnd_6015410 : Nat := 4983230072969 + 3 ^ 40 * 6015410 * 2
def baseEnd_6015410 : Nat := 3088796663862414914410639

theorem tailTrace_6015410 : CollatzResearch.WordTrace tailWord_6015410 prefixEnd_6015410 3088796663862414914410639 := by
  unfold tailWord_6015410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54850006784301098770394921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146266684758136263387719789 54850006784301098770394921)
  ·
    refine ⟨41137505088225824077796191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54850006784301098770394921 41137505088225824077796191)
    ·
      refine ⟨61706257632338736116694287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41137505088225824077796191 61706257632338736116694287)
      ·
        refine ⟨92559386448508104175041431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61706257632338736116694287 92559386448508104175041431)
        ·
          refine ⟨138839079672762156262562147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92559386448508104175041431 138839079672762156262562147)
          ·
            refine ⟨208258619509143234393843221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138839079672762156262562147 208258619509143234393843221)
            ·
              refine ⟨9762122789491089112211401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208258619509143234393843221 9762122789491089112211401)
              ·
                refine ⟨7321592092118316834158551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9762122789491089112211401 7321592092118316834158551)
                ·
                  refine ⟨10982388138177475251237827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321592092118316834158551 10982388138177475251237827)
                  ·
                    refine ⟨16473582207266212876856741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10982388138177475251237827 16473582207266212876856741)
                    ·
                      refine ⟨3088796663862414914410639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16473582207266212876856741 3088796663862414914410639)
                      ·
                        rfl

theorem cell23_6015410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_6015410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015410 prefixEnd_6015410 := by exact prefixLift 6015410
  have htrace : WordTrace (prefixWord ++ tailWord_6015410) baseStart_6015410 baseEnd_6015410 := by
    simpa [prefixWord, tailWord_6015410, baseEnd_6015410] using wordTrace_append hprefix tailTrace_6015410
  have hstable : (prefixWord ++ tailWord_6015410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015410).length < 2 ^ (prefixWord ++ tailWord_6015410).sum := by decide
  have hdescent : baseEnd_6015410 < baseStart_6015410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015420 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_6015420 : Nat := 118140960795 + 6015420 * 2 ^ 59
def prefixEnd_6015420 : Nat := 4983230072969 + 3 ^ 40 * 6015420 * 2
def baseEnd_6015420 : Nat := 1029600599556319958428531

theorem tailTrace_6015420 : CollatzResearch.WordTrace tailWord_6015420 prefixEnd_6015420 1029600599556319958428531 := by
  unfold tailWord_6015420
  simp only [CollatzResearch.WordTrace]
  refine ⟨109700195933584083394721857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146266927911445444526295809 109700195933584083394721857)
  ·
    refine ⟨82275146950188062546041393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109700195933584083394721857 82275146950188062546041393)
    ·
      refine ⟨61706360212641046909531045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82275146950188062546041393 61706360212641046909531045)
      ·
        refine ⟨11569942539870196295537071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61706360212641046909531045 11569942539870196295537071)
        ·
          refine ⟨17354913809805294443305607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11569942539870196295537071 17354913809805294443305607)
          ·
            refine ⟨26032370714707941664958411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17354913809805294443305607 26032370714707941664958411)
            ·
              refine ⟨39048556072061912497437617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26032370714707941664958411 39048556072061912497437617)
              ·
                refine ⟨29286417054046434373078213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39048556072061912497437617 29286417054046434373078213)
                ·
                  refine ⟨5491203197633706444952165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29286417054046434373078213 5491203197633706444952165)
                  ·
                    refine ⟨1029600599556319958428531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491203197633706444952165 1029600599556319958428531)
                    ·
                      rfl

theorem cell23_6015420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_6015420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015420 prefixEnd_6015420 := by exact prefixLift 6015420
  have htrace : WordTrace (prefixWord ++ tailWord_6015420) baseStart_6015420 baseEnd_6015420 := by
    simpa [prefixWord, tailWord_6015420, baseEnd_6015420] using wordTrace_append hprefix tailTrace_6015420
  have hstable : (prefixWord ++ tailWord_6015420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015420).length < 2 ^ (prefixWord ++ tailWord_6015420).sum := by decide
  have hdescent : baseEnd_6015420 < baseStart_6015420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015444 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6015444 : Nat := 118140960795 + 6015444 * 2 ^ 59
def prefixEnd_6015444 : Nat := 4983230072969 + 3 ^ 40 * 6015444 * 2
def baseEnd_6015444 : Nat := 3088814122204667781385483

theorem tailTrace_6015444 : CollatzResearch.WordTrace tailWord_6015444 prefixEnd_6015444 3088814122204667781385483 := by
  unfold tailWord_6015444
  simp only [CollatzResearch.WordTrace]
  refine ⟨109700633609540609444158693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146267511479387479258878257 109700633609540609444158693)
  ·
    refine ⟨20568868801788864270779755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109700633609540609444158693 20568868801788864270779755)
    ·
      refine ⟨30853303202683296406169633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20568868801788864270779755 30853303202683296406169633)
      ·
        refine ⟨23139977402012472304627225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30853303202683296406169633 23139977402012472304627225)
        ·
          refine ⟨17354983051509354228470419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23139977402012472304627225 17354983051509354228470419)
          ·
            refine ⟨26032474577264031342705629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17354983051509354228470419 26032474577264031342705629)
            ·
              refine ⟨9762177966474011753514611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26032474577264031342705629 9762177966474011753514611)
              ·
                refine ⟨14643266949711017630271917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9762177966474011753514611 14643266949711017630271917)
                ·
                  refine ⟨5491225106141631611351969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14643266949711017630271917 5491225106141631611351969)
                  ·
                    refine ⟨4118418829606223708513977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491225106141631611351969 4118418829606223708513977)
                    ·
                      refine ⟨3088814122204667781385483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118418829606223708513977 3088814122204667781385483)
                      ·
                        rfl

theorem cell23_6015444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6015444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015444 prefixEnd_6015444 := by exact prefixLift 6015444
  have htrace : WordTrace (prefixWord ++ tailWord_6015444) baseStart_6015444 baseEnd_6015444 := by
    simpa [prefixWord, tailWord_6015444, baseEnd_6015444] using wordTrace_append hprefix tailTrace_6015444
  have hstable : (prefixWord ++ tailWord_6015444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015444).length < 2 ^ (prefixWord ++ tailWord_6015444).sum := by decide
  have hdescent : baseEnd_6015444 < baseStart_6015444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
