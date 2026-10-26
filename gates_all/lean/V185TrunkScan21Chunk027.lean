import V185TrunkScan21Chunk026

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_325693 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 3]
def baseStart_325693 : Nat := 118140960795 + 325693 * 2 ^ 59
def prefixEnd_325693 : Nat := 4983230072969 + 3 ^ 40 * 325693 * 2
def baseEnd_325693 : Nat := 74327579913288648150965

theorem tailTrace_325693 : CollatzResearch.WordTrace tailWord_325693 prefixEnd_325693 74327579913288648150965 := by
  unfold tailWord_325693
  simp only [CollatzResearch.WordTrace]
  refine ⟨11878999609077359781061733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7919333072718239854041155 11878999609077359781061733)
  ·
    refine ⟨2227312426702004958949075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11878999609077359781061733 2227312426702004958949075)
    ·
      refine ⟨3340968640053007438423613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227312426702004958949075 3340968640053007438423613)
      ·
        refine ⟨1252863240019877789408855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3340968640053007438423613 1252863240019877789408855)
        ·
          refine ⟨1879294860029816684113283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252863240019877789408855 1879294860029816684113283)
          ·
            refine ⟨2818942290044725026169925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879294860029816684113283 2818942290044725026169925)
            ·
              refine ⟨528551679383385942406861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2818942290044725026169925 528551679383385942406861)
              ·
                refine ⟨198206879768769728402573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528551679383385942406861 198206879768769728402573)
                ·
                  refine ⟨74327579913288648150965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198206879768769728402573 74327579913288648150965)
                  ·
                    rfl

theorem cell21_325693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_325693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325693 prefixEnd_325693 := by exact prefixLift 325693
  have htrace : WordTrace (prefixWord ++ tailWord_325693) baseStart_325693 baseEnd_325693 := by
    simpa [prefixWord, tailWord_325693, baseEnd_325693] using wordTrace_append hprefix tailTrace_325693
  have hstable : (prefixWord ++ tailWord_325693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325693).length < 2 ^ (prefixWord ++ tailWord_325693).sum := by decide
  have hdescent : baseEnd_325693 < baseStart_325693 := by decide
  rcases family_descends (prefixWord ++ tailWord_325693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325724 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_325724 : Nat := 118140960795 + 325724 * 2 ^ 59
def prefixEnd_325724 : Nat := 4983230072969 + 3 ^ 40 * 325724 * 2
def baseEnd_325724 : Nat := 74334654535639483134235

theorem tailTrace_325724 : CollatzResearch.WordTrace tailWord_325724 prefixEnd_325724 74334654535639483134235 := by
  unfold tailWord_325724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940065135982526037720113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7920086847976701383626817 5940065135982526037720113)
  ·
    refine ⟨4455048851986894528290085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5940065135982526037720113 4455048851986894528290085)
    ·
      refine ⟨835321659747542724054391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4455048851986894528290085 835321659747542724054391)
      ·
        refine ⟨1252982489621314086081587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835321659747542724054391 1252982489621314086081587)
        ·
          refine ⟨1879473734431971129122381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252982489621314086081587 1879473734431971129122381)
          ·
            refine ⟨704802650411989173420893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1879473734431971129122381 704802650411989173420893)
            ·
              refine ⟨264300993904495940032835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704802650411989173420893 264300993904495940032835)
              ·
                refine ⟨396451490856743910049253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264300993904495940032835 396451490856743910049253)
                ·
                  refine ⟨74334654535639483134235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396451490856743910049253 74334654535639483134235)
                  ·
                    rfl

theorem cell21_325724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_325724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325724 prefixEnd_325724 := by exact prefixLift 325724
  have htrace : WordTrace (prefixWord ++ tailWord_325724) baseStart_325724 baseEnd_325724 := by
    simpa [prefixWord, tailWord_325724, baseEnd_325724] using wordTrace_append hprefix tailTrace_325724
  have hstable : (prefixWord ++ tailWord_325724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325724).length < 2 ^ (prefixWord ++ tailWord_325724).sum := by decide
  have hdescent : baseEnd_325724 < baseStart_325724 := by decide
  rcases family_descends (prefixWord ++ tailWord_325724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325735 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_325735 : Nat := 118140960795 + 325735 * 2 ^ 59
def prefixEnd_325735 : Nat := 4983230072969 + 3 ^ 40 * 325735 * 2
def baseEnd_325735 : Nat := 74337164885505908450879

theorem tailTrace_325735 : CollatzResearch.WordTrace tailWord_325735 prefixEnd_325735 74337164885505908450879 := by
  unfold tailWord_325735
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880531474925200954090659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7920354316616800636060439 11880531474925200954090659)
  ·
    refine ⟨17820797212387801431135989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11880531474925200954090659 17820797212387801431135989)
    ·
      refine ⟨1670699738661356384168999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17820797212387801431135989 1670699738661356384168999)
      ·
        refine ⟨2506049607992034576253499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670699738661356384168999 2506049607992034576253499)
        ·
          refine ⟨3759074411988051864380249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2506049607992034576253499 3759074411988051864380249)
          ·
            refine ⟨2819305808991038898285187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759074411988051864380249 2819305808991038898285187)
            ·
              refine ⟨4228958713486558347427781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819305808991038898285187 4228958713486558347427781)
              ·
                refine ⟨792929758778729690142709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4228958713486558347427781 792929758778729690142709)
                ·
                  refine ⟨74337164885505908450879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 792929758778729690142709 74337164885505908450879)
                  ·
                    rfl

theorem cell21_325735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_325735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325735 prefixEnd_325735 := by exact prefixLift 325735
  have htrace : WordTrace (prefixWord ++ tailWord_325735) baseStart_325735 baseEnd_325735 := by
    simpa [prefixWord, tailWord_325735, baseEnd_325735] using wordTrace_append hprefix tailTrace_325735
  have hstable : (prefixWord ++ tailWord_325735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325735).length < 2 ^ (prefixWord ++ tailWord_325735).sum := by decide
  have hdescent : baseEnd_325735 < baseStart_325735 := by decide
  rcases family_descends (prefixWord ++ tailWord_325735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325769 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 3]
def baseStart_325769 : Nat := 118140960795 + 325769 * 2 ^ 59
def prefixEnd_325769 : Nat := 4983230072969 + 3 ^ 40 * 325769 * 2
def baseEnd_325769 : Nat := 74344924148729404884143

theorem tailTrace_325769 : CollatzResearch.WordTrace tailWord_325769 prefixEnd_325769 74344924148729404884143 := by
  unfold tailWord_325769
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881771556802024760828361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7921181037868016507218907 11881771556802024760828361)
  ·
    refine ⟨8911328667601518570621271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11881771556802024760828361 8911328667601518570621271)
    ·
      refine ⟨13366993001402277855931907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8911328667601518570621271 13366993001402277855931907)
      ·
        refine ⟨20050489502103416783897861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13366993001402277855931907 20050489502103416783897861)
        ·
          refine ⟨3759466781644390646980849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20050489502103416783897861 3759466781644390646980849)
          ·
            refine ⟨2819600086233292985235637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759466781644390646980849 2819600086233292985235637)
            ·
              refine ⟨264337508084371217365841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2819600086233292985235637 264337508084371217365841)
              ·
                refine ⟨198253131063278413024381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264337508084371217365841 198253131063278413024381)
                ·
                  refine ⟨74344924148729404884143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198253131063278413024381 74344924148729404884143)
                  ·
                    rfl

theorem cell21_325769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_325769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325769 prefixEnd_325769 := by exact prefixLift 325769
  have htrace : WordTrace (prefixWord ++ tailWord_325769) baseStart_325769 baseEnd_325769 := by
    simpa [prefixWord, tailWord_325769, baseEnd_325769] using wordTrace_append hprefix tailTrace_325769
  have hstable : (prefixWord ++ tailWord_325769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325769).length < 2 ^ (prefixWord ++ tailWord_325769).sum := by decide
  have hdescent : baseEnd_325769 < baseStart_325769 := by decide
  rcases family_descends (prefixWord ++ tailWord_325769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325783 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_325783 : Nat := 118140960795 + 325783 * 2 ^ 59
def prefixEnd_325783 : Nat := 4983230072969 + 3 ^ 40 * 325783 * 2
def baseEnd_325783 : Nat := 74348119139468491650781

theorem tailTrace_325783 : CollatzResearch.WordTrace tailWord_325783 prefixEnd_325783 74348119139468491650781 := by
  unfold tailWord_325783
  simp only [CollatzResearch.WordTrace]
  refine ⟨11882282178751305151838003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7921521452500870101225335 11882282178751305151838003)
  ·
    refine ⟨17823423268126957727757005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11882282178751305151838003 17823423268126957727757005)
    ·
      refine ⟨6683783725547609147908877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17823423268126957727757005 6683783725547609147908877)
      ·
        refine ⟨2506418897080353430465829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6683783725547609147908877 2506418897080353430465829)
        ·
          refine ⟨469953543202566268212343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2506418897080353430465829 469953543202566268212343)
          ·
            refine ⟨704930314803849402318515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469953543202566268212343 704930314803849402318515)
            ·
              refine ⟨1057395472205774103477773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704930314803849402318515 1057395472205774103477773)
              ·
                refine ⟨396523302077165288804165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057395472205774103477773 396523302077165288804165)
                ·
                  refine ⟨74348119139468491650781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396523302077165288804165 74348119139468491650781)
                  ·
                    rfl

theorem cell21_325783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_325783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325783 prefixEnd_325783 := by exact prefixLift 325783
  have htrace : WordTrace (prefixWord ++ tailWord_325783) baseStart_325783 baseEnd_325783 := by
    simpa [prefixWord, tailWord_325783, baseEnd_325783] using wordTrace_append hprefix tailTrace_325783
  have hstable : (prefixWord ++ tailWord_325783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325783).length < 2 ^ (prefixWord ++ tailWord_325783).sum := by decide
  have hdescent : baseEnd_325783 < baseStart_325783 := by decide
  rcases family_descends (prefixWord ++ tailWord_325783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325887 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_325887 : Nat := 118140960795 + 325887 * 2 ^ 59
def prefixEnd_325887 : Nat := 4983230072969 + 3 ^ 40 * 325887 * 2
def baseEnd_325887 : Nat := 74371853356387421917235

theorem tailTrace_325887 : CollatzResearch.WordTrace tailWord_325887 prefixEnd_325887 74371853356387421917235 := by
  unfold tailWord_325887
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886075370374530913623915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7924050246916353942415943 11886075370374530913623915)
  ·
    refine ⟨17829113055561796370435873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11886075370374530913623915 17829113055561796370435873)
    ·
      refine ⟨13371834791671347277826905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17829113055561796370435873 13371834791671347277826905)
      ·
        refine ⟨10028876093753510458370179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13371834791671347277826905 10028876093753510458370179)
        ·
          refine ⟨15043314140630265687555269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10028876093753510458370179 15043314140630265687555269)
          ·
            refine ⟨2820621401368174816416613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15043314140630265687555269 2820621401368174816416613)
            ·
              refine ⟨528866512756532778078115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2820621401368174816416613 528866512756532778078115)
              ·
                refine ⟨793299769134799167117173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528866512756532778078115 793299769134799167117173)
                ·
                  refine ⟨74371853356387421917235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793299769134799167117173 74371853356387421917235)
                  ·
                    rfl

theorem cell21_325887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_325887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325887 prefixEnd_325887 := by exact prefixLift 325887
  have htrace : WordTrace (prefixWord ++ tailWord_325887) baseStart_325887 baseEnd_325887 := by
    simpa [prefixWord, tailWord_325887, baseEnd_325887] using wordTrace_append hprefix tailTrace_325887
  have hstable : (prefixWord ++ tailWord_325887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325887).length < 2 ^ (prefixWord ++ tailWord_325887).sum := by decide
  have hdescent : baseEnd_325887 < baseStart_325887 := by decide
  rcases family_descends (prefixWord ++ tailWord_325887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325938 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_325938 : Nat := 118140960795 + 325938 * 2 ^ 59
def prefixEnd_325938 : Nat := 4983230072969 + 3 ^ 40 * 325938 * 2
def baseEnd_325938 : Nat := 74383492251222666567131

theorem tailTrace_325938 : CollatzResearch.WordTrace tailWord_325938 prefixEnd_325938 74383492251222666567131 := by
  unfold tailWord_325938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971983873297441655932617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7925290328793177749153645 2971983873297441655932617)
  ·
    refine ⟨2228987904973081241949463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2971983873297441655932617 2228987904973081241949463)
    ·
      refine ⟨3343481857459621862924195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228987904973081241949463 3343481857459621862924195)
      ·
        refine ⟨5015222786189432794386293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343481857459621862924195 5015222786189432794386293)
        ·
          refine ⟨470177136205259324473715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5015222786189432794386293 470177136205259324473715)
          ·
            refine ⟨705265704307888986710573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470177136205259324473715 705265704307888986710573)
            ·
              refine ⟨264474639115458370016465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705265704307888986710573 264474639115458370016465)
              ·
                refine ⟨198355979336593777512349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264474639115458370016465 198355979336593777512349)
                ·
                  refine ⟨74383492251222666567131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198355979336593777512349 74383492251222666567131)
                  ·
                    rfl

theorem cell21_325938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_325938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325938 prefixEnd_325938 := by exact prefixLift 325938
  have htrace : WordTrace (prefixWord ++ tailWord_325938) baseStart_325938 baseEnd_325938 := by
    simpa [prefixWord, tailWord_325938, baseEnd_325938] using wordTrace_append hprefix tailTrace_325938
  have hstable : (prefixWord ++ tailWord_325938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325938).length < 2 ^ (prefixWord ++ tailWord_325938).sum := by decide
  have hdescent : baseEnd_325938 < baseStart_325938 := by decide
  rcases family_descends (prefixWord ++ tailWord_325938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326025 : List Nat := [1, 2, 1, 1, 6, 2, 3, 5]
def baseStart_326025 : Nat := 118140960795 + 326025 * 2 ^ 59
def prefixEnd_326025 : Nat := 4983230072969 + 3 ^ 40 * 326025 * 2
def baseEnd_326025 : Nat := 24801115612176616205651

theorem tailTrace_326025 : CollatzResearch.WordTrace tailWord_326025 prefixEnd_326025 24801115612176616205651 := by
  unfold tailWord_326025
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891108643874580482147529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7927405762583053654765019 11891108643874580482147529)
  ·
    refine ⟨8918331482905935361610647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11891108643874580482147529 8918331482905935361610647)
    ·
      refine ⟨13377497224358903042415971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918331482905935361610647 13377497224358903042415971)
      ·
        refine ⟨20066245836538354563623957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13377497224358903042415971 20066245836538354563623957)
        ·
          refine ⟨940605273587735370169873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20066245836538354563623957 940605273587735370169873)
          ·
            refine ⟨705453955190801527627405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940605273587735370169873 705453955190801527627405)
            ·
              refine ⟨264545233196550572860277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705453955190801527627405 264545233196550572860277)
              ·
                refine ⟨24801115612176616205651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264545233196550572860277 24801115612176616205651)
                ·
                  rfl

theorem cell21_326025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 5].length) (baseStart_326025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326025 prefixEnd_326025 := by exact prefixLift 326025
  have htrace : WordTrace (prefixWord ++ tailWord_326025) baseStart_326025 baseEnd_326025 := by
    simpa [prefixWord, tailWord_326025, baseEnd_326025] using wordTrace_append hprefix tailTrace_326025
  have hstable : (prefixWord ++ tailWord_326025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326025).length < 2 ^ (prefixWord ++ tailWord_326025).sum := by decide
  have hdescent : baseEnd_326025 < baseStart_326025 := by decide
  rcases family_descends (prefixWord ++ tailWord_326025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326053 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_326053 : Nat := 118140960795 + 326053 * 2 ^ 59
def prefixEnd_326053 : Nat := 4983230072969 + 3 ^ 40 * 326053 * 2
def baseEnd_326053 : Nat := 74409736818008022150229

theorem tailTrace_326053 : CollatzResearch.WordTrace tailWord_326053 prefixEnd_326053 74409736818008022150229 := by
  unfold tailWord_326053
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892129887773141264166813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7928086591848760842777875 11892129887773141264166813)
  ·
    refine ⟨4459548707914927974062555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11892129887773141264166813 4459548707914927974062555)
    ·
      refine ⟨6689323061872391961093833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459548707914927974062555 6689323061872391961093833)
      ·
        refine ⟨5016992296404293970820375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6689323061872391961093833 5016992296404293970820375)
        ·
          refine ⟨7525488444606440956230563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016992296404293970820375 7525488444606440956230563)
          ·
            refine ⟨11288232666909661434345845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7525488444606440956230563 11288232666909661434345845)
            ·
              refine ⟨1058271812522780759469923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11288232666909661434345845 1058271812522780759469923)
              ·
                refine ⟨1587407718784171139204885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058271812522780759469923 1587407718784171139204885)
                ·
                  refine ⟨74409736818008022150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1587407718784171139204885 74409736818008022150229)
                  ·
                    rfl

theorem cell21_326053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_326053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326053 prefixEnd_326053 := by exact prefixLift 326053
  have htrace : WordTrace (prefixWord ++ tailWord_326053) baseStart_326053 baseEnd_326053 := by
    simpa [prefixWord, tailWord_326053, baseEnd_326053] using wordTrace_append hprefix tailTrace_326053
  have hstable : (prefixWord ++ tailWord_326053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326053).length < 2 ^ (prefixWord ++ tailWord_326053).sum := by decide
  have hdescent : baseEnd_326053 < baseStart_326053 := by decide
  rcases family_descends (prefixWord ++ tailWord_326053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326056 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_326056 : Nat := 118140960795 + 326056 * 2 ^ 59
def prefixEnd_326056 : Nat := 4983230072969 + 3 ^ 40 * 326056 * 2
def baseEnd_326056 : Nat := 74410421458880683600223

theorem tailTrace_326056 : CollatzResearch.WordTrace tailWord_326056 prefixEnd_326056 74410421458880683600223 := by
  unfold tailWord_326056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946119653381136388263011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7928159537841515184350681 5946119653381136388263011)
  ·
    refine ⟨8919179480071704582394517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5946119653381136388263011 8919179480071704582394517)
    ·
      refine ⟨418086538128361152299743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8919179480071704582394517 418086538128361152299743)
      ·
        refine ⟨627129807192541728449615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418086538128361152299743 627129807192541728449615)
        ·
          refine ⟨940694710788812592674423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627129807192541728449615 940694710788812592674423)
          ·
            refine ⟨1411042066183218889011635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940694710788812592674423 1411042066183218889011635)
            ·
              refine ⟨2116563099274828333517453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411042066183218889011635 2116563099274828333517453)
              ·
                refine ⟨793711162228060625069045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2116563099274828333517453 793711162228060625069045)
                ·
                  refine ⟨74410421458880683600223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793711162228060625069045 74410421458880683600223)
                  ·
                    rfl

theorem cell21_326056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_326056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326056 prefixEnd_326056 := by exact prefixLift 326056
  have htrace : WordTrace (prefixWord ++ tailWord_326056) baseStart_326056 baseEnd_326056 := by
    simpa [prefixWord, tailWord_326056, baseEnd_326056] using wordTrace_append hprefix tailTrace_326056
  have hstable : (prefixWord ++ tailWord_326056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326056).length < 2 ^ (prefixWord ++ tailWord_326056).sum := by decide
  have hdescent : baseEnd_326056 < baseStart_326056 := by decide
  rcases family_descends (prefixWord ++ tailWord_326056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326143 : List Nat := [1, 1, 2, 2, 1, 2, 3, 9]
def baseStart_326143 : Nat := 118140960795 + 326143 * 2 ^ 59
def prefixEnd_326143 : Nat := 4983230072969 + 3 ^ 40 * 326143 * 2
def baseEnd_326143 : Nat := 24810092014729288550015

theorem tailTrace_326143 : CollatzResearch.WordTrace tailWord_326143 prefixEnd_326143 24810092014729288550015 := by
  unfold tailWord_326143
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895412457447086634943083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7930274971631391089962055 11895412457447086634943083)
  ·
    refine ⟨17843118686170629952414625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11895412457447086634943083 17843118686170629952414625)
    ·
      refine ⟨13382339014627972464310969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17843118686170629952414625 13382339014627972464310969)
      ·
        refine ⟨10036754260970979348233227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13382339014627972464310969 10036754260970979348233227)
        ·
          refine ⟨15055131391456469022349841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036754260970979348233227 15055131391456469022349841)
          ·
            refine ⟨11291348543592351766762381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15055131391456469022349841 11291348543592351766762381)
            ·
              refine ⟨4234255703847131912535893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11291348543592351766762381 4234255703847131912535893)
              ·
                refine ⟨24810092014729288550015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4234255703847131912535893 24810092014729288550015)
                ·
                  rfl

theorem cell21_326143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_326143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326143 prefixEnd_326143 := by exact prefixLift 326143
  have htrace : WordTrace (prefixWord ++ tailWord_326143) baseStart_326143 baseEnd_326143 := by
    simpa [prefixWord, tailWord_326143, baseEnd_326143] using wordTrace_append hprefix tailTrace_326143
  have hstable : (prefixWord ++ tailWord_326143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326143).length < 2 ^ (prefixWord ++ tailWord_326143).sum := by decide
  have hdescent : baseEnd_326143 < baseStart_326143 := by decide
  rcases family_descends (prefixWord ++ tailWord_326143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326222 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_326222 : Nat := 118140960795 + 326222 * 2 ^ 59
def prefixEnd_326222 : Nat := 4983230072969 + 3 ^ 40 * 326222 * 2
def baseEnd_326222 : Nat := 74448304920501283833217

theorem tailTrace_326222 : CollatzResearch.WordTrace tailWord_326222 prefixEnd_326222 74448304920501283833217 := by
  unfold tailWord_326222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487286728020110390883615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7932195882773922084712613 1487286728020110390883615)
  ·
    refine ⟨2230930092030165586325423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487286728020110390883615 2230930092030165586325423)
    ·
      refine ⟨3346395138045248379488135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230930092030165586325423 3346395138045248379488135)
      ·
        refine ⟨5019592707067872569232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346395138045248379488135 5019592707067872569232203)
        ·
          refine ⟨7529389060601808853848305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019592707067872569232203 7529389060601808853848305)
          ·
            refine ⟨5647041795451356640386229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7529389060601808853848305 5647041795451356640386229)
            ·
              refine ⟨529410168323564685036209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5647041795451356640386229 529410168323564685036209)
              ·
                refine ⟨397057626242673513777157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529410168323564685036209 397057626242673513777157)
                ·
                  refine ⟨74448304920501283833217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397057626242673513777157 74448304920501283833217)
                  ·
                    rfl

theorem cell21_326222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_326222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326222 prefixEnd_326222 := by exact prefixLift 326222
  have htrace : WordTrace (prefixWord ++ tailWord_326222) baseStart_326222 baseEnd_326222 := by
    simpa [prefixWord, tailWord_326222, baseEnd_326222] using wordTrace_append hprefix tailTrace_326222
  have hstable : (prefixWord ++ tailWord_326222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326222).length < 2 ^ (prefixWord ++ tailWord_326222).sum := by decide
  have hdescent : baseEnd_326222 < baseStart_326222 := by decide
  rcases family_descends (prefixWord ++ tailWord_326222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326253 : List Nat := [1, 5, 1, 1, 3, 1, 4, 5]
def baseStart_326253 : Nat := 118140960795 + 326253 * 2 ^ 59
def prefixEnd_326253 : Nat := 4983230072969 + 3 ^ 40 * 326253 * 2
def baseEnd_326253 : Nat := 24818459847617372938829

theorem tailTrace_326253 : CollatzResearch.WordTrace tailWord_326253 prefixEnd_326253 24818459847617372938829 := by
  unfold tailWord_326253
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899424487048575421447413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7932949658032383614298275 11899424487048575421447413)
  ·
    refine ⟨1115571045660803945760695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11899424487048575421447413 1115571045660803945760695)
    ·
      refine ⟨1673356568491205918641043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115571045660803945760695 1673356568491205918641043)
      ·
        refine ⟨2510034852736808877961565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673356568491205918641043 2510034852736808877961565)
        ·
          refine ⟨941263069776303329235587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2510034852736808877961565 941263069776303329235587)
          ·
            refine ⟨1411894604664454993853381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941263069776303329235587 1411894604664454993853381)
            ·
              refine ⟨264730238374585311347509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1411894604664454993853381 264730238374585311347509)
              ·
                refine ⟨24818459847617372938829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264730238374585311347509 24818459847617372938829)
                ·
                  rfl

theorem cell21_326253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 5].length) (baseStart_326253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326253 prefixEnd_326253 := by exact prefixLift 326253
  have htrace : WordTrace (prefixWord ++ tailWord_326253) baseStart_326253 baseEnd_326253 := by
    simpa [prefixWord, tailWord_326253, baseEnd_326253] using wordTrace_append hprefix tailTrace_326253
  have hstable : (prefixWord ++ tailWord_326253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326253).length < 2 ^ (prefixWord ++ tailWord_326253).sum := by decide
  have hdescent : baseEnd_326253 < baseStart_326253 := by decide
  rcases family_descends (prefixWord ++ tailWord_326253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326267 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 3]
def baseStart_326267 : Nat := 118140960795 + 326267 * 2 ^ 59
def prefixEnd_326267 : Nat := 4983230072969 + 3 ^ 40 * 326267 * 2
def baseEnd_326267 : Nat := 74458574533591205583125

theorem tailTrace_326267 : CollatzResearch.WordTrace tailWord_326267 prefixEnd_326267 74458574533591205583125 := by
  unfold tailWord_326267
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899935108997855812457055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7933290072665237208304703 11899935108997855812457055)
  ·
    refine ⟨17849902663496783718685583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899935108997855812457055 17849902663496783718685583)
    ·
      refine ⟨26774853995245175578028375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17849902663496783718685583 26774853995245175578028375)
      ·
        refine ⟨40162280992867763367042563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26774853995245175578028375 40162280992867763367042563)
        ·
          refine ⟨60243421489301645050563845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40162280992867763367042563 60243421489301645050563845)
          ·
            refine ⟨11295641529244058446980721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60243421489301645050563845 11295641529244058446980721)
            ·
              refine ⟨8471731146933043835235541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11295641529244058446980721 8471731146933043835235541)
              ·
                refine ⟨198556198756243214888333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8471731146933043835235541 198556198756243214888333)
                ·
                  refine ⟨74458574533591205583125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198556198756243214888333 74458574533591205583125)
                  ·
                    rfl

theorem cell21_326267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 3].length) (baseStart_326267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326267 prefixEnd_326267 := by exact prefixLift 326267
  have htrace : WordTrace (prefixWord ++ tailWord_326267) baseStart_326267 baseEnd_326267 := by
    simpa [prefixWord, tailWord_326267, baseEnd_326267] using wordTrace_append hprefix tailTrace_326267
  have hstable : (prefixWord ++ tailWord_326267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326267).length < 2 ^ (prefixWord ++ tailWord_326267).sum := by decide
  have hdescent : baseEnd_326267 < baseStart_326267 := by decide
  rcases family_descends (prefixWord ++ tailWord_326267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326281 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_326281 : Nat := 118140960795 + 326281 * 2 ^ 59
def prefixEnd_326281 : Nat := 4983230072969 + 3 ^ 40 * 326281 * 2
def baseEnd_326281 : Nat := 74461769524330292349763

theorem tailTrace_326281 : CollatzResearch.WordTrace tailWord_326281 prefixEnd_326281 74461769524330292349763 := by
  unfold tailWord_326281
  simp only [CollatzResearch.WordTrace]
  refine ⟨11900445730947136203466697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7933630487298090802311131 11900445730947136203466697)
  ·
    refine ⟨8925334298210352152600023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11900445730947136203466697 8925334298210352152600023)
    ·
      refine ⟨13388001447315528228900035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8925334298210352152600023 13388001447315528228900035)
      ·
        refine ⟨20082002170973292343350053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13388001447315528228900035 20082002170973292343350053)
        ·
          refine ⟨3765375407057492314378135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20082002170973292343350053 3765375407057492314378135)
          ·
            refine ⟨5648063110586238471567203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765375407057492314378135 5648063110586238471567203)
            ·
              refine ⟨8472094665879357707350805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648063110586238471567203 8472094665879357707350805)
              ·
                refine ⟨397129437463094892532069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8472094665879357707350805 397129437463094892532069)
                ·
                  refine ⟨74461769524330292349763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397129437463094892532069 74461769524330292349763)
                  ·
                    rfl

theorem cell21_326281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_326281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326281 prefixEnd_326281 := by exact prefixLift 326281
  have htrace : WordTrace (prefixWord ++ tailWord_326281) baseStart_326281 baseEnd_326281 := by
    simpa [prefixWord, tailWord_326281, baseEnd_326281] using wordTrace_append hprefix tailTrace_326281
  have hstable : (prefixWord ++ tailWord_326281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326281).length < 2 ^ (prefixWord ++ tailWord_326281).sum := by decide
  have hdescent : baseEnd_326281 < baseStart_326281 := by decide
  rcases family_descends (prefixWord ++ tailWord_326281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326453 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 3]
def baseStart_326453 : Nat := 118140960795 + 326453 * 2 ^ 59
def prefixEnd_326453 : Nat := 4983230072969 + 3 ^ 40 * 326453 * 2
def baseEnd_326453 : Nat := 74501022267696215482745

theorem tailTrace_326453 : CollatzResearch.WordTrace tailWord_326453 prefixEnd_326453 74501022267696215482745 := by
  unfold tailWord_326453
  simp only [CollatzResearch.WordTrace]
  refine ⟨11906719086324009578728013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7937812724216006385818675 11906719086324009578728013)
  ·
    refine ⟨4465019657371503592023005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11906719086324009578728013 4465019657371503592023005)
    ·
      refine ⟨1674382371514313847008627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4465019657371503592023005 1674382371514313847008627)
      ·
        refine ⟨2511573557271470770512941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674382371514313847008627 2511573557271470770512941)
        ·
          refine ⟨941840083976801538942353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2511573557271470770512941 941840083976801538942353)
          ·
            refine ⟨706380062982601154206765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941840083976801538942353 706380062982601154206765)
            ·
              refine ⟨264892523618475432827537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706380062982601154206765 264892523618475432827537)
              ·
                refine ⟨198669392713856574620653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264892523618475432827537 198669392713856574620653)
                ·
                  refine ⟨74501022267696215482745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198669392713856574620653 74501022267696215482745)
                  ·
                    rfl

theorem cell21_326453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_326453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326453 prefixEnd_326453 := by exact prefixLift 326453
  have htrace : WordTrace (prefixWord ++ tailWord_326453) baseStart_326453 baseEnd_326453 := by
    simpa [prefixWord, tailWord_326453, baseEnd_326453] using wordTrace_append hprefix tailTrace_326453
  have hstable : (prefixWord ++ tailWord_326453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326453).length < 2 ^ (prefixWord ++ tailWord_326453).sum := by decide
  have hdescent : baseEnd_326453 < baseStart_326453 := by decide
  rcases family_descends (prefixWord ++ tailWord_326453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326478 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_326478 : Nat := 118140960795 + 326478 * 2 ^ 59
def prefixEnd_326478 : Nat := 4983230072969 + 3 ^ 40 * 326478 * 2
def baseEnd_326478 : Nat := 74506727608301727566027

theorem tailTrace_326478 : CollatzResearch.WordTrace tailWord_326478 prefixEnd_326478 74506727608301727566027 := by
  unfold tailWord_326478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488453863904179856048511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7938420607488959232258725 1488453863904179856048511)
  ·
    refine ⟨2232680795856269784072767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1488453863904179856048511 2232680795856269784072767)
    ·
      refine ⟨3349021193784404676109151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232680795856269784072767 3349021193784404676109151)
      ·
        refine ⟨5023531790676607014163727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349021193784404676109151 5023531790676607014163727)
        ·
          refine ⟨7535297686014910521245591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023531790676607014163727 7535297686014910521245591)
          ·
            refine ⟨11302946529022365781868387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7535297686014910521245591 11302946529022365781868387)
            ·
              refine ⟨16954419793533548672802581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11302946529022365781868387 16954419793533548672802581)
              ·
                refine ⟨794738427821885094037621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16954419793533548672802581 794738427821885094037621)
                ·
                  refine ⟨74506727608301727566027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 794738427821885094037621 74506727608301727566027)
                  ·
                    rfl

theorem cell21_326478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_326478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326478 prefixEnd_326478 := by exact prefixLift 326478
  have htrace : WordTrace (prefixWord ++ tailWord_326478) baseStart_326478 baseEnd_326478 := by
    simpa [prefixWord, tailWord_326478, baseEnd_326478] using wordTrace_append hprefix tailTrace_326478
  have hstable : (prefixWord ++ tailWord_326478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326478).length < 2 ^ (prefixWord ++ tailWord_326478).sum := by decide
  have hdescent : baseEnd_326478 < baseStart_326478 := by decide
  rcases family_descends (prefixWord ++ tailWord_326478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326495 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 3]
def baseStart_326495 : Nat := 118140960795 + 326495 * 2 ^ 59
def prefixEnd_326495 : Nat := 4983230072969 + 3 ^ 40 * 326495 * 2
def baseEnd_326495 : Nat := 74510607239913475782659

theorem tailTrace_326495 : CollatzResearch.WordTrace tailWord_326495 prefixEnd_326495 74510607239913475782659 := by
  unfold tailWord_326495
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908250952171850751756939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7938833968114567167837959 11908250952171850751756939)
  ·
    refine ⟨17862376428257776127635409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11908250952171850751756939 17862376428257776127635409)
    ·
      refine ⟨13396782321193332095726557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17862376428257776127635409 13396782321193332095726557)
      ·
        refine ⟨5023793370447499535897459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13396782321193332095726557 5023793370447499535897459)
        ·
          refine ⟨7535690055671249303846189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023793370447499535897459 7535690055671249303846189)
          ·
            refine ⟨2825883770876718488942321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7535690055671249303846189 2825883770876718488942321)
            ·
              refine ⟨2119412828157538866706741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825883770876718488942321 2119412828157538866706741)
              ·
                refine ⟨198694952639769268753757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2119412828157538866706741 198694952639769268753757)
                ·
                  refine ⟨74510607239913475782659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198694952639769268753757 74510607239913475782659)
                  ·
                    rfl

theorem cell21_326495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3].length) (baseStart_326495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326495 prefixEnd_326495 := by exact prefixLift 326495
  have htrace : WordTrace (prefixWord ++ tailWord_326495) baseStart_326495 baseEnd_326495 := by
    simpa [prefixWord, tailWord_326495, baseEnd_326495] using wordTrace_append hprefix tailTrace_326495
  have hstable : (prefixWord ++ tailWord_326495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326495).length < 2 ^ (prefixWord ++ tailWord_326495).sum := by decide
  have hdescent : baseEnd_326495 < baseStart_326495 := by decide
  rcases family_descends (prefixWord ++ tailWord_326495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326512 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_326512 : Nat := 118140960795 + 326512 * 2 ^ 59
def prefixEnd_326512 : Nat := 4983230072969 + 3 ^ 40 * 326512 * 2
def baseEnd_326512 : Nat := 74514486871525223999291

theorem tailTrace_326512 : CollatzResearch.WordTrace tailWord_326512 prefixEnd_326512 74514486871525223999291 := by
  unfold tailWord_326512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954435496555131327562895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7939247328740175103417193 5954435496555131327562895)
  ·
    refine ⟨8931653244832696991344343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5954435496555131327562895 8931653244832696991344343)
    ·
      refine ⟨13397479867249045487016515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8931653244832696991344343 13397479867249045487016515)
      ·
        refine ⟨20096219800873568230524773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13397479867249045487016515 20096219800873568230524773)
        ·
          refine ⟨3768041212663794043223395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20096219800873568230524773 3768041212663794043223395)
          ·
            refine ⟨5652061818995691064835093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768041212663794043223395 5652061818995691064835093)
            ·
              refine ⟨264940397765423018664145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5652061818995691064835093 264940397765423018664145)
              ·
                refine ⟨198705298324067263998109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264940397765423018664145 198705298324067263998109)
                ·
                  refine ⟨74514486871525223999291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198705298324067263998109 74514486871525223999291)
                  ·
                    rfl

theorem cell21_326512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_326512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326512 prefixEnd_326512 := by exact prefixLift 326512
  have htrace : WordTrace (prefixWord ++ tailWord_326512) baseStart_326512 baseEnd_326512 := by
    simpa [prefixWord, tailWord_326512, baseEnd_326512] using wordTrace_append hprefix tailTrace_326512
  have hstable : (prefixWord ++ tailWord_326512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326512).length < 2 ^ (prefixWord ++ tailWord_326512).sum := by decide
  have hdescent : baseEnd_326512 < baseStart_326512 := by decide
  rcases family_descends (prefixWord ++ tailWord_326512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326523 : List Nat := [1, 1, 1, 1, 1, 5, 5, 6]
def baseStart_326523 : Nat := 118140960795 + 326523 * 2 ^ 59
def prefixEnd_326523 : Nat := 4983230072969 + 3 ^ 40 * 326523 * 2
def baseEnd_326523 : Nat := 24838999073797216438645

theorem tailTrace_326523 : CollatzResearch.WordTrace tailWord_326523 prefixEnd_326523 24838999073797216438645 := by
  unfold tailWord_326523
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909272196070411533776223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7939514797380274355850815 11909272196070411533776223)
  ·
    refine ⟨17863908294105617300664335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11909272196070411533776223 17863908294105617300664335)
    ·
      refine ⟨26795862441158425950996503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863908294105617300664335 26795862441158425950996503)
      ·
        refine ⟨40193793661737638926494755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26795862441158425950996503 40193793661737638926494755)
        ·
          refine ⟨60290690492606458389742133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40193793661737638926494755 60290690492606458389742133)
          ·
            refine ⟨5652252233681855474038325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60290690492606458389742133 5652252233681855474038325)
            ·
              refine ⟨529898646907673950691093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5652252233681855474038325 529898646907673950691093)
              ·
                refine ⟨24838999073797216438645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 529898646907673950691093 24838999073797216438645)
                ·
                  rfl

theorem cell21_326523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_326523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326523 prefixEnd_326523 := by exact prefixLift 326523
  have htrace : WordTrace (prefixWord ++ tailWord_326523) baseStart_326523 baseEnd_326523 := by
    simpa [prefixWord, tailWord_326523, baseEnd_326523] using wordTrace_append hprefix tailTrace_326523
  have hstable : (prefixWord ++ tailWord_326523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326523).length < 2 ^ (prefixWord ++ tailWord_326523).sum := by decide
  have hdescent : baseEnd_326523 < baseStart_326523 := by decide
  rcases family_descends (prefixWord ++ tailWord_326523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326692 : List Nat := [2, 3, 1, 4, 1, 1, 3, 6]
def baseStart_326692 : Nat := 118140960795 + 326692 * 2 ^ 59
def prefixEnd_326692 : Nat := 4983230072969 + 3 ^ 40 * 326692 * 2
def baseEnd_326692 : Nat := 24851855107961636999641

theorem tailTrace_326692 : CollatzResearch.WordTrace tailWord_326692 prefixEnd_326692 24851855107961636999641 := by
  unfold tailWord_326692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957718066229076698339165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7943624088305435597785553 5957718066229076698339165)
  ·
    refine ⟨2234144274835903761877187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5957718066229076698339165 2234144274835903761877187)
    ·
      refine ⟨3351216412253855642815781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234144274835903761877187 3351216412253855642815781)
      ·
        refine ⟨628353077297597933027959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3351216412253855642815781 628353077297597933027959)
        ·
          refine ⟨942529615946396899541939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628353077297597933027959 942529615946396899541939)
          ·
            refine ⟨1413794423919595349312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942529615946396899541939 1413794423919595349312909)
            ·
              refine ⟨530172908969848255992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1413794423919595349312909 530172908969848255992341)
              ·
                refine ⟨24851855107961636999641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 530172908969848255992341 24851855107961636999641)
                ·
                  rfl

theorem cell21_326692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_326692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326692 prefixEnd_326692 := by exact prefixLift 326692
  have htrace : WordTrace (prefixWord ++ tailWord_326692) baseStart_326692 baseEnd_326692 := by
    simpa [prefixWord, tailWord_326692, baseEnd_326692] using wordTrace_append hprefix tailTrace_326692
  have hstable : (prefixWord ++ tailWord_326692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326692).length < 2 ^ (prefixWord ++ tailWord_326692).sum := by decide
  have hdescent : baseEnd_326692 < baseStart_326692 := by decide
  rcases family_descends (prefixWord ++ tailWord_326692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326706 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_326706 : Nat := 118140960795 + 326706 * 2 ^ 59
def prefixEnd_326706 : Nat := 4983230072969 + 3 ^ 40 * 326706 * 2
def baseEnd_326706 : Nat := 74558760314623997765561

theorem tailTrace_326706 : CollatzResearch.WordTrace tailWord_326706 prefixEnd_326706 74558760314623997765561 := by
  unfold tailWord_326706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978986688601858446921993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7943964502938289191791981 2978986688601858446921993)
  ·
    refine ⟨2234240016451393835191495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2978986688601858446921993 2234240016451393835191495)
    ·
      refine ⟨3351360024677090752787243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234240016451393835191495 3351360024677090752787243)
      ·
        refine ⟨5027040037015636129180865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351360024677090752787243 5027040037015636129180865)
        ·
          refine ⟨3770280027761727096885649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5027040037015636129180865 3770280027761727096885649)
          ·
            refine ⟨2827710020821295322664237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3770280027761727096885649 2827710020821295322664237)
            ·
              refine ⟨1060391257807985745999089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2827710020821295322664237 1060391257807985745999089)
              ·
                refine ⟨795293443355989309499317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060391257807985745999089 795293443355989309499317)
                ·
                  refine ⟨74558760314623997765561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 795293443355989309499317 74558760314623997765561)
                  ·
                    rfl

theorem cell21_326706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_326706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326706 prefixEnd_326706 := by exact prefixLift 326706
  have htrace : WordTrace (prefixWord ++ tailWord_326706) baseStart_326706 baseEnd_326706 := by
    simpa [prefixWord, tailWord_326706, baseEnd_326706] using wordTrace_append hprefix tailTrace_326706
  have hstable : (prefixWord ++ tailWord_326706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326706).length < 2 ^ (prefixWord ++ tailWord_326706).sum := by decide
  have hdescent : baseEnd_326706 < baseStart_326706 := by decide
  rcases family_descends (prefixWord ++ tailWord_326706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326720 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_326720 : Nat := 118140960795 + 326720 * 2 ^ 59
def prefixEnd_326720 : Nat := 4983230072969 + 3 ^ 40 * 326720 * 2
def baseEnd_326720 : Nat := 74561955305363084532199

theorem tailTrace_326720 : CollatzResearch.WordTrace tailWord_326720 prefixEnd_326720 74561955305363084532199 := by
  unfold tailWord_326720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958228688178357089348807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7944304917571142785798409 5958228688178357089348807)
  ·
    refine ⟨8937343032267535634023211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5958228688178357089348807 8937343032267535634023211)
    ·
      refine ⟨13406014548401303451034817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937343032267535634023211 13406014548401303451034817)
      ·
        refine ⟨10054510911300977588276113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13406014548401303451034817 10054510911300977588276113)
        ·
          refine ⟨7540883183475733191207085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10054510911300977588276113 7540883183475733191207085)
          ·
            refine ⟨2827831193803399946702657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7540883183475733191207085 2827831193803399946702657)
            ·
              refine ⟨2120873395352549960026993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827831193803399946702657 2120873395352549960026993)
              ·
                refine ⟨1590655046514412470020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120873395352549960026993 1590655046514412470020245)
                ·
                  refine ⟨74561955305363084532199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1590655046514412470020245 74561955305363084532199)
                  ·
                    rfl

theorem cell21_326720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_326720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326720 prefixEnd_326720 := by exact prefixLift 326720
  have htrace : WordTrace (prefixWord ++ tailWord_326720) baseStart_326720 baseEnd_326720 := by
    simpa [prefixWord, tailWord_326720, baseEnd_326720] using wordTrace_append hprefix tailTrace_326720
  have hstable : (prefixWord ++ tailWord_326720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326720).length < 2 ^ (prefixWord ++ tailWord_326720).sum := by decide
  have hdescent : baseEnd_326720 < baseStart_326720 := by decide
  rcases family_descends (prefixWord ++ tailWord_326720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326723 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 3]
def baseStart_326723 : Nat := 118140960795 + 326723 * 2 ^ 59
def prefixEnd_326723 : Nat := 4983230072969 + 3 ^ 40 * 326723 * 2
def baseEnd_326723 : Nat := 74562639946235745982193

theorem tailTrace_326723 : CollatzResearch.WordTrace tailWord_326723 prefixEnd_326723 74562639946235745982193 := by
  unfold tailWord_326723
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916566795345845691056823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7944377863563897127371215 11916566795345845691056823)
  ·
    refine ⟨17874850193018768536585235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11916566795345845691056823 17874850193018768536585235)
    ·
      refine ⟨26812275289528152804877853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17874850193018768536585235 26812275289528152804877853)
      ·
        refine ⟨10054603233573057301829195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26812275289528152804877853 10054603233573057301829195)
        ·
          refine ⟨15081904850359585952743793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054603233573057301829195 15081904850359585952743793)
          ·
            refine ⟨11311428637769689464557845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15081904850359585952743793 11311428637769689464557845)
            ·
              refine ⟨530223217395454193651149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11311428637769689464557845 530223217395454193651149)
              ·
                refine ⟨198833706523295322619181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530223217395454193651149 198833706523295322619181)
                ·
                  refine ⟨74562639946235745982193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198833706523295322619181 74562639946235745982193)
                  ·
                    rfl

theorem cell21_326723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3].length) (baseStart_326723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326723 prefixEnd_326723 := by exact prefixLift 326723
  have htrace : WordTrace (prefixWord ++ tailWord_326723) baseStart_326723 baseEnd_326723 := by
    simpa [prefixWord, tailWord_326723, baseEnd_326723] using wordTrace_append hprefix tailTrace_326723
  have hstable : (prefixWord ++ tailWord_326723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326723).length < 2 ^ (prefixWord ++ tailWord_326723).sum := by decide
  have hdescent : baseEnd_326723 < baseStart_326723 := by decide
  rcases family_descends (prefixWord ++ tailWord_326723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326737 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_326737 : Nat := 118140960795 + 326737 * 2 ^ 59
def prefixEnd_326737 : Nat := 4983230072969 + 3 ^ 40 * 326737 * 2
def baseEnd_326737 : Nat := 74565834936974832748831

theorem tailTrace_326737 : CollatzResearch.WordTrace tailWord_326737 prefixEnd_326737 74565834936974832748831 := by
  unfold tailWord_326737
  simp only [CollatzResearch.WordTrace]
  refine ⟨11917077417295126082066465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7944718278196750721377643 11917077417295126082066465)
  ·
    refine ⟨8937808062971344561549849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11917077417295126082066465 8937808062971344561549849)
    ·
      refine ⟨6703356047228508421162387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8937808062971344561549849 6703356047228508421162387)
      ·
        refine ⟨10055034070842762631743581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703356047228508421162387 10055034070842762631743581)
        ·
          refine ⟨3770637776566035986903843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10055034070842762631743581 3770637776566035986903843)
          ·
            refine ⟨5655956664849053980355765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770637776566035986903843 5655956664849053980355765)
            ·
              refine ⟨530245937329598810658353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5655956664849053980355765 530245937329598810658353)
              ·
                refine ⟨397684452997199107993765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530245937329598810658353 397684452997199107993765)
                ·
                  refine ⟨74565834936974832748831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397684452997199107993765 74565834936974832748831)
                  ·
                    rfl

theorem cell21_326737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_326737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326737 prefixEnd_326737 := by exact prefixLift 326737
  have htrace : WordTrace (prefixWord ++ tailWord_326737) baseStart_326737 baseEnd_326737 := by
    simpa [prefixWord, tailWord_326737, baseEnd_326737] using wordTrace_append hprefix tailTrace_326737
  have hstable : (prefixWord ++ tailWord_326737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326737).length < 2 ^ (prefixWord ++ tailWord_326737).sum := by decide
  have hdescent : baseEnd_326737 < baseStart_326737 := by decide
  rcases family_descends (prefixWord ++ tailWord_326737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326813 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_326813 : Nat := 118140960795 + 326813 * 2 ^ 59
def prefixEnd_326813 : Nat := 4983230072969 + 3 ^ 40 * 326813 * 2
def baseEnd_326813 : Nat := 74583179172415589482009

theorem tailTrace_326813 : CollatzResearch.WordTrace tailWord_326813 prefixEnd_326813 74583179172415589482009 := by
  unfold tailWord_326813
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919849365019791061833093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7946566243346527374555395 11919849365019791061833093)
  ·
    refine ⟨2234971755941210824093705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11919849365019791061833093 2234971755941210824093705)
    ·
      refine ⟨1676228816955908118070279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2234971755941210824093705 1676228816955908118070279)
      ·
        refine ⟨2514343225433862177105419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676228816955908118070279 2514343225433862177105419)
        ·
          refine ⟨3771514838150793265658129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514343225433862177105419 3771514838150793265658129)
          ·
            refine ⟨2828636128613094949243597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771514838150793265658129 2828636128613094949243597)
            ·
              refine ⟨1060738548229910605966349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2828636128613094949243597 1060738548229910605966349)
              ·
                refine ⟨397776955586216477237381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060738548229910605966349 397776955586216477237381)
                ·
                  refine ⟨74583179172415589482009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 397776955586216477237381 74583179172415589482009)
                  ·
                    rfl

theorem cell21_326813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_326813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326813 prefixEnd_326813 := by exact prefixLift 326813
  have htrace : WordTrace (prefixWord ++ tailWord_326813) baseStart_326813 baseEnd_326813 := by
    simpa [prefixWord, tailWord_326813, baseEnd_326813] using wordTrace_append hprefix tailTrace_326813
  have hstable : (prefixWord ++ tailWord_326813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326813).length < 2 ^ (prefixWord ++ tailWord_326813).sum := by decide
  have hdescent : baseEnd_326813 < baseStart_326813 := by decide
  rcases family_descends (prefixWord ++ tailWord_326813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326850 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_326850 : Nat := 118140960795 + 326850 * 2 ^ 59
def prefixEnd_326850 : Nat := 4983230072969 + 3 ^ 40 * 326850 * 2
def baseEnd_326850 : Nat := 74591623076511747365267

theorem tailTrace_326850 : CollatzResearch.WordTrace tailWord_326850 prefixEnd_326850 74591623076511747365267 := by
  unfold tailWord_326850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2980299716471436595232501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7947465910590497587286669 2980299716471436595232501)
  ·
    refine ⟨279403098419197180803047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2980299716471436595232501 279403098419197180803047)
    ·
      refine ⟨419104647628795771204571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279403098419197180803047 419104647628795771204571)
      ·
        refine ⟨628656971443193656806857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419104647628795771204571 628656971443193656806857)
        ·
          refine ⟨471492728582395242605143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628656971443193656806857 471492728582395242605143)
          ·
            refine ⟨707239092873592863907715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471492728582395242605143 707239092873592863907715)
            ·
              refine ⟨1060858639310389295861573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707239092873592863907715 1060858639310389295861573)
              ·
                refine ⟨198910994870697992974045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1060858639310389295861573 198910994870697992974045)
                ·
                  refine ⟨74591623076511747365267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198910994870697992974045 74591623076511747365267)
                  ·
                    rfl

theorem cell21_326850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_326850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326850 prefixEnd_326850 := by exact prefixLift 326850
  have htrace : WordTrace (prefixWord ++ tailWord_326850) baseStart_326850 baseEnd_326850 := by
    simpa [prefixWord, tailWord_326850, baseEnd_326850] using wordTrace_append hprefix tailTrace_326850
  have hstable : (prefixWord ++ tailWord_326850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326850).length < 2 ^ (prefixWord ++ tailWord_326850).sum := by decide
  have hdescent : baseEnd_326850 < baseStart_326850 := by decide
  rcases family_descends (prefixWord ++ tailWord_326850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326948 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_326948 : Nat := 118140960795 + 326948 * 2 ^ 59
def prefixEnd_326948 : Nat := 4983230072969 + 3 ^ 40 * 326948 * 2
def baseEnd_326948 : Nat := 74613988011685354731733

theorem tailTrace_326948 : CollatzResearch.WordTrace tailWord_326948 prefixEnd_326948 74613988011685354731733 := by
  unfold tailWord_326948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962386609765354558998749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7949848813020472745331665 5962386609765354558998749)
  ·
    refine ⟨2235894978662007959624531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5962386609765354558998749 2235894978662007959624531)
    ·
      refine ⟨3353842467993011939436797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235894978662007959624531 3353842467993011939436797)
      ·
        refine ⟨1257690925497379477288799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3353842467993011939436797 1257690925497379477288799)
        ·
          refine ⟨1886536388246069215933199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257690925497379477288799 1886536388246069215933199)
          ·
            refine ⟨2829804582369103823899799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886536388246069215933199 2829804582369103823899799)
            ·
              refine ⟨4244706873553655735849699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829804582369103823899799 4244706873553655735849699)
              ·
                refine ⟨6367060310330483603774549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244706873553655735849699 6367060310330483603774549)
                ·
                  refine ⟨74613988011685354731733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6367060310330483603774549 74613988011685354731733)
                  ·
                    rfl

theorem cell21_326948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_326948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326948 prefixEnd_326948 := by exact prefixLift 326948
  have htrace : WordTrace (prefixWord ++ tailWord_326948) baseStart_326948 baseEnd_326948 := by
    simpa [prefixWord, tailWord_326948, baseEnd_326948] using wordTrace_append hprefix tailTrace_326948
  have hstable : (prefixWord ++ tailWord_326948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326948).length < 2 ^ (prefixWord ++ tailWord_326948).sum := by decide
  have hdescent : baseEnd_326948 < baseStart_326948 := by decide
  rcases family_descends (prefixWord ++ tailWord_326948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326993 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_326993 : Nat := 118140960795 + 326993 * 2 ^ 59
def prefixEnd_326993 : Nat := 4983230072969 + 3 ^ 40 * 326993 * 2
def baseEnd_326993 : Nat := 74624257624775276481641

theorem tailTrace_326993 : CollatzResearch.WordTrace tailWord_326993 prefixEnd_326993 74624257624775276481641 := by
  unfold tailWord_326993
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926414504367681803385633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950943002911787868923755 11926414504367681803385633)
  ·
    refine ⟨8944810878275761352539225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11926414504367681803385633 8944810878275761352539225)
    ·
      refine ⟨6708608158706821014404419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8944810878275761352539225 6708608158706821014404419)
      ·
        refine ⟨10062912238060231521606629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6708608158706821014404419 10062912238060231521606629)
        ·
          refine ⟨1886796044636293410301243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10062912238060231521606629 1886796044636293410301243)
          ·
            refine ⟨2830194066954440115451865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886796044636293410301243 2830194066954440115451865)
            ·
              refine ⟨2122645550215830086588899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830194066954440115451865 2122645550215830086588899)
              ·
                refine ⟨3183968325323745129883349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122645550215830086588899 3183968325323745129883349)
                ·
                  refine ⟨74624257624775276481641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3183968325323745129883349 74624257624775276481641)
                  ·
                    rfl

theorem cell21_326993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_326993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_326993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_326993 prefixEnd_326993 := by exact prefixLift 326993
  have htrace : WordTrace (prefixWord ++ tailWord_326993) baseStart_326993 baseEnd_326993 := by
    simpa [prefixWord, tailWord_326993, baseEnd_326993] using wordTrace_append hprefix tailTrace_326993
  have hstable : (prefixWord ++ tailWord_326993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326993).length < 2 ^ (prefixWord ++ tailWord_326993).sum := by decide
  have hdescent : baseEnd_326993 < baseStart_326993 := by decide
  rcases family_descends (prefixWord ++ tailWord_326993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327159 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_327159 : Nat := 118140960795 + 327159 * 2 ^ 59
def prefixEnd_327159 : Nat := 4983230072969 + 3 ^ 40 * 327159 * 2
def baseEnd_327159 : Nat := 74662141086395876714635

theorem tailTrace_327159 : CollatzResearch.WordTrace tailWord_327159 prefixEnd_327159 74662141086395876714635 := by
  unfold tailWord_327159
  simp only [CollatzResearch.WordTrace]
  refine ⟨11932469021766292153928531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7954979347844194769285687 11932469021766292153928531)
  ·
    refine ⟨17898703532649438230892797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11932469021766292153928531 17898703532649438230892797)
    ·
      refine ⟨6712013824743539336584799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17898703532649438230892797 6712013824743539336584799)
      ·
        refine ⟨10068020737115309004877199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712013824743539336584799 10068020737115309004877199)
        ·
          refine ⟨15102031105672963507315799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10068020737115309004877199 15102031105672963507315799)
          ·
            refine ⟨22653046658509445260973699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15102031105672963507315799 22653046658509445260973699)
            ·
              refine ⟨33979569987764167891460549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22653046658509445260973699 33979569987764167891460549)
              ·
                refine ⟨6371169372705781479648853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33979569987764167891460549 6371169372705781479648853)
                ·
                  refine ⟨74662141086395876714635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6371169372705781479648853 74662141086395876714635)
                  ·
                    rfl

theorem cell21_327159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_327159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327159 prefixEnd_327159 := by exact prefixLift 327159
  have htrace : WordTrace (prefixWord ++ tailWord_327159) baseStart_327159 baseEnd_327159 := by
    simpa [prefixWord, tailWord_327159, baseEnd_327159] using wordTrace_append hprefix tailTrace_327159
  have hstable : (prefixWord ++ tailWord_327159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327159).length < 2 ^ (prefixWord ++ tailWord_327159).sum := by decide
  have hdescent : baseEnd_327159 < baseStart_327159 := by decide
  rcases family_descends (prefixWord ++ tailWord_327159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327221 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_327221 : Nat := 118140960795 + 327221 * 2 ^ 59
def prefixEnd_327221 : Nat := 4983230072969 + 3 ^ 40 * 327221 * 2
def baseEnd_327221 : Nat := 74676290331097546681175

theorem tailTrace_327221 : CollatzResearch.WordTrace tailWord_327221 prefixEnd_327221 74676290331097546681175 := by
  unfold tailWord_327221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11934730347541676742685517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7956486898361117828457011 11934730347541676742685517)
  ·
    refine ⟨4475523880328128778507069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11934730347541676742685517 4475523880328128778507069)
    ·
      refine ⟨1678321455123048291940151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4475523880328128778507069 1678321455123048291940151)
      ·
        refine ⟨2517482182684572437910227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678321455123048291940151 2517482182684572437910227)
        ·
          refine ⟨3776223274026858656865341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517482182684572437910227 3776223274026858656865341)
          ·
            refine ⟨1416083727760071996324503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3776223274026858656865341 1416083727760071996324503)
            ·
              refine ⟨2124125591640107994486755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416083727760071996324503 2124125591640107994486755)
              ·
                refine ⟨3186188387460161991730133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124125591640107994486755 3186188387460161991730133)
                ·
                  refine ⟨74676290331097546681175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3186188387460161991730133 74676290331097546681175)
                  ·
                    rfl

theorem cell21_327221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_327221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327221 prefixEnd_327221 := by exact prefixLift 327221
  have htrace : WordTrace (prefixWord ++ tailWord_327221) baseStart_327221 baseEnd_327221 := by
    simpa [prefixWord, tailWord_327221, baseEnd_327221] using wordTrace_append hprefix tailTrace_327221
  have hstable : (prefixWord ++ tailWord_327221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327221).length < 2 ^ (prefixWord ++ tailWord_327221).sum := by decide
  have hdescent : baseEnd_327221 < baseStart_327221 := by decide
  rcases family_descends (prefixWord ++ tailWord_327221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327252 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_327252 : Nat := 118140960795 + 327252 * 2 ^ 59
def prefixEnd_327252 : Nat := 4983230072969 + 3 ^ 40 * 327252 * 2
def baseEnd_327252 : Nat := 74683364953448381664445

theorem tailTrace_327252 : CollatzResearch.WordTrace tailWord_327252 prefixEnd_327252 74683364953448381664445 := by
  unfold tailWord_327252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967930505214684518532005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7957240673619579358042673 5967930505214684518532005)
  ·
    refine ⟨1118986969727753347224751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5967930505214684518532005 1118986969727753347224751)
    ·
      refine ⟨1678480454591630020837127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118986969727753347224751 1678480454591630020837127)
      ·
        refine ⟨2517720681887445031255691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678480454591630020837127 2517720681887445031255691)
        ·
          refine ⟨3776581022831167546883537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517720681887445031255691 3776581022831167546883537)
          ·
            refine ⟨2832435767123375660162653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776581022831167546883537 2832435767123375660162653)
            ·
              refine ⟨1062163412671265872560995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2832435767123375660162653 1062163412671265872560995)
              ·
                refine ⟨1593245119006898808841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062163412671265872560995 1593245119006898808841493)
                ·
                  refine ⟨74683364953448381664445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1593245119006898808841493 74683364953448381664445)
                  ·
                    rfl

theorem cell21_327252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_327252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327252 prefixEnd_327252 := by exact prefixLift 327252
  have htrace : WordTrace (prefixWord ++ tailWord_327252) baseStart_327252 baseEnd_327252 := by
    simpa [prefixWord, tailWord_327252, baseEnd_327252] using wordTrace_append hprefix tailTrace_327252
  have hstable : (prefixWord ++ tailWord_327252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327252).length < 2 ^ (prefixWord ++ tailWord_327252).sum := by decide
  have hdescent : baseEnd_327252 < baseStart_327252 := by decide
  rcases family_descends (prefixWord ++ tailWord_327252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327300 : List Nat := [2, 3, 2, 1, 5, 1, 7]
def baseStart_327300 : Nat := 118140960795 + 327300 * 2 ^ 59
def prefixEnd_327300 : Nat := 4983230072969 + 3 ^ 40 * 327300 * 2
def baseEnd_327300 : Nat := 8299368800823440540483

theorem tailTrace_327300 : CollatzResearch.WordTrace tailWord_327300 prefixEnd_327300 8299368800823440540483 := by
  unfold tailWord_327300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968805857127736617405677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7958407809503648823207569 5968805857127736617405677)
  ·
    refine ⟨2238302196422901231527129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5968805857127736617405677 2238302196422901231527129)
    ·
      refine ⟨1678726647317175923645347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2238302196422901231527129 1678726647317175923645347)
      ·
        refine ⟨2518089970975763885468021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678726647317175923645347 2518089970975763885468021)
        ·
          refine ⟨236070934778977864262627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2518089970975763885468021 236070934778977864262627)
          ·
            refine ⟨354106402168466796393941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236070934778977864262627 354106402168466796393941)
            ·
              refine ⟨8299368800823440540483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 354106402168466796393941 8299368800823440540483)
              ·
                rfl

theorem cell21_327300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 7].length) (baseStart_327300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327300 prefixEnd_327300 := by exact prefixLift 327300
  have htrace : WordTrace (prefixWord ++ tailWord_327300) baseStart_327300 baseEnd_327300 := by
    simpa [prefixWord, tailWord_327300, baseEnd_327300] using wordTrace_append hprefix tailTrace_327300
  have hstable : (prefixWord ++ tailWord_327300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327300).length < 2 ^ (prefixWord ++ tailWord_327300).sum := by decide
  have hdescent : baseEnd_327300 < baseStart_327300 := by decide
  rcases family_descends (prefixWord ++ tailWord_327300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327430 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_327430 : Nat := 118140960795 + 327430 * 2 ^ 59
def prefixEnd_327430 : Nat := 4983230072969 + 3 ^ 40 * 327430 * 2
def baseEnd_327430 : Nat := 74723986978559627697415

theorem tailTrace_327430 : CollatzResearch.WordTrace tailWord_327430 prefixEnd_327430 74723986978559627697415 := by
  unfold tailWord_327430
  simp only [CollatzResearch.WordTrace]
  refine ⟨373198537618265794907617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7961568802523003624695829 373198537618265794907617)
  ·
    refine ⟨279898903213699346180713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 373198537618265794907617 279898903213699346180713)
    ·
      refine ⟨209924177410274509635535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279898903213699346180713 209924177410274509635535)
      ·
        refine ⟨314886266115411764453303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209924177410274509635535 314886266115411764453303)
        ·
          refine ⟨472329399173117646679955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314886266115411764453303 472329399173117646679955)
          ·
            refine ⟨708494098759676470019933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472329399173117646679955 708494098759676470019933)
            ·
              refine ⟨265685287034878676257475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708494098759676470019933 265685287034878676257475)
              ·
                refine ⟨398527930552318014386213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265685287034878676257475 398527930552318014386213)
                ·
                  refine ⟨74723986978559627697415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398527930552318014386213 74723986978559627697415)
                  ·
                    rfl

theorem cell21_327430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_327430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327430 prefixEnd_327430 := by exact prefixLift 327430
  have htrace : WordTrace (prefixWord ++ tailWord_327430) baseStart_327430 baseEnd_327430 := by
    simpa [prefixWord, tailWord_327430, baseEnd_327430] using wordTrace_append hprefix tailTrace_327430
  have hstable : (prefixWord ++ tailWord_327430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327430).length < 2 ^ (prefixWord ++ tailWord_327430).sum := by decide
  have hdescent : baseEnd_327430 < baseStart_327430 := by decide
  rcases family_descends (prefixWord ++ tailWord_327430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327556 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_327556 : Nat := 118140960795 + 327556 * 2 ^ 59
def prefixEnd_327556 : Nat := 4983230072969 + 3 ^ 40 * 327556 * 2
def baseEnd_327556 : Nat := 74752741895211408597157

theorem tailTrace_327556 : CollatzResearch.WordTrace tailWord_327556 prefixEnd_327556 74752741895211408597157 := by
  unfold tailWord_327556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973474400664014478065261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7964632534218685970753681 5973474400664014478065261)
  ·
    refine ⟨2240052900249005429274473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5973474400664014478065261 2240052900249005429274473)
    ·
      refine ⟨1680039675186754071955855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2240052900249005429274473 1680039675186754071955855)
      ·
        refine ⟨2520059512780131107933783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680039675186754071955855 2520059512780131107933783)
        ·
          refine ⟨3780089269170196661900675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520059512780131107933783 3780089269170196661900675)
          ·
            refine ⟨5670133903755294992851013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780089269170196661900675 5670133903755294992851013)
            ·
              refine ⟨1063150106954117811159565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5670133903755294992851013 1063150106954117811159565)
              ·
                refine ⟨398681290107794179184837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063150106954117811159565 398681290107794179184837)
                ·
                  refine ⟨74752741895211408597157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398681290107794179184837 74752741895211408597157)
                  ·
                    rfl

theorem cell21_327556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_327556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327556 prefixEnd_327556 := by exact prefixLift 327556
  have htrace : WordTrace (prefixWord ++ tailWord_327556) baseStart_327556 baseEnd_327556 := by
    simpa [prefixWord, tailWord_327556, baseEnd_327556] using wordTrace_append hprefix tailTrace_327556
  have hstable : (prefixWord ++ tailWord_327556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327556).length < 2 ^ (prefixWord ++ tailWord_327556).sum := by decide
  have hdescent : baseEnd_327556 < baseStart_327556 := by decide
  rcases family_descends (prefixWord ++ tailWord_327556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327576 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_327576 : Nat := 118140960795 + 327576 * 2 ^ 59
def prefixEnd_327576 : Nat := 4983230072969 + 3 ^ 40 * 327576 * 2
def baseEnd_327576 : Nat := 74757306167695818263783

theorem tailTrace_327576 : CollatzResearch.WordTrace tailWord_327576 prefixEnd_327576 74757306167695818263783 := by
  unfold tailWord_327576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973839130627786185929291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7965118840837048247905721 5973839130627786185929291)
  ·
    refine ⟨8960758695941679278893937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973839130627786185929291 8960758695941679278893937)
    ·
      refine ⟨6720569021956259459170453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8960758695941679278893937 6720569021956259459170453)
      ·
        refine ⟨315026672904199662148615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6720569021956259459170453 315026672904199662148615)
        ·
          refine ⟨472540009356299493222923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315026672904199662148615 472540009356299493222923)
          ·
            refine ⟨708810014034449239834385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472540009356299493222923 708810014034449239834385)
            ·
              refine ⟨531607510525836929875789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708810014034449239834385 531607510525836929875789)
              ·
                refine ⟨199352816447188848703421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531607510525836929875789 199352816447188848703421)
                ·
                  refine ⟨74757306167695818263783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199352816447188848703421 74757306167695818263783)
                  ·
                    rfl

theorem cell21_327576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_327576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327576 prefixEnd_327576 := by exact prefixLift 327576
  have htrace : WordTrace (prefixWord ++ tailWord_327576) baseStart_327576 baseEnd_327576 := by
    simpa [prefixWord, tailWord_327576, baseEnd_327576] using wordTrace_append hprefix tailTrace_327576
  have hstable : (prefixWord ++ tailWord_327576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327576).length < 2 ^ (prefixWord ++ tailWord_327576).sum := by decide
  have hdescent : baseEnd_327576 < baseStart_327576 := by decide
  rcases family_descends (prefixWord ++ tailWord_327576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327584 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_327584 : Nat := 118140960795 + 327584 * 2 ^ 59
def prefixEnd_327584 : Nat := 4983230072969 + 3 ^ 40 * 327584 * 2
def baseEnd_327584 : Nat := 74759131876689582130433

theorem tailTrace_327584 : CollatzResearch.WordTrace tailWord_327584 prefixEnd_327584 74759131876689582130433 := by
  unfold tailWord_327584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973985022613294869074903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7965313363484393158766537 5973985022613294869074903)
  ·
    refine ⟨8960977533919942303612355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973985022613294869074903 8960977533919942303612355)
    ·
      refine ⟨13441466300879913455418533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8960977533919942303612355 13441466300879913455418533)
      ·
        refine ⟨2520274931414983772890975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13441466300879913455418533 2520274931414983772890975)
        ·
          refine ⟨3780412397122475659336463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520274931414983772890975 3780412397122475659336463)
          ·
            refine ⟨5670618595683713489004695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780412397122475659336463 5670618595683713489004695)
            ·
              refine ⟨8505927893525570233507043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670618595683713489004695 8505927893525570233507043)
              ·
                refine ⟨12758891840288355350260565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505927893525570233507043 12758891840288355350260565)
                ·
                  refine ⟨74759131876689582130433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12758891840288355350260565 74759131876689582130433)
                  ·
                    rfl

theorem cell21_327584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_327584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327584 prefixEnd_327584 := by exact prefixLift 327584
  have htrace : WordTrace (prefixWord ++ tailWord_327584) baseStart_327584 baseEnd_327584 := by
    simpa [prefixWord, tailWord_327584, baseEnd_327584] using wordTrace_append hprefix tailTrace_327584
  have hstable : (prefixWord ++ tailWord_327584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327584).length < 2 ^ (prefixWord ++ tailWord_327584).sum := by decide
  have hdescent : baseEnd_327584 < baseStart_327584 := by decide
  rcases family_descends (prefixWord ++ tailWord_327584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327601 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_327601 : Nat := 118140960795 + 327601 * 2 ^ 59
def prefixEnd_327601 : Nat := 4983230072969 + 3 ^ 40 * 327601 * 2
def baseEnd_327601 : Nat := 74763011508301330347065

theorem tailTrace_327601 : CollatzResearch.WordTrace tailWord_327601 prefixEnd_327601 74763011508301330347065 := by
  unfold tailWord_327601
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948590086165001641518657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7965726724110001094345771 11948590086165001641518657)
  ·
    refine ⟨8961442564623751231138993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11948590086165001641518657 8961442564623751231138993)
    ·
      refine ⟨6721081923467813423354245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8961442564623751231138993 6721081923467813423354245)
      ·
        refine ⟨1260202860650215016878921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6721081923467813423354245 1260202860650215016878921)
        ·
          refine ⟨945152145487661262659191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260202860650215016878921 945152145487661262659191)
          ·
            refine ⟨1417728218231491893988787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945152145487661262659191 1417728218231491893988787)
            ·
              refine ⟨2126592327347237840983181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417728218231491893988787 2126592327347237840983181)
              ·
                refine ⟨797472122755214190368693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2126592327347237840983181 797472122755214190368693)
                ·
                  refine ⟨74763011508301330347065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 797472122755214190368693 74763011508301330347065)
                  ·
                    rfl

theorem cell21_327601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_327601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327601 prefixEnd_327601 := by exact prefixLift 327601
  have htrace : WordTrace (prefixWord ++ tailWord_327601) baseStart_327601 baseEnd_327601 := by
    simpa [prefixWord, tailWord_327601, baseEnd_327601] using wordTrace_append hprefix tailTrace_327601
  have hstable : (prefixWord ++ tailWord_327601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327601).length < 2 ^ (prefixWord ++ tailWord_327601).sum := by decide
  have hdescent : baseEnd_327601 < baseStart_327601 := by decide
  rcases family_descends (prefixWord ++ tailWord_327601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327694 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_327694 : Nat := 118140960795 + 327694 * 2 ^ 59
def prefixEnd_327694 : Nat := 4983230072969 + 3 ^ 40 * 327694 * 2
def baseEnd_327694 : Nat := 74784235375353835296875

theorem tailTrace_327694 : CollatzResearch.WordTrace tailWord_327694 prefixEnd_327694 74784235375353835296875 := by
  unfold tailWord_327694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493997759353509815581767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7967988049885385683102757 1493997759353509815581767)
  ·
    refine ⟨2240996639030264723372651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1493997759353509815581767 2240996639030264723372651)
    ·
      refine ⟨3361494958545397085058977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240996639030264723372651 3361494958545397085058977)
      ·
        refine ⟨2521121218909047813794233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3361494958545397085058977 2521121218909047813794233)
        ·
          refine ⟨1890840914181785860345675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521121218909047813794233 1890840914181785860345675)
          ·
            refine ⟨2836261371272678790518513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890840914181785860345675 2836261371272678790518513)
            ·
              refine ⟨2127196028454509092888885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836261371272678790518513 2127196028454509092888885)
              ·
                refine ⟨199424627667610227458333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2127196028454509092888885 199424627667610227458333)
                ·
                  refine ⟨74784235375353835296875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199424627667610227458333 74784235375353835296875)
                  ·
                    rfl

theorem cell21_327694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_327694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327694 prefixEnd_327694 := by exact prefixLift 327694
  have htrace : WordTrace (prefixWord ++ tailWord_327694) baseStart_327694 baseEnd_327694 := by
    simpa [prefixWord, tailWord_327694, baseEnd_327694] using wordTrace_append hprefix tailTrace_327694
  have hstable : (prefixWord ++ tailWord_327694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327694).length < 2 ^ (prefixWord ++ tailWord_327694).sum := by decide
  have hdescent : baseEnd_327694 < baseStart_327694 := by decide
  rcases family_descends (prefixWord ++ tailWord_327694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327708 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_327708 : Nat := 118140960795 + 327708 * 2 ^ 59
def prefixEnd_327708 : Nat := 4983230072969 + 3 ^ 40 * 327708 * 2
def baseEnd_327708 : Nat := 74787430366092922063513

theorem tailTrace_327708 : CollatzResearch.WordTrace tailWord_327708 prefixEnd_327708 74787430366092922063513 := by
  unfold tailWord_327708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976246348388679457831889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7968328464518239277109185 5976246348388679457831889)
  ·
    refine ⟨4482184761291509593373917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5976246348388679457831889 4482184761291509593373917)
    ·
      refine ⟨1680819285484316097515219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4482184761291509593373917 1680819285484316097515219)
      ·
        refine ⟨2521228928226474146272829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680819285484316097515219 2521228928226474146272829)
        ·
          refine ⟨945460848084927804852311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2521228928226474146272829 945460848084927804852311)
          ·
            refine ⟨1418191272127391707278467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945460848084927804852311 1418191272127391707278467)
            ·
              refine ⟨2127286908191087560917701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418191272127391707278467 2127286908191087560917701)
              ·
                refine ⟨398866295285828917672069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2127286908191087560917701 398866295285828917672069)
                ·
                  refine ⟨74787430366092922063513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398866295285828917672069 74787430366092922063513)
                  ·
                    rfl

theorem cell21_327708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_327708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327708 prefixEnd_327708 := by exact prefixLift 327708
  have htrace : WordTrace (prefixWord ++ tailWord_327708) baseStart_327708 baseEnd_327708 := by
    simpa [prefixWord, tailWord_327708, baseEnd_327708] using wordTrace_append hprefix tailTrace_327708
  have hstable : (prefixWord ++ tailWord_327708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327708).length < 2 ^ (prefixWord ++ tailWord_327708).sum := by decide
  have hdescent : baseEnd_327708 < baseStart_327708 := by decide
  rcases family_descends (prefixWord ++ tailWord_327708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327922 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_327922 : Nat := 118140960795 + 327922 * 2 ^ 59
def prefixEnd_327922 : Nat := 4983230072969 + 3 ^ 40 * 327922 * 2
def baseEnd_327922 : Nat := 74836268081676105496409

theorem tailTrace_327922 : CollatzResearch.WordTrace tailWord_327922 prefixEnd_327922 74836268081676105496409 := by
  unfold tailWord_327922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990074479500518365988505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7973531945334715642636013 2990074479500518365988505)
  ·
    refine ⟨2242555859625388774491379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2990074479500518365988505 2242555859625388774491379)
    ·
      refine ⟨3363833789438083161737069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2242555859625388774491379 3363833789438083161737069)
      ·
        refine ⟨1261437671039281185651401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3363833789438083161737069 1261437671039281185651401)
        ·
          refine ⟨946078253279460889238551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261437671039281185651401 946078253279460889238551)
          ·
            refine ⟨1419117379919191333857827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946078253279460889238551 1419117379919191333857827)
            ·
              refine ⟨2128676069878787000786741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419117379919191333857827 2128676069878787000786741)
              ·
                refine ⟨199563381551136281323757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2128676069878787000786741 199563381551136281323757)
                ·
                  refine ⟨74836268081676105496409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199563381551136281323757 74836268081676105496409)
                  ·
                    rfl

theorem cell21_327922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_327922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327922 prefixEnd_327922 := by exact prefixLift 327922
  have htrace : WordTrace (prefixWord ++ tailWord_327922) baseStart_327922 baseEnd_327922 := by
    simpa [prefixWord, tailWord_327922, baseEnd_327922] using wordTrace_append hprefix tailTrace_327922
  have hstable : (prefixWord ++ tailWord_327922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327922).length < 2 ^ (prefixWord ++ tailWord_327922).sum := by decide
  have hdescent : baseEnd_327922 < baseStart_327922 := by decide
  rcases family_descends (prefixWord ++ tailWord_327922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327967 : List Nat := [1, 1, 2, 4, 3, 3, 2, 5]
def baseStart_327967 : Nat := 118140960795 + 327967 * 2 ^ 59
def prefixEnd_327967 : Nat := 4983230072969 + 3 ^ 40 * 327967 * 2
def baseEnd_327967 : Nat := 24948845898255342415439

theorem tailTrace_327967 : CollatzResearch.WordTrace tailWord_327967 prefixEnd_327967 24948845898255342415439 := by
  unfold tailWord_327967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961939202839046149342155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7974626135226030766228103 11961939202839046149342155)
  ·
    refine ⟨17942908804258569224013233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11961939202839046149342155 17942908804258569224013233)
    ·
      refine ⟨13457181603193926918009925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17942908804258569224013233 13457181603193926918009925)
      ·
        refine ⟨2523221550598861297126861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13457181603193926918009925 2523221550598861297126861)
        ·
          refine ⟨946208081474572986422573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2523221550598861297126861 946208081474572986422573)
          ·
            refine ⟨354828030552964869908465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 946208081474572986422573 354828030552964869908465)
            ·
              refine ⟨266121022914723652431349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354828030552964869908465 266121022914723652431349)
              ·
                refine ⟨24948845898255342415439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266121022914723652431349 24948845898255342415439)
                ·
                  rfl

theorem cell21_327967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 5].length) (baseStart_327967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327967 prefixEnd_327967 := by exact prefixLift 327967
  have htrace : WordTrace (prefixWord ++ tailWord_327967) baseStart_327967 baseEnd_327967 := by
    simpa [prefixWord, tailWord_327967, baseEnd_327967] using wordTrace_append hprefix tailTrace_327967
  have hstable : (prefixWord ++ tailWord_327967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327967).length < 2 ^ (prefixWord ++ tailWord_327967).sum := by decide
  have hdescent : baseEnd_327967 < baseStart_327967 := by decide
  rcases family_descends (prefixWord ++ tailWord_327967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327998 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_327998 : Nat := 118140960795 + 327998 * 2 ^ 59
def prefixEnd_327998 : Nat := 4983230072969 + 3 ^ 40 * 327998 * 2
def baseEnd_327998 : Nat := 74853612317116862229587

theorem tailTrace_327998 : CollatzResearch.WordTrace tailWord_327998 prefixEnd_327998 74853612317116862229587 := by
  unfold tailWord_327998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495383733215842305465081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7975379910484492295813765 1495383733215842305465081)
  ·
    refine ⟨1121537799911881729098811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495383733215842305465081 1121537799911881729098811)
    ·
      refine ⟨1682306699867822593648217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121537799911881729098811 1682306699867822593648217)
      ·
        refine ⟨1261730024900866945236163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1682306699867822593648217 1261730024900866945236163)
        ·
          refine ⟨1892595037351300417854245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261730024900866945236163 1892595037351300417854245)
          ·
            refine ⟨354861569503368828347671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1892595037351300417854245 354861569503368828347671)
            ·
              refine ⟨532292354255053242521507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354861569503368828347671 532292354255053242521507)
              ·
                refine ⟨798438531382579863782261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532292354255053242521507 798438531382579863782261)
                ·
                  refine ⟨74853612317116862229587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 798438531382579863782261 74853612317116862229587)
                  ·
                    rfl

theorem cell21_327998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_327998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_327998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_327998 prefixEnd_327998 := by exact prefixLift 327998
  have htrace : WordTrace (prefixWord ++ tailWord_327998) baseStart_327998 baseEnd_327998 := by
    simpa [prefixWord, tailWord_327998, baseEnd_327998] using wordTrace_append hprefix tailTrace_327998
  have hstable : (prefixWord ++ tailWord_327998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327998).length < 2 ^ (prefixWord ++ tailWord_327998).sum := by decide
  have hdescent : baseEnd_327998 < baseStart_327998 := by decide
  rcases family_descends (prefixWord ++ tailWord_327998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328071 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_328071 : Nat := 118140960795 + 328071 * 2 ^ 59
def prefixEnd_328071 : Nat := 4983230072969 + 3 ^ 40 * 328071 * 2
def baseEnd_328071 : Nat := 74870271911684957512771

theorem tailTrace_328071 : CollatzResearch.WordTrace tailWord_328071 prefixEnd_328071 74870271911684957512771 := by
  unfold tailWord_328071
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965732394462271911128067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7977154929641514607418711 11965732394462271911128067)
  ·
    refine ⟨17948598591693407866692101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11965732394462271911128067 17948598591693407866692101)
    ·
      refine ⟨3365362235942513975004769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17948598591693407866692101 3365362235942513975004769)
      ·
        refine ⟨2524021676956885481253577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365362235942513975004769 2524021676956885481253577)
        ·
          refine ⟨1893016257717664110940183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524021676956885481253577 1893016257717664110940183)
          ·
            refine ⟨2839524386576496166410275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893016257717664110940183 2839524386576496166410275)
            ·
              refine ⟨4259286579864744249615413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839524386576496166410275 4259286579864744249615413)
              ·
                refine ⟨399308116862319773401445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4259286579864744249615413 399308116862319773401445)
                ·
                  refine ⟨74870271911684957512771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399308116862319773401445 74870271911684957512771)
                  ·
                    rfl

theorem cell21_328071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_328071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328071 prefixEnd_328071 := by exact prefixLift 328071
  have htrace : WordTrace (prefixWord ++ tailWord_328071) baseStart_328071 baseEnd_328071 := by
    simpa [prefixWord, tailWord_328071, baseEnd_328071] using wordTrace_append hprefix tailTrace_328071
  have hstable : (prefixWord ++ tailWord_328071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328071).length < 2 ^ (prefixWord ++ tailWord_328071).sum := by decide
  have hdescent : baseEnd_328071 < baseStart_328071 := by decide
  rcases family_descends (prefixWord ++ tailWord_328071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328074 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_328074 : Nat := 118140960795 + 328074 * 2 ^ 59
def prefixEnd_328074 : Nat := 4983230072969 + 3 ^ 40 * 328074 * 2
def baseEnd_328074 : Nat := 74870956552557618962765

theorem tailTrace_328074 : CollatzResearch.WordTrace tailWord_328074 prefixEnd_328074 74870956552557618962765 := by
  unfold tailWord_328074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991460453362850855871819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7977227875634268948991517 2991460453362850855871819)
  ·
    refine ⟨4487190680044276283807729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2991460453362850855871819 4487190680044276283807729)
    ·
      refine ⟨3365393010033207212855797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4487190680044276283807729 3365393010033207212855797)
      ·
        refine ⟨315505594690613176205231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3365393010033207212855797 315505594690613176205231)
        ·
          refine ⟨473258392035919764307847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315505594690613176205231 473258392035919764307847)
          ·
            refine ⟨709887588053879646461771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473258392035919764307847 709887588053879646461771)
            ·
              refine ⟨1064831382080819469692657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709887588053879646461771 1064831382080819469692657)
              ·
                refine ⟨798623536560614602269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064831382080819469692657 798623536560614602269493)
                ·
                  refine ⟨74870956552557618962765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 798623536560614602269493 74870956552557618962765)
                  ·
                    rfl

theorem cell21_328074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_328074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328074 prefixEnd_328074 := by exact prefixLift 328074
  have htrace : WordTrace (prefixWord ++ tailWord_328074) baseStart_328074 baseEnd_328074 := by
    simpa [prefixWord, tailWord_328074, baseEnd_328074] using wordTrace_append hprefix tailTrace_328074
  have hstable : (prefixWord ++ tailWord_328074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328074).length < 2 ^ (prefixWord ++ tailWord_328074).sum := by decide
  have hdescent : baseEnd_328074 < baseStart_328074 := by decide
  rcases family_descends (prefixWord ++ tailWord_328074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328181 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_328181 : Nat := 118140960795 + 328181 * 2 ^ 59
def prefixEnd_328181 : Nat := 4983230072969 + 3 ^ 40 * 328181 * 2
def baseEnd_328181 : Nat := 74895375410349210679213

theorem tailTrace_328181 : CollatzResearch.WordTrace tailWord_328181 prefixEnd_328181 74895375410349210679213 := by
  unfold tailWord_328181
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969744424063760697632397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7979829616042507131754931 11969744424063760697632397)
  ·
    refine ⟨4488654159023910261612149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11969744424063760697632397 4488654159023910261612149)
    ·
      refine ⟨420811327408491587026139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4488654159023910261612149 420811327408491587026139)
      ·
        refine ⟨631216991112737380539209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420811327408491587026139 631216991112737380539209)
        ·
          refine ⟨473412743334553035404407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631216991112737380539209 473412743334553035404407)
          ·
            refine ⟨710119115001829553106611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473412743334553035404407 710119115001829553106611)
            ·
              refine ⟨1065178672502744329659917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710119115001829553106611 1065178672502744329659917)
              ·
                refine ⟨399442002188529123622469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1065178672502744329659917 399442002188529123622469)
                ·
                  refine ⟨74895375410349210679213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399442002188529123622469 74895375410349210679213)
                  ·
                    rfl

theorem cell21_328181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_328181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328181 prefixEnd_328181 := by exact prefixLift 328181
  have htrace : WordTrace (prefixWord ++ tailWord_328181) baseStart_328181 baseEnd_328181 := by
    simpa [prefixWord, tailWord_328181, baseEnd_328181] using wordTrace_append hprefix tailTrace_328181
  have hstable : (prefixWord ++ tailWord_328181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328181).length < 2 ^ (prefixWord ++ tailWord_328181).sum := by decide
  have hdescent : baseEnd_328181 < baseStart_328181 := by decide
  rcases family_descends (prefixWord ++ tailWord_328181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328313 : List Nat := [1, 2, 1, 3, 3, 3, 1, 7]
def baseStart_328313 : Nat := 118140960795 + 328313 * 2 ^ 59
def prefixEnd_328313 : Nat := 4983230072969 + 3 ^ 40 * 328313 * 2
def baseEnd_328313 : Nat := 24975166536248771492981

theorem tailTrace_328313 : CollatzResearch.WordTrace tailWord_328313 prefixEnd_328313 24975166536248771492981 := by
  unfold tailWord_328313
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974558859585547241437593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7983039239723698160958395 11974558859585547241437593)
  ·
    refine ⟨8980919144689160431078195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11974558859585547241437593 8980919144689160431078195)
    ·
      refine ⟨13471378717033740646617293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8980919144689160431078195 13471378717033740646617293)
      ·
        refine ⟨5051767018887652742481485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13471378717033740646617293 5051767018887652742481485)
        ·
          refine ⟨1894412632082869778430557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5051767018887652742481485 1894412632082869778430557)
          ·
            refine ⟨710404737031076166911459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1894412632082869778430557 710404737031076166911459)
            ·
              refine ⟨1065607105546614250367189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710404737031076166911459 1065607105546614250367189)
              ·
                refine ⟨24975166536248771492981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1065607105546614250367189 24975166536248771492981)
                ·
                  rfl

theorem cell21_328313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_328313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328313 prefixEnd_328313 := by exact prefixLift 328313
  have htrace : WordTrace (prefixWord ++ tailWord_328313) baseStart_328313 baseEnd_328313 := by
    simpa [prefixWord, tailWord_328313, baseEnd_328313] using wordTrace_append hprefix tailTrace_328313
  have hstable : (prefixWord ++ tailWord_328313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328313).length < 2 ^ (prefixWord ++ tailWord_328313).sum := by decide
  have hdescent : baseEnd_328313 < baseStart_328313 := by decide
  rcases family_descends (prefixWord ++ tailWord_328313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328330 : List Nat := [3, 1, 2, 3, 3, 2, 7]
def baseStart_328330 : Nat := 118140960795 + 328330 * 2 ^ 59
def prefixEnd_328330 : Nat := 4983230072969 + 3 ^ 40 * 328330 * 2
def baseEnd_328330 : Nat := 8325486582262006966175

theorem tailTrace_328330 : CollatzResearch.WordTrace tailWord_328330 prefixEnd_328330 8325486582262006966175 := by
  unfold tailWord_328330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993794725130989786201611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7983452600349306096537629 2993794725130989786201611)
  ·
    refine ⟨4490692087696484679302417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2993794725130989786201611 4490692087696484679302417)
    ·
      refine ⟨3368019065772363509476813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4490692087696484679302417 3368019065772363509476813)
      ·
        refine ⟨1263007149664636316053805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3368019065772363509476813 1263007149664636316053805)
        ·
          refine ⟨473627681124238618520177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1263007149664636316053805 473627681124238618520177)
          ·
            refine ⟨355220760843178963890133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473627681124238618520177 355220760843178963890133)
            ·
              refine ⟨8325486582262006966175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 355220760843178963890133 8325486582262006966175)
              ·
                rfl

theorem cell21_328330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 7].length) (baseStart_328330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328330 prefixEnd_328330 := by exact prefixLift 328330
  have htrace : WordTrace (prefixWord ++ tailWord_328330) baseStart_328330 baseEnd_328330 := by
    simpa [prefixWord, tailWord_328330, baseEnd_328330] using wordTrace_append hprefix tailTrace_328330
  have hstable : (prefixWord ++ tailWord_328330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328330).length < 2 ^ (prefixWord ++ tailWord_328330).sum := by decide
  have hdescent : baseEnd_328330 < baseStart_328330 := by decide
  rcases family_descends (prefixWord ++ tailWord_328330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328420 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_328420 : Nat := 118140960795 + 328420 * 2 ^ 59
def prefixEnd_328420 : Nat := 4983230072969 + 3 ^ 40 * 328420 * 2
def baseEnd_328420 : Nat := 74949918466537906195391

theorem tailTrace_328420 : CollatzResearch.WordTrace tailWord_328420 prefixEnd_328420 74949918466537906195391 := by
  unfold tailWord_328420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989230735098952257791357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7985640980131936343721809 5989230735098952257791357)
  ·
    refine ⟨2245961525662107096671759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5989230735098952257791357 2245961525662107096671759)
    ·
      refine ⟨3368942288493160645007639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2245961525662107096671759 3368942288493160645007639)
      ·
        refine ⟨5053413432739740967511459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368942288493160645007639 5053413432739740967511459)
        ·
          refine ⟨7580120149109611451267189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053413432739740967511459 7580120149109611451267189)
          ·
            refine ⟨710636263979026073556299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7580120149109611451267189 710636263979026073556299)
            ·
              refine ⟨1065954395968539110334449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710636263979026073556299 1065954395968539110334449)
              ·
                refine ⟨799465796976404332750837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065954395968539110334449 799465796976404332750837)
                ·
                  refine ⟨74949918466537906195391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799465796976404332750837 74949918466537906195391)
                  ·
                    rfl

theorem cell21_328420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_328420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328420 prefixEnd_328420 := by exact prefixLift 328420
  have htrace : WordTrace (prefixWord ++ tailWord_328420) baseStart_328420 baseEnd_328420 := by
    simpa [prefixWord, tailWord_328420, baseEnd_328420] using wordTrace_append hprefix tailTrace_328420
  have hstable : (prefixWord ++ tailWord_328420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328420).length < 2 ^ (prefixWord ++ tailWord_328420).sum := by decide
  have hdescent : baseEnd_328420 < baseStart_328420 := by decide
  rcases family_descends (prefixWord ++ tailWord_328420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328482 : List Nat := [3, 3, 1, 1, 2, 2, 4, 5]
def baseStart_328482 : Nat := 118140960795 + 328482 * 2 ^ 59
def prefixEnd_328482 : Nat := 4983230072969 + 3 ^ 40 * 328482 * 2
def baseEnd_328482 : Nat := 24988022570413192053977

theorem tailTrace_328482 : CollatzResearch.WordTrace tailWord_328482 prefixEnd_328482 24988022570413192053977 := by
  unfold tailWord_328482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995180698993322276084925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7987148530648859402893133 2995180698993322276084925)
  ·
    refine ⟨1123192762122495853531847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2995180698993322276084925 1123192762122495853531847)
    ·
      refine ⟨1684789143183743780297771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123192762122495853531847 1684789143183743780297771)
      ·
        refine ⟨2527183714775615670446657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684789143183743780297771 2527183714775615670446657)
        ·
          refine ⟨1895387786081711752834993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527183714775615670446657 1895387786081711752834993)
          ·
            refine ⟨1421540839561283814626245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895387786081711752834993 1421540839561283814626245)
            ·
              refine ⟨266538907417740715242421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1421540839561283814626245 266538907417740715242421)
              ·
                refine ⟨24988022570413192053977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266538907417740715242421 24988022570413192053977)
                ·
                  rfl

theorem cell21_328482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_328482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328482 prefixEnd_328482 := by exact prefixLift 328482
  have htrace : WordTrace (prefixWord ++ tailWord_328482) baseStart_328482 baseEnd_328482 := by
    simpa [prefixWord, tailWord_328482, baseEnd_328482] using wordTrace_append hprefix tailTrace_328482
  have hstable : (prefixWord ++ tailWord_328482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328482).length < 2 ^ (prefixWord ++ tailWord_328482).sum := by decide
  have hdescent : baseEnd_328482 < baseStart_328482 := by decide
  rcases family_descends (prefixWord ++ tailWord_328482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328558 : List Nat := [4, 1, 2, 3, 3, 8]
def baseStart_328558 : Nat := 118140960795 + 328558 * 2 ^ 59
def prefixEnd_328558 : Nat := 4983230072969 + 3 ^ 40 * 328558 * 2
def baseEnd_328558 : Nat := 2777089331358530847967

theorem tailTrace_328558 : CollatzResearch.WordTrace tailWord_328558 prefixEnd_328558 2777089331358530847967 := by
  unfold tailWord_328558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497936842962244260513291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7988996495798636056070885 1497936842962244260513291)
  ·
    refine ⟨2246905264443366390769937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497936842962244260513291 2246905264443366390769937)
    ·
      refine ⟨1685178948332524793077453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2246905264443366390769937 1685178948332524793077453)
      ·
        refine ⟨631942105624696797404045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1685178948332524793077453 631942105624696797404045)
        ·
          refine ⟨236978289609261299026517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 631942105624696797404045 236978289609261299026517)
          ·
            refine ⟨2777089331358530847967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 236978289609261299026517 2777089331358530847967)
            ·
              rfl

theorem cell21_328558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 8].length) (baseStart_328558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328558 prefixEnd_328558 := by exact prefixLift 328558
  have htrace : WordTrace (prefixWord ++ tailWord_328558) baseStart_328558 baseEnd_328558 := by
    simpa [prefixWord, tailWord_328558, baseEnd_328558] using wordTrace_append hprefix tailTrace_328558
  have hstable : (prefixWord ++ tailWord_328558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328558).length < 2 ^ (prefixWord ++ tailWord_328558).sum := by decide
  have hdescent : baseEnd_328558 < baseStart_328558 := by decide
  rcases family_descends (prefixWord ++ tailWord_328558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328631 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_328631 : Nat := 118140960795 + 328631 * 2 ^ 59
def prefixEnd_328631 : Nat := 4983230072969 + 3 ^ 40 * 328631 * 2
def baseEnd_328631 : Nat := 74998071541248428178293

theorem tailTrace_328631 : CollatzResearch.WordTrace tailWord_328631 prefixEnd_328631 74998071541248428178293 := by
  unfold tailWord_328631
  simp only [CollatzResearch.WordTrace]
  refine ⟨11986157272433487551513747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7990771514955658367675831 11986157272433487551513747)
  ·
    refine ⟨17979235908650231327270621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11986157272433487551513747 17979235908650231327270621)
    ·
      refine ⟨6742213465743836747726483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17979235908650231327270621 6742213465743836747726483)
      ·
        refine ⟨10113320198615755121589725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6742213465743836747726483 10113320198615755121589725)
        ·
          refine ⟨3792495074480908170596147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10113320198615755121589725 3792495074480908170596147)
          ·
            refine ⟨5688742611721362255894221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792495074480908170596147 5688742611721362255894221)
            ·
              refine ⟨2133278479395510845960333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5688742611721362255894221 2133278479395510845960333)
              ·
                refine ⟨799979429773316567235125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133278479395510845960333 799979429773316567235125)
                ·
                  refine ⟨74998071541248428178293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799979429773316567235125 74998071541248428178293)
                  ·
                    rfl

theorem cell21_328631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_328631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328631 prefixEnd_328631 := by exact prefixLift 328631
  have htrace : WordTrace (prefixWord ++ tailWord_328631) baseStart_328631 baseEnd_328631 := by
    simpa [prefixWord, tailWord_328631, baseEnd_328631] using wordTrace_append hprefix tailTrace_328631
  have hstable : (prefixWord ++ tailWord_328631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328631).length < 2 ^ (prefixWord ++ tailWord_328631).sum := by decide
  have hdescent : baseEnd_328631 < baseStart_328631 := by decide
  rcases family_descends (prefixWord ++ tailWord_328631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328665 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 3]
def baseStart_328665 : Nat := 118140960795 + 328665 * 2 ^ 59
def prefixEnd_328665 : Nat := 4983230072969 + 3 ^ 40 * 328665 * 2
def baseEnd_328665 : Nat := 75005830804471924611557

theorem tailTrace_328665 : CollatzResearch.WordTrace tailWord_328665 prefixEnd_328665 75005830804471924611557 := by
  unfold tailWord_328665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987397354310311358251449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7991598236206874238834299 11987397354310311358251449)
  ·
    refine ⟨8990548015732733518688587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11987397354310311358251449 8990548015732733518688587)
    ·
      refine ⟨13485822023599100278032881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8990548015732733518688587 13485822023599100278032881)
      ·
        refine ⟨10114366517699325208524661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13485822023599100278032881 10114366517699325208524661)
        ·
          refine ⟨948221861034311738299187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10114366517699325208524661 948221861034311738299187)
          ·
            refine ⟨1422332791551467607448781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948221861034311738299187 1422332791551467607448781)
            ·
              refine ⟨533374796831800352793293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1422332791551467607448781 533374796831800352793293)
              ·
                refine ⟨200015548811925132297485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533374796831800352793293 200015548811925132297485)
                ·
                  refine ⟨75005830804471924611557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200015548811925132297485 75005830804471924611557)
                  ·
                    rfl

theorem cell21_328665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_328665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328665 prefixEnd_328665 := by exact prefixLift 328665
  have htrace : WordTrace (prefixWord ++ tailWord_328665) baseStart_328665 baseEnd_328665 := by
    simpa [prefixWord, tailWord_328665, baseEnd_328665] using wordTrace_append hprefix tailTrace_328665
  have hstable : (prefixWord ++ tailWord_328665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328665).length < 2 ^ (prefixWord ++ tailWord_328665).sum := by decide
  have hdescent : baseEnd_328665 < baseStart_328665 := by decide
  rcases family_descends (prefixWord ++ tailWord_328665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328682 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_328682 : Nat := 118140960795 + 328682 * 2 ^ 59
def prefixEnd_328682 : Nat := 4983230072969 + 3 ^ 40 * 328682 * 2
def baseEnd_328682 : Nat := 75009710436083672828189

theorem tailTrace_328682 : CollatzResearch.WordTrace tailWord_328682 prefixEnd_328682 75009710436083672828189 := by
  unfold tailWord_328682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997004348812180815405075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7992011596832482174413533 2997004348812180815405075)
  ·
    refine ⟨4495506523218271223107613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997004348812180815405075 4495506523218271223107613)
    ·
      refine ⟨1685814946206851708665355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4495506523218271223107613 1685814946206851708665355)
      ·
        refine ⟨2528722419310277562998033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685814946206851708665355 2528722419310277562998033)
        ·
          refine ⟨1896541814482708172248525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2528722419310277562998033 1896541814482708172248525)
          ·
            refine ⟨711203180431015564593197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1896541814482708172248525 711203180431015564593197)
            ·
              refine ⟨266701192661630836722449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711203180431015564593197 266701192661630836722449)
              ·
                refine ⟨200025894496223127541837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266701192661630836722449 200025894496223127541837)
                ·
                  refine ⟨75009710436083672828189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200025894496223127541837 75009710436083672828189)
                  ·
                    rfl

theorem cell21_328682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_328682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328682 prefixEnd_328682 := by exact prefixLift 328682
  have htrace : WordTrace (prefixWord ++ tailWord_328682) baseStart_328682 baseEnd_328682 := by
    simpa [prefixWord, tailWord_328682, baseEnd_328682] using wordTrace_append hprefix tailTrace_328682
  have hstable : (prefixWord ++ tailWord_328682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328682).length < 2 ^ (prefixWord ++ tailWord_328682).sum := by decide
  have hdescent : baseEnd_328682 < baseStart_328682 := by decide
  rcases family_descends (prefixWord ++ tailWord_328682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328721 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_328721 : Nat := 118140960795 + 328721 * 2 ^ 59
def prefixEnd_328721 : Nat := 4983230072969 + 3 ^ 40 * 328721 * 2
def baseEnd_328721 : Nat := 75018610767428271678109

theorem tailTrace_328721 : CollatzResearch.WordTrace tailWord_328721 prefixEnd_328721 75018610767428271678109 := by
  unfold tailWord_328721
  simp only [CollatzResearch.WordTrace]
  refine ⟨11989439842107432922290017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7992959894738288614860011 11989439842107432922290017)
  ·
    refine ⟨8992079881580574691717513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11989439842107432922290017 8992079881580574691717513)
    ·
      refine ⟨6744059911185431018788135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8992079881580574691717513 6744059911185431018788135)
      ·
        refine ⟨10116089866778146528182203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744059911185431018788135 10116089866778146528182203)
        ·
          refine ⟨15174134800167219792273305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10116089866778146528182203 15174134800167219792273305)
          ·
            refine ⟨11380601100125414844204979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15174134800167219792273305 11380601100125414844204979)
            ·
              refine ⟨17070901650188122266307469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11380601100125414844204979 17070901650188122266307469)
              ·
                refine ⟨6401588118820545849865301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17070901650188122266307469 6401588118820545849865301)
                ·
                  refine ⟨75018610767428271678109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6401588118820545849865301 75018610767428271678109)
                  ·
                    rfl

theorem cell21_328721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_328721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328721 prefixEnd_328721 := by exact prefixLift 328721
  have htrace : WordTrace (prefixWord ++ tailWord_328721) baseStart_328721 baseEnd_328721 := by
    simpa [prefixWord, tailWord_328721, baseEnd_328721] using wordTrace_append hprefix tailTrace_328721
  have hstable : (prefixWord ++ tailWord_328721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328721).length < 2 ^ (prefixWord ++ tailWord_328721).sum := by decide
  have hdescent : baseEnd_328721 < baseStart_328721 := by decide
  rcases family_descends (prefixWord ++ tailWord_328721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328800 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_328800 : Nat := 118140960795 + 328800 * 2 ^ 59
def prefixEnd_328800 : Nat := 4983230072969 + 3 ^ 40 * 328800 * 2
def baseEnd_328800 : Nat := 75036639643741689861281

theorem tailTrace_328800 : CollatzResearch.WordTrace tailWord_328800 prefixEnd_328800 75036639643741689861281 := by
  unfold tailWord_328800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996160604410614707207927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7994880805880819609610569 5996160604410614707207927)
  ·
    refine ⟨8994240906615922060811891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996160604410614707207927 8994240906615922060811891)
    ·
      refine ⟨13491361359923883091217837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8994240906615922060811891 13491361359923883091217837)
      ·
        refine ⟨5059260509971456159206689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13491361359923883091217837 5059260509971456159206689)
        ·
          refine ⟨3794445382478592119405017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5059260509971456159206689 3794445382478592119405017)
          ·
            refine ⟨2845834036858944089553763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794445382478592119405017 2845834036858944089553763)
            ·
              refine ⟨4268751055288416134330645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845834036858944089553763 4268751055288416134330645)
              ·
                refine ⟨200097705716644506296749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4268751055288416134330645 200097705716644506296749)
                ·
                  refine ⟨75036639643741689861281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200097705716644506296749 75036639643741689861281)
                  ·
                    rfl

theorem cell21_328800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_328800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328800 prefixEnd_328800 := by exact prefixLift 328800
  have htrace : WordTrace (prefixWord ++ tailWord_328800) baseStart_328800 baseEnd_328800 := by
    simpa [prefixWord, tailWord_328800, baseEnd_328800] using wordTrace_append hprefix tailTrace_328800
  have hstable : (prefixWord ++ tailWord_328800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328800).length < 2 ^ (prefixWord ++ tailWord_328800).sum := by decide
  have hdescent : baseEnd_328800 < baseStart_328800 := by decide
  rcases family_descends (prefixWord ++ tailWord_328800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328828 : List Nat := [2, 2, 2, 1, 1, 3, 3, 7]
def baseStart_328828 : Nat := 118140960795 + 328828 * 2 ^ 59
def prefixEnd_328828 : Nat := 4983230072969 + 3 ^ 40 * 328828 * 2
def baseEnd_328828 : Nat := 25014343208406621131519

theorem tailTrace_328828 : CollatzResearch.WordTrace tailWord_328828 prefixEnd_328828 25014343208406621131519 := by
  unfold tailWord_328828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996671226359895098217569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7995561635146526797623425 5996671226359895098217569)
  ·
    refine ⟨4497503419769921323663177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5996671226359895098217569 4497503419769921323663177)
    ·
      refine ⟨3373127564827440992747383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4497503419769921323663177 3373127564827440992747383)
      ·
        refine ⟨5059691347241161489121075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3373127564827440992747383 5059691347241161489121075)
        ·
          refine ⟨7589537020861742233681613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059691347241161489121075 7589537020861742233681613)
          ·
            refine ⟨2846076382823153337630605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7589537020861742233681613 2846076382823153337630605)
            ·
              refine ⟨1067278643558682501611477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2846076382823153337630605 1067278643558682501611477)
              ·
                refine ⟨25014343208406621131519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1067278643558682501611477 25014343208406621131519)
                ·
                  rfl

theorem cell21_328828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_328828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328828 prefixEnd_328828 := by exact prefixLift 328828
  have htrace : WordTrace (prefixWord ++ tailWord_328828) baseStart_328828 baseEnd_328828 := by
    simpa [prefixWord, tailWord_328828, baseEnd_328828] using wordTrace_append hprefix tailTrace_328828
  have hstable : (prefixWord ++ tailWord_328828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328828).length < 2 ^ (prefixWord ++ tailWord_328828).sum := by decide
  have hdescent : baseEnd_328828 < baseStart_328828 := by decide
  rcases family_descends (prefixWord ++ tailWord_328828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328862 : List Nat := [4, 3, 1, 1, 2, 2, 2, 6]
def baseStart_328862 : Nat := 118140960795 + 328862 * 2 ^ 59
def prefixEnd_328862 : Nat := 4983230072969 + 3 ^ 40 * 328862 * 2
def baseEnd_328862 : Nat := 25016929629481119942607

theorem tailTrace_328862 : CollatzResearch.WordTrace tailWord_328862 prefixEnd_328862 25016929629481119942607 := by
  unfold tailWord_328862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499322816824576750396605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7996388356397742668781893 1499322816824576750396605)
  ·
    refine ⟨562246056309216281398727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1499322816824576750396605 562246056309216281398727)
    ·
      refine ⟨843369084463824422098091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562246056309216281398727 843369084463824422098091)
      ·
        refine ⟨1265053626695736633147137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843369084463824422098091 1265053626695736633147137)
        ·
          refine ⟨948790220021802474860353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265053626695736633147137 948790220021802474860353)
          ·
            refine ⟨711592665016351856145265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948790220021802474860353 711592665016351856145265)
            ·
              refine ⟨533694498762263892108949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711592665016351856145265 533694498762263892108949)
              ·
                refine ⟨25016929629481119942607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 533694498762263892108949 25016929629481119942607)
                ·
                  rfl

theorem cell21_328862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_328862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328862 prefixEnd_328862 := by exact prefixLift 328862
  have htrace : WordTrace (prefixWord ++ tailWord_328862) baseStart_328862 baseEnd_328862 := by
    simpa [prefixWord, tailWord_328862, baseEnd_328862] using wordTrace_append hprefix tailTrace_328862
  have hstable : (prefixWord ++ tailWord_328862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328862).length < 2 ^ (prefixWord ++ tailWord_328862).sum := by decide
  have hdescent : baseEnd_328862 < baseStart_328862 := by decide
  rcases family_descends (prefixWord ++ tailWord_328862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328902 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_328902 : Nat := 118140960795 + 328902 * 2 ^ 59
def prefixEnd_328902 : Nat := 4983230072969 + 3 ^ 40 * 328902 * 2
def baseEnd_328902 : Nat := 75059917433412179161073

theorem tailTrace_328902 : CollatzResearch.WordTrace tailWord_328902 prefixEnd_328902 75059917433412179161073 := by
  unfold tailWord_328902
  simp only [CollatzResearch.WordTrace]
  refine ⟨374876295451615651082155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7997360969634467223085973 374876295451615651082155)
  ·
    refine ⟨562314443177423476623233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374876295451615651082155 562314443177423476623233)
    ·
      refine ⟨421735832383067607467425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562314443177423476623233 421735832383067607467425)
      ·
        refine ⟨316301874287300705600569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421735832383067607467425 316301874287300705600569)
        ·
          refine ⟨237226405715475529200427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316301874287300705600569 237226405715475529200427)
          ·
            refine ⟨355839608573213293800641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237226405715475529200427 355839608573213293800641)
            ·
              refine ⟨266879706429909970350481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355839608573213293800641 266879706429909970350481)
              ·
                refine ⟨200159779822432477762861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266879706429909970350481 200159779822432477762861)
                ·
                  refine ⟨75059917433412179161073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200159779822432477762861 75059917433412179161073)
                  ·
                    rfl

theorem cell21_328902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_328902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328902 prefixEnd_328902 := by exact prefixLift 328902
  have htrace : WordTrace (prefixWord ++ tailWord_328902) baseStart_328902 baseEnd_328902 := by
    simpa [prefixWord, tailWord_328902, baseEnd_328902] using wordTrace_append hprefix tailTrace_328902
  have hstable : (prefixWord ++ tailWord_328902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328902).length < 2 ^ (prefixWord ++ tailWord_328902).sum := by decide
  have hdescent : baseEnd_328902 < baseStart_328902 := by decide
  rcases family_descends (prefixWord ++ tailWord_328902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328983 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 4]
def baseStart_328983 : Nat := 118140960795 + 328983 * 2 ^ 59
def prefixEnd_328983 : Nat := 4983230072969 + 3 ^ 40 * 328983 * 2
def baseEnd_328983 : Nat := 75078402736974038310907

theorem tailTrace_328983 : CollatzResearch.WordTrace tailWord_328983 prefixEnd_328983 75078402736974038310907 := by
  unfold tailWord_328983
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998995767158251668327603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7999330511438834445551735 11998995767158251668327603)
  ·
    refine ⟨17998493650737377502491405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11998995767158251668327603 17998493650737377502491405)
    ·
      refine ⟨6749435119026516563434277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17998493650737377502491405 6749435119026516563434277)
      ·
        refine ⟨1265519084817471855643927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6749435119026516563434277 1265519084817471855643927)
        ·
          refine ⟨1898278627226207783465891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265519084817471855643927 1898278627226207783465891)
          ·
            refine ⟨2847417940839311675198837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898278627226207783465891 2847417940839311675198837)
            ·
              refine ⟨266945431953685469549891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2847417940839311675198837 266945431953685469549891)
              ·
                refine ⟨400418147930528204324837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266945431953685469549891 400418147930528204324837)
                ·
                  refine ⟨75078402736974038310907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400418147930528204324837 75078402736974038310907)
                  ·
                    rfl

theorem cell21_328983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4].length) (baseStart_328983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328983 prefixEnd_328983 := by exact prefixLift 328983
  have htrace : WordTrace (prefixWord ++ tailWord_328983) baseStart_328983 baseEnd_328983 := by
    simpa [prefixWord, tailWord_328983, baseEnd_328983] using wordTrace_append hprefix tailTrace_328983
  have hstable : (prefixWord ++ tailWord_328983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328983).length < 2 ^ (prefixWord ++ tailWord_328983).sum := by decide
  have hdescent : baseEnd_328983 < baseStart_328983 := by decide
  rcases family_descends (prefixWord ++ tailWord_328983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328997 : List Nat := [1, 3, 1, 2, 4, 1, 4, 5]
def baseStart_328997 : Nat := 118140960795 + 328997 * 2 ^ 59
def prefixEnd_328997 : Nat := 4983230072969 + 3 ^ 40 * 328997 * 2
def baseEnd_328997 : Nat := 25027199242571041692515

theorem tailTrace_328997 : CollatzResearch.WordTrace tailWord_328997 prefixEnd_328997 25027199242571041692515 := by
  unfold tailWord_328997
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999506389107532059337245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7999670926071688039558163 11999506389107532059337245)
  ·
    refine ⟨4499814895915324522251467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11999506389107532059337245 4499814895915324522251467)
    ·
      refine ⟨6749722343872986783377201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499814895915324522251467 6749722343872986783377201)
      ·
        refine ⟨5062291757904740087532901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6749722343872986783377201 5062291757904740087532901)
        ·
          refine ⟨949179704607138766412419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5062291757904740087532901 949179704607138766412419)
          ·
            refine ⟨1423769556910708149618629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949179704607138766412419 1423769556910708149618629)
            ·
              refine ⟨266956791920757778053493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1423769556910708149618629 266956791920757778053493)
              ·
                refine ⟨25027199242571041692515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266956791920757778053493 25027199242571041692515)
                ·
                  rfl

theorem cell21_328997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 5].length) (baseStart_328997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_328997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_328997 prefixEnd_328997 := by exact prefixLift 328997
  have htrace : WordTrace (prefixWord ++ tailWord_328997) baseStart_328997 baseEnd_328997 := by
    simpa [prefixWord, tailWord_328997, baseEnd_328997] using wordTrace_append hprefix tailTrace_328997
  have hstable : (prefixWord ++ tailWord_328997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328997).length < 2 ^ (prefixWord ++ tailWord_328997).sum := by decide
  have hdescent : baseEnd_328997 < baseStart_328997 := by decide
  rcases family_descends (prefixWord ++ tailWord_328997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329056 : List Nat := [2, 1, 1, 3, 4, 1, 2, 7]
def baseStart_329056 : Nat := 118140960795 + 329056 * 2 ^ 59
def prefixEnd_329056 : Nat := 4983230072969 + 3 ^ 40 * 329056 * 2
def baseEnd_329056 : Nat := 25031687443847377864697

theorem tailTrace_329056 : CollatzResearch.WordTrace tailWord_329056 prefixEnd_329056 25031687443847377864697 := by
  unfold tailWord_329056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000829147946892567867511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8001105530595856757156681 6000829147946892567867511)
  ·
    refine ⟨9001243721920338851801267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6000829147946892567867511 9001243721920338851801267)
    ·
      refine ⟨13501865582880508277701901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001243721920338851801267 13501865582880508277701901)
      ·
        refine ⟨5063199593580190604138213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13501865582880508277701901 5063199593580190604138213)
        ·
          refine ⟨949349923796285738275915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5063199593580190604138213 949349923796285738275915)
          ·
            refine ⟨1424024885694428607413873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949349923796285738275915 1424024885694428607413873)
            ·
              refine ⟨1068018664270821455560405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424024885694428607413873 1068018664270821455560405)
              ·
                refine ⟨25031687443847377864697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1068018664270821455560405 25031687443847377864697)
                ·
                  rfl

theorem cell21_329056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_329056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329056 prefixEnd_329056 := by exact prefixLift 329056
  have htrace : WordTrace (prefixWord ++ tailWord_329056) baseStart_329056 baseEnd_329056 := by
    simpa [prefixWord, tailWord_329056, baseEnd_329056] using wordTrace_append hprefix tailTrace_329056
  have hstable : (prefixWord ++ tailWord_329056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329056).length < 2 ^ (prefixWord ++ tailWord_329056).sum := by decide
  have hdescent : baseEnd_329056 < baseStart_329056 := by decide
  rcases family_descends (prefixWord ++ tailWord_329056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329090 : List Nat := [3, 4, 2, 1, 1, 1, 3, 6]
def baseStart_329090 : Nat := 118140960795 + 329090 * 2 ^ 59
def prefixEnd_329090 : Nat := 4983230072969 + 3 ^ 40 * 329090 * 2
def baseEnd_329090 : Nat := 25034273864921876675785

theorem tailTrace_329090 : CollatzResearch.WordTrace tailWord_329090 prefixEnd_329090 25034273864921876675785 := by
  unfold tailWord_329090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3000724594442652235618181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8001932251847072628315149 3000724594442652235618181)
  ·
    refine ⟨562635861457997294178409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3000724594442652235618181 562635861457997294178409)
    ·
      refine ⟨421976896093497970633807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562635861457997294178409 421976896093497970633807)
      ·
        refine ⟨632965344140246955950711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421976896093497970633807 632965344140246955950711)
        ·
          refine ⟨949448016210370433926067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632965344140246955950711 949448016210370433926067)
          ·
            refine ⟨1424172024315555650889101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949448016210370433926067 1424172024315555650889101)
            ·
              refine ⟨534064509118333369083413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1424172024315555650889101 534064509118333369083413)
              ·
                refine ⟨25034273864921876675785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 534064509118333369083413 25034273864921876675785)
                ·
                  rfl

theorem cell21_329090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_329090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329090 prefixEnd_329090 := by exact prefixLift 329090
  have htrace : WordTrace (prefixWord ++ tailWord_329090) baseStart_329090 baseEnd_329090 := by
    simpa [prefixWord, tailWord_329090, baseEnd_329090] using wordTrace_append hprefix tailTrace_329090
  have hstable : (prefixWord ++ tailWord_329090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329090).length < 2 ^ (prefixWord ++ tailWord_329090).sum := by decide
  have hdescent : baseEnd_329090 < baseStart_329090 := by decide
  rcases family_descends (prefixWord ++ tailWord_329090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329177 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_329177 : Nat := 118140960795 + 329177 * 2 ^ 59
def prefixEnd_329177 : Nat := 4983230072969 + 3 ^ 40 * 329177 * 2
def baseEnd_329177 : Nat := 75122676180072812077177

theorem tailTrace_329177 : CollatzResearch.WordTrace tailWord_329177 prefixEnd_329177 75122676180072812077177 := by
  unfold tailWord_329177
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006071528455422800889785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8004047685636948533926523 12006071528455422800889785)
  ·
    refine ⟨9004553646341567100667339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12006071528455422800889785 9004553646341567100667339)
    ·
      refine ⟨13506830469512350651001009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9004553646341567100667339 13506830469512350651001009)
      ·
        refine ⟨10130122852134262988250757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13506830469512350651001009 10130122852134262988250757)
        ·
          refine ⟨1899398034775174310297017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10130122852134262988250757 1899398034775174310297017)
          ·
            refine ⟨1424548526081380732722763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899398034775174310297017 1424548526081380732722763)
            ·
              refine ⟨2136822789122071099084145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424548526081380732722763 2136822789122071099084145)
              ·
                refine ⟨1602617091841553324313109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136822789122071099084145 1602617091841553324313109)
                ·
                  refine ⟨75122676180072812077177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1602617091841553324313109 75122676180072812077177)
                  ·
                    rfl

theorem cell21_329177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_329177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329177 prefixEnd_329177 := by exact prefixLift 329177
  have htrace : WordTrace (prefixWord ++ tailWord_329177) baseStart_329177 baseEnd_329177 := by
    simpa [prefixWord, tailWord_329177, baseEnd_329177] using wordTrace_append hprefix tailTrace_329177
  have hstable : (prefixWord ++ tailWord_329177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329177).length < 2 ^ (prefixWord ++ tailWord_329177).sum := by decide
  have hdescent : baseEnd_329177 < baseStart_329177 := by decide
  rcases family_descends (prefixWord ++ tailWord_329177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329197 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 5]
def baseStart_329197 : Nat := 118140960795 + 329197 * 2 ^ 59
def prefixEnd_329197 : Nat := 4983230072969 + 3 ^ 40 * 329197 * 2
def baseEnd_329197 : Nat := 75127240452557221743803

theorem tailTrace_329197 : CollatzResearch.WordTrace tailWord_329197 prefixEnd_329197 75127240452557221743803 := by
  unfold tailWord_329197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006800988382966216617845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8004533992255310811078563 12006800988382966216617845)
  ·
    refine ⟨1125637592660903082807923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12006800988382966216617845 1125637592660903082807923)
    ·
      refine ⟨1688456388991354624211885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125637592660903082807923 1688456388991354624211885)
      ·
        refine ⟨633171145871757984079457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1688456388991354624211885 633171145871757984079457)
        ·
          refine ⟨474878359403818488059593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633171145871757984079457 474878359403818488059593)
          ·
            refine ⟨356158769552863866044695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474878359403818488059593 356158769552863866044695)
            ·
              refine ⟨534238154329295799067043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356158769552863866044695 534238154329295799067043)
              ·
                refine ⟨801357231493943698600565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534238154329295799067043 801357231493943698600565)
                ·
                  refine ⟨75127240452557221743803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801357231493943698600565 75127240452557221743803)
                  ·
                    rfl

theorem cell21_329197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_329197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329197 prefixEnd_329197 := by exact prefixLift 329197
  have htrace : WordTrace (prefixWord ++ tailWord_329197) baseStart_329197 baseEnd_329197 := by
    simpa [prefixWord, tailWord_329197, baseEnd_329197] using wordTrace_append hprefix tailTrace_329197
  have hstable : (prefixWord ++ tailWord_329197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329197).length < 2 ^ (prefixWord ++ tailWord_329197).sum := by decide
  have hdescent : baseEnd_329197 < baseStart_329197 := by decide
  rcases family_descends (prefixWord ++ tailWord_329197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329208 : List Nat := [2, 1, 2, 1, 1, 6, 2, 6]
def baseStart_329208 : Nat := 118140960795 + 329208 * 2 ^ 59
def prefixEnd_329208 : Nat := 4983230072969 + 3 ^ 40 * 329208 * 2
def baseEnd_329208 : Nat := 25043250267474549020149

theorem tailTrace_329208 : CollatzResearch.WordTrace tailWord_329208 prefixEnd_329208 25043250267474549020149 := by
  unfold tailWord_329208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6003601095671557547634139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8004801460895410063512185 6003601095671557547634139)
  ·
    refine ⟨9005401643507336321451209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6003601095671557547634139 9005401643507336321451209)
    ·
      refine ⟨6754051232630502241088407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9005401643507336321451209 6754051232630502241088407)
      ·
        refine ⟨10131076848945753361632611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754051232630502241088407 10131076848945753361632611)
        ·
          refine ⟨15196615273418630042448917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10131076848945753361632611 15196615273418630042448917)
          ·
            refine ⟨712341340941498283239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15196615273418630042448917 712341340941498283239793)
            ·
              refine ⟨534256005706123712429845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712341340941498283239793 534256005706123712429845)
              ·
                refine ⟨25043250267474549020149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 534256005706123712429845 25043250267474549020149)
                ·
                  rfl

theorem cell21_329208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_329208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329208 prefixEnd_329208 := by exact prefixLift 329208
  have htrace : WordTrace (prefixWord ++ tailWord_329208) baseStart_329208 baseEnd_329208 := by
    simpa [prefixWord, tailWord_329208, baseEnd_329208] using wordTrace_append hprefix tailTrace_329208
  have hstable : (prefixWord ++ tailWord_329208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329208).length < 2 ^ (prefixWord ++ tailWord_329208).sum := by decide
  have hdescent : baseEnd_329208 < baseStart_329208 := by decide
  rcases family_descends (prefixWord ++ tailWord_329208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329315 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_329315 : Nat := 118140960795 + 329315 * 2 ^ 59
def prefixEnd_329315 : Nat := 4983230072969 + 3 ^ 40 * 329315 * 2
def baseEnd_329315 : Nat := 75154169660215238776895

theorem tailTrace_329315 : CollatzResearch.WordTrace tailWord_329315 prefixEnd_329315 75154169660215238776895 := by
  unfold tailWord_329315
  simp only [CollatzResearch.WordTrace]
  refine ⟨12011104801955472369413399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8007403201303648246275599 12011104801955472369413399)
  ·
    refine ⟨18016657202933208554120099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12011104801955472369413399 18016657202933208554120099)
    ·
      refine ⟨27024985804399812831180149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18016657202933208554120099 27024985804399812831180149)
      ·
        refine ⟨2533592419162482452923139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27024985804399812831180149 2533592419162482452923139)
        ·
          refine ⟨3800388628743723679384709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533592419162482452923139 3800388628743723679384709)
          ·
            refine ⟨712572867889448189884633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3800388628743723679384709 712572867889448189884633)
            ·
              refine ⟨534429650917086142413475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712572867889448189884633 534429650917086142413475)
              ·
                refine ⟨801644476375629213620213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534429650917086142413475 801644476375629213620213)
                ·
                  refine ⟨75154169660215238776895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801644476375629213620213 75154169660215238776895)
                  ·
                    rfl

theorem cell21_329315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_329315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329315 prefixEnd_329315 := by exact prefixLift 329315
  have htrace : WordTrace (prefixWord ++ tailWord_329315) baseStart_329315 baseEnd_329315 := by
    simpa [prefixWord, tailWord_329315, baseEnd_329315] using wordTrace_append hprefix tailTrace_329315
  have hstable : (prefixWord ++ tailWord_329315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329315).length < 2 ^ (prefixWord ++ tailWord_329315).sum := by decide
  have hdescent : baseEnd_329315 < baseStart_329315 := by decide
  rcases family_descends (prefixWord ++ tailWord_329315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329329 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_329329 : Nat := 118140960795 + 329329 * 2 ^ 59
def prefixEnd_329329 : Nat := 4983230072969 + 3 ^ 40 * 329329 * 2
def baseEnd_329329 : Nat := 75157364650954325543533

theorem tailTrace_329329 : CollatzResearch.WordTrace tailWord_329329 prefixEnd_329329 75157364650954325543533 := by
  unfold tailWord_329329
  simp only [CollatzResearch.WordTrace]
  refine ⟨12011615423904752760423041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8007743615936501840282027 12011615423904752760423041)
  ·
    refine ⟨9008711567928564570317281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12011615423904752760423041 9008711567928564570317281)
    ·
      refine ⟨6756533675946423427737961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9008711567928564570317281 6756533675946423427737961)
      ·
        refine ⟨5067400256959817570803471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756533675946423427737961 5067400256959817570803471)
        ·
          refine ⟨7601100385439726356205207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067400256959817570803471 7601100385439726356205207)
          ·
            refine ⟨11401650578159589534307811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601100385439726356205207 11401650578159589534307811)
            ·
              refine ⟨17102475867239384301461717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401650578159589534307811 17102475867239384301461717)
              ·
                refine ⟨400839278138423069565509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17102475867239384301461717 400839278138423069565509)
                ·
                  refine ⟨75157364650954325543533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400839278138423069565509 75157364650954325543533)
                  ·
                    rfl

theorem cell21_329329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_329329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329329 prefixEnd_329329 := by exact prefixLift 329329
  have htrace : WordTrace (prefixWord ++ tailWord_329329) baseStart_329329 baseEnd_329329 := by
    simpa [prefixWord, tailWord_329329, baseEnd_329329] using wordTrace_append hprefix tailTrace_329329
  have hstable : (prefixWord ++ tailWord_329329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329329).length < 2 ^ (prefixWord ++ tailWord_329329).sum := by decide
  have hdescent : baseEnd_329329 < baseStart_329329 := by decide
  rcases family_descends (prefixWord ++ tailWord_329329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329422 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_329422 : Nat := 118140960795 + 329422 * 2 ^ 59
def prefixEnd_329422 : Nat := 4983230072969 + 3 ^ 40 * 329422 * 2
def baseEnd_329422 : Nat := 75178588518006830493343

theorem tailTrace_329422 : CollatzResearch.WordTrace tailWord_329422 prefixEnd_329422 75178588518006830493343 := by
  unfold tailWord_329422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501875926570978705444815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8010004941711886429039013 1501875926570978705444815)
  ·
    refine ⟨2252813889856468058167223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501875926570978705444815 2252813889856468058167223)
    ·
      refine ⟨3379220834784702087250835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252813889856468058167223 3379220834784702087250835)
      ·
        refine ⟨5068831252177053130876253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379220834784702087250835 5068831252177053130876253)
        ·
          refine ⟨1900811719566394924078595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5068831252177053130876253 1900811719566394924078595)
          ·
            refine ⟨2851217579349592386117893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900811719566394924078595 2851217579349592386117893)
            ·
              refine ⟨534603296128048572397105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2851217579349592386117893 534603296128048572397105)
              ·
                refine ⟨400952472096036429297829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534603296128048572397105 400952472096036429297829)
                ·
                  refine ⟨75178588518006830493343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400952472096036429297829 75178588518006830493343)
                  ·
                    rfl

theorem cell21_329422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_329422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329422 prefixEnd_329422 := by exact prefixLift 329422
  have htrace : WordTrace (prefixWord ++ tailWord_329422) baseStart_329422 baseEnd_329422 := by
    simpa [prefixWord, tailWord_329422, baseEnd_329422] using wordTrace_append hprefix tailTrace_329422
  have hstable : (prefixWord ++ tailWord_329422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329422).length < 2 ^ (prefixWord ++ tailWord_329422).sum := by decide
  have hdescent : baseEnd_329422 < baseStart_329422 := by decide
  rcases family_descends (prefixWord ++ tailWord_329422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329425 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 3]
def baseStart_329425 : Nat := 118140960795 + 329425 * 2 ^ 59
def prefixEnd_329425 : Nat := 4983230072969 + 3 ^ 40 * 329425 * 2
def baseEnd_329425 : Nat := 75179273158879491943337

theorem tailTrace_329425 : CollatzResearch.WordTrace tailWord_329425 prefixEnd_329425 75179273158879491943337 := by
  unfold tailWord_329425
  simp only [CollatzResearch.WordTrace]
  refine ⟨12015116831556961155917729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8010077887704640770611819 12015116831556961155917729)
  ·
    refine ⟨9011337623667720866938297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12015116831556961155917729 9011337623667720866938297)
    ·
      refine ⟨6758503217750790650203723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9011337623667720866938297 6758503217750790650203723)
      ·
        refine ⟨10137754826626185975305585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758503217750790650203723 10137754826626185975305585)
        ·
          refine ⟨7603316119969639481479189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10137754826626185975305585 7603316119969639481479189)
          ·
            refine ⟨356405443123576850694337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7603316119969639481479189 356405443123576850694337)
            ·
              refine ⟨267304082342682638020753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356405443123576850694337 267304082342682638020753)
              ·
                refine ⟨200478061757011978515565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267304082342682638020753 200478061757011978515565)
                ·
                  refine ⟨75179273158879491943337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200478061757011978515565 75179273158879491943337)
                  ·
                    rfl

theorem cell21_329425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_329425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329425 prefixEnd_329425 := by exact prefixLift 329425
  have htrace : WordTrace (prefixWord ++ tailWord_329425) baseStart_329425 baseEnd_329425 := by
    simpa [prefixWord, tailWord_329425, baseEnd_329425] using wordTrace_append hprefix tailTrace_329425
  have hstable : (prefixWord ++ tailWord_329425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329425).length < 2 ^ (prefixWord ++ tailWord_329425).sum := by decide
  have hdescent : baseEnd_329425 < baseStart_329425 := by decide
  rcases family_descends (prefixWord ++ tailWord_329425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329450 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_329450 : Nat := 118140960795 + 329450 * 2 ^ 59
def prefixEnd_329450 : Nat := 4983230072969 + 3 ^ 40 * 329450 * 2
def baseEnd_329450 : Nat := 75184978499485004026619

theorem tailTrace_329450 : CollatzResearch.WordTrace tailWord_329450 prefixEnd_329450 75184978499485004026619 := by
  unfold tailWord_329450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004007164116597606394451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8010685770977593617051869 3004007164116597606394451)
  ·
    refine ⟨4506010746174896409591677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3004007164116597606394451 4506010746174896409591677)
    ·
      refine ⟨1689754029815586153596879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4506010746174896409591677 1689754029815586153596879)
      ·
        refine ⟨2534631044723379230395319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689754029815586153596879 2534631044723379230395319)
        ·
          refine ⟨3801946567085068845592979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534631044723379230395319 3801946567085068845592979)
          ·
            refine ⟨5702919850627603268389469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801946567085068845592979 5702919850627603268389469)
            ·
              refine ⟨2138594943985351225646051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5702919850627603268389469 2138594943985351225646051)
              ·
                refine ⟨3207892415978026838469077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138594943985351225646051 3207892415978026838469077)
                ·
                  refine ⟨75184978499485004026619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3207892415978026838469077 75184978499485004026619)
                  ·
                    rfl

theorem cell21_329450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_329450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329450 prefixEnd_329450 := by exact prefixLift 329450
  have htrace : WordTrace (prefixWord ++ tailWord_329450) baseStart_329450 baseEnd_329450 := by
    simpa [prefixWord, tailWord_329450, baseEnd_329450] using wordTrace_append hprefix tailTrace_329450
  have hstable : (prefixWord ++ tailWord_329450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329450).length < 2 ^ (prefixWord ++ tailWord_329450).sum := by decide
  have hdescent : baseEnd_329450 < baseStart_329450 := by decide
  rcases family_descends (prefixWord ++ tailWord_329450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329453 : List Nat := [1, 5, 1, 2, 1, 3, 3, 5]
def baseStart_329453 : Nat := 118140960795 + 329453 * 2 ^ 59
def prefixEnd_329453 : Nat := 4983230072969 + 3 ^ 40 * 329453 * 2
def baseEnd_329453 : Nat := 25061887713452555158871

theorem tailTrace_329453 : CollatzResearch.WordTrace tailWord_329453 prefixEnd_329453 25061887713452555158871 := by
  unfold tailWord_329453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016138075455521937937013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8010758716970347958624675 12016138075455521937937013)
  ·
    refine ⟨1126512944573955181681595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12016138075455521937937013 1126512944573955181681595)
    ·
      refine ⟨1689769416860932772522393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126512944573955181681595 1689769416860932772522393)
      ·
        refine ⟨1267327062645699579391795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689769416860932772522393 1267327062645699579391795)
        ·
          refine ⟨1900990593968549369087693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267327062645699579391795 1900990593968549369087693)
          ·
            refine ⟨712871472738206013407885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1900990593968549369087693 712871472738206013407885)
            ·
              refine ⟨267326802276827255027957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 712871472738206013407885 267326802276827255027957)
              ·
                refine ⟨25061887713452555158871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267326802276827255027957 25061887713452555158871)
                ·
                  rfl

theorem cell21_329453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 5].length) (baseStart_329453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329453 prefixEnd_329453 := by exact prefixLift 329453
  have htrace : WordTrace (prefixWord ++ tailWord_329453) baseStart_329453 baseEnd_329453 := by
    simpa [prefixWord, tailWord_329453, baseEnd_329453] using wordTrace_append hprefix tailTrace_329453
  have hstable : (prefixWord ++ tailWord_329453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329453).length < 2 ^ (prefixWord ++ tailWord_329453).sum := by decide
  have hdescent : baseEnd_329453 < baseStart_329453 := by decide
  rcases family_descends (prefixWord ++ tailWord_329453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329512 : List Nat := [2, 1, 5, 1, 1, 3, 1, 7]
def baseStart_329512 : Nat := 118140960795 + 329512 * 2 ^ 59
def prefixEnd_329512 : Nat := 4983230072969 + 3 ^ 40 * 329512 * 2
def baseEnd_329512 : Nat := 25066375914728891331053

theorem tailTrace_329512 : CollatzResearch.WordTrace tailWord_329512 prefixEnd_329512 25066375914728891331053 := by
  unfold tailWord_329512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6009144991120887507167395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8012193321494516676223193 6009144991120887507167395)
  ·
    refine ⟨9013717486681331260751093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6009144991120887507167395 9013717486681331260751093)
    ·
      refine ⟨845036014376374805695415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9013717486681331260751093 845036014376374805695415)
      ·
        refine ⟨1267554021564562208543123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845036014376374805695415 1267554021564562208543123)
        ·
          refine ⟨1901331032346843312814685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267554021564562208543123 1901331032346843312814685)
          ·
            refine ⟨712999137130066242305507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1901331032346843312814685 712999137130066242305507)
            ·
              refine ⟨1069498705695099363458261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712999137130066242305507 1069498705695099363458261)
              ·
                refine ⟨25066375914728891331053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1069498705695099363458261 25066375914728891331053)
                ·
                  rfl

theorem cell21_329512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_329512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329512 prefixEnd_329512 := by exact prefixLift 329512
  have htrace : WordTrace (prefixWord ++ tailWord_329512) baseStart_329512 baseEnd_329512 := by
    simpa [prefixWord, tailWord_329512, baseEnd_329512] using wordTrace_append hprefix tailTrace_329512
  have hstable : (prefixWord ++ tailWord_329512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329512).length < 2 ^ (prefixWord ++ tailWord_329512).sum := by decide
  have hdescent : baseEnd_329512 < baseStart_329512 := by decide
  rcases family_descends (prefixWord ++ tailWord_329512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329518 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_329518 : Nat := 118140960795 + 329518 * 2 ^ 59
def prefixEnd_329518 : Nat := 4983230072969 + 3 ^ 40 * 329518 * 2
def baseEnd_329518 : Nat := 75200497025931996893147

theorem tailTrace_329518 : CollatzResearch.WordTrace tailWord_329518 prefixEnd_329518 75200497025931996893147 := by
  unfold tailWord_329518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502313602527504754881651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8012339213480025359368805 1502313602527504754881651)
  ·
    refine ⟨2253470403791257132322477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502313602527504754881651 2253470403791257132322477)
    ·
      refine ⟨845051401421721424620929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2253470403791257132322477 845051401421721424620929)
      ·
        refine ⟨633788551066291068465697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845051401421721424620929 633788551066291068465697)
        ·
          refine ⟨475341413299718301349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633788551066291068465697 475341413299718301349273)
          ·
            refine ⟨356506059974788726011955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475341413299718301349273 356506059974788726011955)
            ·
              refine ⟨534759089962183089017933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356506059974788726011955 534759089962183089017933)
              ·
                refine ⟨200534658735818658381725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534759089962183089017933 200534658735818658381725)
                ·
                  refine ⟨75200497025931996893147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200534658735818658381725 75200497025931996893147)
                  ·
                    rfl

theorem cell21_329518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_329518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329518 prefixEnd_329518 := by exact prefixLift 329518
  have htrace : WordTrace (prefixWord ++ tailWord_329518) baseStart_329518 baseEnd_329518 := by
    simpa [prefixWord, tailWord_329518, baseEnd_329518] using wordTrace_append hprefix tailTrace_329518
  have hstable : (prefixWord ++ tailWord_329518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329518).length < 2 ^ (prefixWord ++ tailWord_329518).sum := by decide
  have hdescent : baseEnd_329518 < baseStart_329518 := by decide
  rcases family_descends (prefixWord ++ tailWord_329518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329529 : List Nat := [1, 2, 1, 7, 1, 2, 7]
def baseStart_329529 : Nat := 118140960795 + 329529 * 2 ^ 59
def prefixEnd_329529 : Nat := 4983230072969 + 3 ^ 40 * 329529 * 2
def baseEnd_329529 : Nat := 8355889708422046912199

theorem tailTrace_329529 : CollatzResearch.WordTrace tailWord_329529 prefixEnd_329529 8355889708422046912199 := by
  unfold tailWord_329529
  simp only [CollatzResearch.WordTrace]
  refine ⟨12018910023180186917703641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8012606682120124611802427 12018910023180186917703641)
  ·
    refine ⟨9014182517385140188277731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12018910023180186917703641 9014182517385140188277731)
    ·
      refine ⟨13521273776077710282416597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9014182517385140188277731 13521273776077710282416597)
      ·
        refine ⟨316904854126821334744139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13521273776077710282416597 316904854126821334744139)
        ·
          refine ⟨475357281190232002116209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316904854126821334744139 475357281190232002116209)
          ·
            refine ⟨356517960892674001587157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475357281190232002116209 356517960892674001587157)
            ·
              refine ⟨8355889708422046912199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 356517960892674001587157 8355889708422046912199)
              ·
                rfl

theorem cell21_329529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 7].length) (baseStart_329529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329529 prefixEnd_329529 := by exact prefixLift 329529
  have htrace : WordTrace (prefixWord ++ tailWord_329529) baseStart_329529 baseEnd_329529 := by
    simpa [prefixWord, tailWord_329529, baseEnd_329529] using wordTrace_append hprefix tailTrace_329529
  have hstable : (prefixWord ++ tailWord_329529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329529).length < 2 ^ (prefixWord ++ tailWord_329529).sum := by decide
  have hdescent : baseEnd_329529 < baseStart_329529 := by decide
  rcases family_descends (prefixWord ++ tailWord_329529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329543 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 3]
def baseStart_329543 : Nat := 118140960795 + 329543 * 2 ^ 59
def prefixEnd_329543 : Nat := 4983230072969 + 3 ^ 40 * 329543 * 2
def baseEnd_329543 : Nat := 75206202366537508976429

theorem tailTrace_329543 : CollatzResearch.WordTrace tailWord_329543 prefixEnd_329543 75206202366537508976429 := by
  unfold tailWord_329543
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019420645129467308713283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8012947096752978205808855 12019420645129467308713283)
  ·
    refine ⟨18029130967694200963069925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12019420645129467308713283 18029130967694200963069925)
    ·
      refine ⟨3380462056442662680575611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18029130967694200963069925 3380462056442662680575611)
      ·
        refine ⟨5070693084663994020863417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380462056442662680575611 5070693084663994020863417)
        ·
          refine ⟨3803019813497995515647563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5070693084663994020863417 3803019813497995515647563)
          ·
            refine ⟨5704529720246993273471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803019813497995515647563 5704529720246993273471345)
            ·
              refine ⟨4278397290185244955103509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5704529720246993273471345 4278397290185244955103509)
              ·
                refine ⟨200549872977433357270477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4278397290185244955103509 200549872977433357270477)
                ·
                  refine ⟨75206202366537508976429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200549872977433357270477 75206202366537508976429)
                  ·
                    rfl

theorem cell21_329543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3].length) (baseStart_329543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329543 prefixEnd_329543 := by exact prefixLift 329543
  have htrace : WordTrace (prefixWord ++ tailWord_329543) baseStart_329543 baseEnd_329543 := by
    simpa [prefixWord, tailWord_329543, baseEnd_329543] using wordTrace_append hprefix tailTrace_329543
  have hstable : (prefixWord ++ tailWord_329543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329543).length < 2 ^ (prefixWord ++ tailWord_329543).sum := by decide
  have hdescent : baseEnd_329543 < baseStart_329543 := by decide
  rcases family_descends (prefixWord ++ tailWord_329543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329636 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_329636 : Nat := 118140960795 + 329636 * 2 ^ 59
def prefixEnd_329636 : Nat := 4983230072969 + 3 ^ 40 * 329636 * 2
def baseEnd_329636 : Nat := 75227426233590013926239

theorem tailTrace_329636 : CollatzResearch.WordTrace tailWord_329636 prefixEnd_329636 75227426233590013926239 := by
  unfold tailWord_329636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011406316896272095924381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8015208422528362794565841 6011406316896272095924381)
  ·
    refine ⟨2254277368836102035971643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6011406316896272095924381 2254277368836102035971643)
    ·
      refine ⟨3381416053254153053957465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2254277368836102035971643 3381416053254153053957465)
      ·
        refine ⟨2536062039940614790468099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3381416053254153053957465 2536062039940614790468099)
        ·
          refine ⟨3804093059910922185702149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536062039940614790468099 3804093059910922185702149)
          ·
            refine ⟨713267448733297909819153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3804093059910922185702149 713267448733297909819153)
            ·
              refine ⟨534950586549973432364365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713267448733297909819153 534950586549973432364365)
              ·
                refine ⟨200606469956240037136637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534950586549973432364365 200606469956240037136637)
                ·
                  refine ⟨75227426233590013926239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200606469956240037136637 75227426233590013926239)
                  ·
                    rfl

theorem cell21_329636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_329636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329636 prefixEnd_329636 := by exact prefixLift 329636
  have htrace : WordTrace (prefixWord ++ tailWord_329636) baseStart_329636 baseEnd_329636 := by
    simpa [prefixWord, tailWord_329636, baseEnd_329636] using wordTrace_append hprefix tailTrace_329636
  have hstable : (prefixWord ++ tailWord_329636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329636).length < 2 ^ (prefixWord ++ tailWord_329636).sum := by decide
  have hdescent : baseEnd_329636 < baseStart_329636 := by decide
  rcases family_descends (prefixWord ++ tailWord_329636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329678 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_329678 : Nat := 118140960795 + 329678 * 2 ^ 59
def prefixEnd_329678 : Nat := 4983230072969 + 3 ^ 40 * 329678 * 2
def baseEnd_329678 : Nat := 75237011205807274226153

theorem tailTrace_329678 : CollatzResearch.WordTrace tailWord_329678 prefixEnd_329678 75237011205807274226153 := by
  unfold tailWord_329678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503043062455048170609711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8016229666426923576585125 1503043062455048170609711)
  ·
    refine ⟨2254564593682572255914567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503043062455048170609711 2254564593682572255914567)
    ·
      refine ⟨3381846890523858383871851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2254564593682572255914567 3381846890523858383871851)
      ·
        refine ⟨5072770335785787575807777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381846890523858383871851 5072770335785787575807777)
        ·
          refine ⟨3804577751839340681855833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5072770335785787575807777 3804577751839340681855833)
          ·
            refine ⟨2853433313879505511391875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804577751839340681855833 2853433313879505511391875)
            ·
              refine ⟨4280149970819258267087813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853433313879505511391875 4280149970819258267087813)
              ·
                refine ⟨802528119528610925078965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4280149970819258267087813 802528119528610925078965)
                ·
                  refine ⟨75237011205807274226153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802528119528610925078965 75237011205807274226153)
                  ·
                    rfl

theorem cell21_329678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_329678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329678 prefixEnd_329678 := by exact prefixLift 329678
  have htrace : WordTrace (prefixWord ++ tailWord_329678) baseStart_329678 baseEnd_329678 := by
    simpa [prefixWord, tailWord_329678, baseEnd_329678] using wordTrace_append hprefix tailTrace_329678
  have hstable : (prefixWord ++ tailWord_329678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329678).length < 2 ^ (prefixWord ++ tailWord_329678).sum := by decide
  have hdescent : baseEnd_329678 < baseStart_329678 := by decide
  rcases family_descends (prefixWord ++ tailWord_329678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329698 : List Nat := [3, 3, 3, 1, 3, 1, 7]
def baseStart_329698 : Nat := 118140960795 + 329698 * 2 ^ 59
def prefixEnd_329698 : Nat := 4983230072969 + 3 ^ 40 * 329698 * 2
def baseEnd_329698 : Nat := 8360175053143520432531

theorem tailTrace_329698 : CollatzResearch.WordTrace tailWord_329698 prefixEnd_329698 8360175053143520432531 := by
  unfold tailWord_329698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006268489891982195151437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8016715973045285853737165 3006268489891982195151437)
  ·
    refine ⟨1127350683709493323181789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3006268489891982195151437 1127350683709493323181789)
    ·
      refine ⟨422756506391059996193171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1127350683709493323181789 422756506391059996193171)
      ·
        refine ⟨634134759586589994289757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422756506391059996193171 634134759586589994289757)
        ·
          refine ⟨237800534844971247858659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 634134759586589994289757 237800534844971247858659)
          ·
            refine ⟨356700802267456871787989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237800534844971247858659 356700802267456871787989)
            ·
              refine ⟨8360175053143520432531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 356700802267456871787989 8360175053143520432531)
              ·
                rfl

theorem cell21_329698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 7].length) (baseStart_329698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329698 prefixEnd_329698 := by exact prefixLift 329698
  have htrace : WordTrace (prefixWord ++ tailWord_329698) baseStart_329698 baseEnd_329698 := by
    simpa [prefixWord, tailWord_329698, baseEnd_329698] using wordTrace_append hprefix tailTrace_329698
  have hstable : (prefixWord ++ tailWord_329698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329698).length < 2 ^ (prefixWord ++ tailWord_329698).sum := by decide
  have hdescent : baseEnd_329698 < baseStart_329698 := by decide
  rcases family_descends (prefixWord ++ tailWord_329698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329864 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_329864 : Nat := 118140960795 + 329864 * 2 ^ 59
def prefixEnd_329864 : Nat := 4983230072969 + 3 ^ 40 * 329864 * 2
def baseEnd_329864 : Nat := 75279458939912284125773

theorem tailTrace_329864 : CollatzResearch.WordTrace tailWord_329864 prefixEnd_329864 75279458939912284125773 := by
  unfold tailWord_329864
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015564238483269565574323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8020752317977692754099097 6015564238483269565574323)
  ·
    refine ⟨9023346357724904348361485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015564238483269565574323 9023346357724904348361485)
    ·
      refine ⟨3383754884146839130635557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9023346357724904348361485 3383754884146839130635557)
      ·
        refine ⟨634454040777532336994167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3383754884146839130635557 634454040777532336994167)
        ·
          refine ⟨951681061166298505491251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634454040777532336994167 951681061166298505491251)
          ·
            refine ⟨1427521591749447758236877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951681061166298505491251 1427521591749447758236877)
            ·
              refine ⟨535320596906042909338829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1427521591749447758236877 535320596906042909338829)
              ·
                refine ⟨200745223839766091002061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 535320596906042909338829 200745223839766091002061)
                ·
                  refine ⟨75279458939912284125773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200745223839766091002061 75279458939912284125773)
                  ·
                    rfl

theorem cell21_329864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_329864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329864 prefixEnd_329864 := by exact prefixLift 329864
  have htrace : WordTrace (prefixWord ++ tailWord_329864) baseStart_329864 baseEnd_329864 := by
    simpa [prefixWord, tailWord_329864, baseEnd_329864] using wordTrace_append hprefix tailTrace_329864
  have hstable : (prefixWord ++ tailWord_329864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329864).length < 2 ^ (prefixWord ++ tailWord_329864).sum := by decide
  have hdescent : baseEnd_329864 < baseStart_329864 := by decide
  rcases family_descends (prefixWord ++ tailWord_329864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329892 : List Nat := [2, 3, 1, 2, 4, 1, 2, 6]
def baseStart_329892 : Nat := 118140960795 + 329892 * 2 ^ 59
def prefixEnd_329892 : Nat := 4983230072969 + 3 ^ 40 * 329892 * 2
def baseEnd_329892 : Nat := 25095282973796819219683

theorem tailTrace_329892 : CollatzResearch.WordTrace tailWord_329892 prefixEnd_329892 25095282973796819219683 := by
  unfold tailWord_329892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016074860432549956583965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8021433147243399942111953 6016074860432549956583965)
  ·
    refine ⟨2256028072662206233718987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6016074860432549956583965 2256028072662206233718987)
    ·
      refine ⟨3384042108993309350578481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256028072662206233718987 3384042108993309350578481)
      ·
        refine ⟨2538031581744982012933861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3384042108993309350578481 2538031581744982012933861)
        ·
          refine ⟨475880921577184127425099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2538031581744982012933861 475880921577184127425099)
          ·
            refine ⟨713821382365776191137649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475880921577184127425099 713821382365776191137649)
            ·
              refine ⟨535366036774332143353237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713821382365776191137649 535366036774332143353237)
              ·
                refine ⟨25095282973796819219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 535366036774332143353237 25095282973796819219683)
                ·
                  rfl

theorem cell21_329892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_329892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329892 prefixEnd_329892 := by exact prefixLift 329892
  have htrace : WordTrace (prefixWord ++ tailWord_329892) baseStart_329892 baseEnd_329892 := by
    simpa [prefixWord, tailWord_329892, baseEnd_329892] using wordTrace_append hprefix tailTrace_329892
  have hstable : (prefixWord ++ tailWord_329892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329892).length < 2 ^ (prefixWord ++ tailWord_329892).sum := by decide
  have hdescent : baseEnd_329892 < baseStart_329892 := by decide
  rcases family_descends (prefixWord ++ tailWord_329892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329982 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_329982 : Nat := 118140960795 + 329982 * 2 ^ 59
def prefixEnd_329982 : Nat := 4983230072969 + 3 ^ 40 * 329982 * 2
def baseEnd_329982 : Nat := 75306388147570301158865

theorem tailTrace_329982 : CollatzResearch.WordTrace tailWord_329982 prefixEnd_329982 75306388147570301158865 := by
  unfold tailWord_329982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504429036317380660493025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8023621527026030189296133 1504429036317380660493025)
  ·
    refine ⟨1128321777238035495369769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1504429036317380660493025 1128321777238035495369769)
    ·
      refine ⟨846241332928526621527327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1128321777238035495369769 846241332928526621527327)
      ·
        refine ⟨1269361999392789932290991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846241332928526621527327 1269361999392789932290991)
        ·
          refine ⟨1904042999089184898436487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269361999392789932290991 1904042999089184898436487)
          ·
            refine ⟨2856064498633777347654731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904042999089184898436487 2856064498633777347654731)
            ·
              refine ⟨4284096747950666021482097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856064498633777347654731 4284096747950666021482097)
              ·
                refine ⟨3213072560962999516111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284096747950666021482097 3213072560962999516111573)
                ·
                  refine ⟨75306388147570301158865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3213072560962999516111573 75306388147570301158865)
                  ·
                    rfl

theorem cell21_329982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_329982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329982 prefixEnd_329982 := by exact prefixLift 329982
  have htrace : WordTrace (prefixWord ++ tailWord_329982) baseStart_329982 baseEnd_329982 := by
    simpa [prefixWord, tailWord_329982, baseEnd_329982] using wordTrace_append hprefix tailTrace_329982
  have hstable : (prefixWord ++ tailWord_329982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329982).length < 2 ^ (prefixWord ++ tailWord_329982).sum := by decide
  have hdescent : baseEnd_329982 < baseStart_329982 := by decide
  rcases family_descends (prefixWord ++ tailWord_329982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329996 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_329996 : Nat := 118140960795 + 329996 * 2 ^ 59
def prefixEnd_329996 : Nat := 4983230072969 + 3 ^ 40 * 329996 * 2
def baseEnd_329996 : Nat := 75309583138309387925503

theorem tailTrace_329996 : CollatzResearch.WordTrace tailWord_329996 prefixEnd_329996 75309583138309387925503 := by
  unfold tailWord_329996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017971456244162837476921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8023961941658883783302561 6017971456244162837476921)
  ·
    refine ⟨4513478592183122128107691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6017971456244162837476921 4513478592183122128107691)
    ·
      refine ⟨6770217888274683192161537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4513478592183122128107691 6770217888274683192161537)
      ·
        refine ⟨5077663416206012394121153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6770217888274683192161537 5077663416206012394121153)
        ·
          refine ⟨3808247562154509295590865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5077663416206012394121153 3808247562154509295590865)
          ·
            refine ⟨2856185671615881971693149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808247562154509295590865 2856185671615881971693149)
            ·
              refine ⟨1071069626855955739384931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2856185671615881971693149 1071069626855955739384931)
              ·
                refine ⟨1606604440283933609077397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071069626855955739384931 1606604440283933609077397)
                ·
                  refine ⟨75309583138309387925503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1606604440283933609077397 75309583138309387925503)
                  ·
                    rfl

theorem cell21_329996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_329996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_329996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_329996 prefixEnd_329996 := by exact prefixLift 329996
  have htrace : WordTrace (prefixWord ++ tailWord_329996) baseStart_329996 baseEnd_329996 := by
    simpa [prefixWord, tailWord_329996, baseEnd_329996] using wordTrace_append hprefix tailTrace_329996
  have hstable : (prefixWord ++ tailWord_329996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329996).length < 2 ^ (prefixWord ++ tailWord_329996).sum := by decide
  have hdescent : baseEnd_329996 < baseStart_329996 := by decide
  rcases family_descends (prefixWord ++ tailWord_329996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330033 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 3]
def baseStart_330033 : Nat := 118140960795 + 330033 * 2 ^ 59
def prefixEnd_330033 : Nat := 4983230072969 + 3 ^ 40 * 330033 * 2
def baseEnd_330033 : Nat := 75318027042405545808761

theorem tailTrace_330033 : CollatzResearch.WordTrace tailWord_330033 prefixEnd_330033 75318027042405545808761 := by
  unfold tailWord_330033
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037292413354280994050753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8024861608902853996033835 12037292413354280994050753)
  ·
    refine ⟨9027969310015710745538065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12037292413354280994050753 9027969310015710745538065)
    ·
      refine ⟨6770976982511783059153549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9027969310015710745538065 6770976982511783059153549)
      ·
        refine ⟨2539116368441918647182581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6770976982511783059153549 2539116368441918647182581)
        ·
          refine ⟨238042159541429873173367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2539116368441918647182581 238042159541429873173367)
          ·
            refine ⟨357063239312144809760051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238042159541429873173367 357063239312144809760051)
            ·
              refine ⟨535594858968217214640077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357063239312144809760051 535594858968217214640077)
              ·
                refine ⟨200848072113081455490029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 535594858968217214640077 200848072113081455490029)
                ·
                  refine ⟨75318027042405545808761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200848072113081455490029 75318027042405545808761)
                  ·
                    rfl

theorem cell21_330033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_330033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330033 prefixEnd_330033 := by exact prefixLift 330033
  have htrace : WordTrace (prefixWord ++ tailWord_330033) baseStart_330033 baseEnd_330033 := by
    simpa [prefixWord, tailWord_330033, baseEnd_330033] using wordTrace_append hprefix tailTrace_330033
  have hstable : (prefixWord ++ tailWord_330033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330033).length < 2 ^ (prefixWord ++ tailWord_330033).sum := by decide
  have hdescent : baseEnd_330033 < baseStart_330033 := by decide
  rcases family_descends (prefixWord ++ tailWord_330033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330117 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_330117 : Nat := 118140960795 + 330117 * 2 ^ 59
def prefixEnd_330117 : Nat := 4983230072969 + 3 ^ 40 * 330117 * 2
def baseEnd_330117 : Nat := 75337196986840066408589

theorem tailTrace_330117 : CollatzResearch.WordTrace tailWord_330117 prefixEnd_330117 75337196986840066408589 := by
  unfold tailWord_330117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040356145049963340108605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8026904096699975560072403 12040356145049963340108605)
  ·
    refine ⟨4515133554393736252540727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12040356145049963340108605 4515133554393736252540727)
    ·
      refine ⟨6772700331590604378811091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515133554393736252540727 6772700331590604378811091)
      ·
        refine ⟨10159050497385906568216637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772700331590604378811091 10159050497385906568216637)
        ·
          refine ⟨3809643936519714963081239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10159050497385906568216637 3809643936519714963081239)
          ·
            refine ⟨5714465904779572444621859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809643936519714963081239 5714465904779572444621859)
            ·
              refine ⟨8571698857169358666932789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5714465904779572444621859 8571698857169358666932789)
              ·
                refine ⟨803596767859627375024949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8571698857169358666932789 803596767859627375024949)
                ·
                  refine ⟨75337196986840066408589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803596767859627375024949 75337196986840066408589)
                  ·
                    rfl

theorem cell21_330117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_330117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330117 prefixEnd_330117 := by exact prefixLift 330117
  have htrace : WordTrace (prefixWord ++ tailWord_330117) baseStart_330117 baseEnd_330117 := by
    simpa [prefixWord, tailWord_330117, baseEnd_330117] using wordTrace_append hprefix tailTrace_330117
  have hstable : (prefixWord ++ tailWord_330117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330117).length < 2 ^ (prefixWord ++ tailWord_330117).sum := by decide
  have hdescent : baseEnd_330117 < baseStart_330117 := by decide
  rcases family_descends (prefixWord ++ tailWord_330117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330151 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 3]
def baseStart_330151 : Nat := 118140960795 + 330151 * 2 ^ 59
def prefixEnd_330151 : Nat := 4983230072969 + 3 ^ 40 * 330151 * 2
def baseEnd_330151 : Nat := 75344956250063562841853

theorem tailTrace_330151 : CollatzResearch.WordTrace tailWord_330151 prefixEnd_330151 75344956250063562841853 := by
  unfold tailWord_330151
  simp only [CollatzResearch.WordTrace]
  refine ⟨12041596226926787146846307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8027730817951191431230871 12041596226926787146846307)
  ·
    refine ⟨18062394340390180720269461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12041596226926787146846307 18062394340390180720269461)
    ·
      refine ⟨846674734705789721262631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18062394340390180720269461 846674734705789721262631)
      ·
        refine ⟨1270012102058684581893947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846674734705789721262631 1270012102058684581893947)
        ·
          refine ⟨1905018153088026872840921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270012102058684581893947 1905018153088026872840921)
          ·
            refine ⟨1428763614816020154630691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905018153088026872840921 1428763614816020154630691)
            ·
              refine ⟨2143145422224030231946037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428763614816020154630691 2143145422224030231946037)
              ·
                refine ⟨200919883333502834244941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2143145422224030231946037 200919883333502834244941)
                ·
                  refine ⟨75344956250063562841853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200919883333502834244941 75344956250063562841853)
                  ·
                    rfl

theorem cell21_330151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3].length) (baseStart_330151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330151 prefixEnd_330151 := by exact prefixLift 330151
  have htrace : WordTrace (prefixWord ++ tailWord_330151) baseStart_330151 baseEnd_330151 := by
    simpa [prefixWord, tailWord_330151, baseEnd_330151] using wordTrace_append hprefix tailTrace_330151
  have hstable : (prefixWord ++ tailWord_330151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330151).length < 2 ^ (prefixWord ++ tailWord_330151).sum := by decide
  have hdescent : baseEnd_330151 < baseStart_330151 := by decide
  rcases family_descends (prefixWord ++ tailWord_330151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330162 : List Nat := [3, 2, 1, 1, 1, 1, 12]
def baseStart_330162 : Nat := 118140960795 + 330162 * 2 ^ 59
def prefixEnd_330162 : Nat := 4983230072969 + 3 ^ 40 * 330162 * 2
def baseEnd_330162 : Nat := 8371940733325554239833

theorem tailTrace_330162 : CollatzResearch.WordTrace tailWord_330162 prefixEnd_330162 8371940733325554239833 := by
  unfold tailWord_330162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010499357471734006374185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8027998286591290683664493 3010499357471734006374185)
  ·
    refine ⟨2257874518103800504780639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3010499357471734006374185 2257874518103800504780639)
    ·
      refine ⟨3386811777155700757170959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2257874518103800504780639 3386811777155700757170959)
      ·
        refine ⟨5080217665733551135756439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386811777155700757170959 5080217665733551135756439)
        ·
          refine ⟨7620326498600326703634659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080217665733551135756439 7620326498600326703634659)
          ·
            refine ⟨11430489747900490055451989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620326498600326703634659 11430489747900490055451989)
            ·
              refine ⟨8371940733325554239833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11430489747900490055451989 8371940733325554239833)
              ·
                rfl

theorem cell21_330162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 12].length) (baseStart_330162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330162 prefixEnd_330162 := by exact prefixLift 330162
  have htrace : WordTrace (prefixWord ++ tailWord_330162) baseStart_330162 baseEnd_330162 := by
    simpa [prefixWord, tailWord_330162, baseEnd_330162] using wordTrace_append hprefix tailTrace_330162
  have hstable : (prefixWord ++ tailWord_330162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330162).length < 2 ^ (prefixWord ++ tailWord_330162).sum := by decide
  have hdescent : baseEnd_330162 < baseStart_330162 := by decide
  rcases family_descends (prefixWord ++ tailWord_330162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330165 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_330165 : Nat := 118140960795 + 330165 * 2 ^ 59
def prefixEnd_330165 : Nat := 4983230072969 + 3 ^ 40 * 330165 * 2
def baseEnd_330165 : Nat := 75348151240802649608491

theorem tailTrace_330165 : CollatzResearch.WordTrace tailWord_330165 prefixEnd_330165 75348151240802649608491 := by
  unfold tailWord_330165
  simp only [CollatzResearch.WordTrace]
  refine ⟨12042106848876067537855949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8028071232584045025237299 12042106848876067537855949)
  ·
    refine ⟨4515790068328525326695981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12042106848876067537855949 4515790068328525326695981)
    ·
      refine ⟨1693421275623196997510993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4515790068328525326695981 1693421275623196997510993)
      ·
        refine ⟨1270065956717397748133245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693421275623196997510993 1270065956717397748133245)
        ·
          refine ⟨476274733769024155549967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1270065956717397748133245 476274733769024155549967)
          ·
            refine ⟨714412100653536233324951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476274733769024155549967 714412100653536233324951)
            ·
              refine ⟨1071618150980304349987427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714412100653536233324951 1071618150980304349987427)
              ·
                refine ⟨1607427226470456524981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071618150980304349987427 1607427226470456524981141)
                ·
                  refine ⟨75348151240802649608491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1607427226470456524981141 75348151240802649608491)
                  ·
                    rfl

theorem cell21_330165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_330165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330165 prefixEnd_330165 := by exact prefixLift 330165
  have htrace : WordTrace (prefixWord ++ tailWord_330165) baseStart_330165 baseEnd_330165 := by
    simpa [prefixWord, tailWord_330165, baseEnd_330165] using wordTrace_append hprefix tailTrace_330165
  have hstable : (prefixWord ++ tailWord_330165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330165).length < 2 ^ (prefixWord ++ tailWord_330165).sum := by decide
  have hdescent : baseEnd_330165 < baseStart_330165 := by decide
  rcases family_descends (prefixWord ++ tailWord_330165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330196 : List Nat := [2, 4, 1, 2, 2, 1, 4, 5]
def baseStart_330196 : Nat := 118140960795 + 330196 * 2 ^ 59
def prefixEnd_330196 : Nat := 4983230072969 + 3 ^ 40 * 330196 * 2
def baseEnd_330196 : Nat := 25118408621051161530587

theorem tailTrace_330196 : CollatzResearch.WordTrace tailWord_330196 prefixEnd_330196 25118408621051161530587 := by
  unfold tailWord_330196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6021618755881879916117221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8028825007842506554822961 6021618755881879916117221)
  ·
    refine ⟨1129053516727852484271979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6021618755881879916117221 1129053516727852484271979)
    ·
      refine ⟨1693580275091778726407969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129053516727852484271979 1693580275091778726407969)
      ·
        refine ⟨1270185206318834044805977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693580275091778726407969 1270185206318834044805977)
        ·
          refine ⟨952638904739125533604483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1270185206318834044805977 952638904739125533604483)
          ·
            refine ⟨1428958357108688300406725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952638904739125533604483 1428958357108688300406725)
            ·
              refine ⟨267929691957879056326261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1428958357108688300406725 267929691957879056326261)
              ·
                refine ⟨25118408621051161530587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267929691957879056326261 25118408621051161530587)
                ·
                  rfl

theorem cell21_330196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_330196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330196 prefixEnd_330196 := by exact prefixLift 330196
  have htrace : WordTrace (prefixWord ++ tailWord_330196) baseStart_330196 baseEnd_330196 := by
    simpa [prefixWord, tailWord_330196, baseEnd_330196] using wordTrace_append hprefix tailTrace_330196
  have hstable : (prefixWord ++ tailWord_330196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330196).length < 2 ^ (prefixWord ++ tailWord_330196).sum := by decide
  have hdescent : baseEnd_330196 < baseStart_330196 := by decide
  rcases family_descends (prefixWord ++ tailWord_330196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330224 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_330224 : Nat := 118140960795 + 330224 * 2 ^ 59
def prefixEnd_330224 : Nat := 4983230072969 + 3 ^ 40 * 330224 * 2
def baseEnd_330224 : Nat := 75361615844631658125037

theorem tailTrace_330224 : CollatzResearch.WordTrace tailWord_330224 prefixEnd_330224 75361615844631658125037 := by
  unfold tailWord_330224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022129377831160307126863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8029505837108213742835817 6022129377831160307126863)
  ·
    refine ⟨9033194066746740460690295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6022129377831160307126863 9033194066746740460690295)
    ·
      refine ⟨13549791100120110691035443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9033194066746740460690295 13549791100120110691035443)
      ·
        refine ⟨20324686650180166036553165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13549791100120110691035443 20324686650180166036553165)
        ·
          refine ⟨7621757493817562263707437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20324686650180166036553165 7621757493817562263707437)
          ·
            refine ⟨2858159060181585848890289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7621757493817562263707437 2858159060181585848890289)
            ·
              refine ⟨2143619295136189386667717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858159060181585848890289 2143619295136189386667717)
              ·
                refine ⟨401928617838035510000197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2143619295136189386667717 401928617838035510000197)
                ·
                  refine ⟨75361615844631658125037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401928617838035510000197 75361615844631658125037)
                  ·
                    rfl

theorem cell21_330224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_330224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330224 prefixEnd_330224 := by exact prefixLift 330224
  have htrace : WordTrace (prefixWord ++ tailWord_330224) baseStart_330224 baseEnd_330224 := by
    simpa [prefixWord, tailWord_330224, baseEnd_330224] using wordTrace_append hprefix tailTrace_330224
  have hstable : (prefixWord ++ tailWord_330224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330224).length < 2 ^ (prefixWord ++ tailWord_330224).sum := by decide
  have hdescent : baseEnd_330224 < baseStart_330224 := by decide
  rcases family_descends (prefixWord ++ tailWord_330224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330227 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 3]
def baseStart_330227 : Nat := 118140960795 + 330227 * 2 ^ 59
def prefixEnd_330227 : Nat := 4983230072969 + 3 ^ 40 * 330227 * 2
def baseEnd_330227 : Nat := 75362300485504319575031

theorem tailTrace_330227 : CollatzResearch.WordTrace tailWord_330227 prefixEnd_330227 75362300485504319575031 := by
  unfold tailWord_330227
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044368174651452126612935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8029578783100968084408623 12044368174651452126612935)
  ·
    refine ⟨18066552261977178189919403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12044368174651452126612935 18066552261977178189919403)
    ·
      refine ⟨27099828392965767284879105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18066552261977178189919403 27099828392965767284879105)
      ·
        refine ⟨20324871294724325463659329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27099828392965767284879105 20324871294724325463659329)
        ·
          refine ⟨15243653471043244097744497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20324871294724325463659329 15243653471043244097744497)
          ·
            refine ⟨11432740103282433073308373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15243653471043244097744497 11432740103282433073308373)
            ·
              refine ⟨267954846170682025155665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11432740103282433073308373 267954846170682025155665)
              ·
                refine ⟨200966134628011518866749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267954846170682025155665 200966134628011518866749)
                ·
                  refine ⟨75362300485504319575031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200966134628011518866749 75362300485504319575031)
                  ·
                    rfl

theorem cell21_330227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3].length) (baseStart_330227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330227 prefixEnd_330227 := by exact prefixLift 330227
  have htrace : WordTrace (prefixWord ++ tailWord_330227) baseStart_330227 baseEnd_330227 := by
    simpa [prefixWord, tailWord_330227, baseEnd_330227] using wordTrace_append hprefix tailTrace_330227
  have hstable : (prefixWord ++ tailWord_330227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330227).length < 2 ^ (prefixWord ++ tailWord_330227).sum := by decide
  have hdescent : baseEnd_330227 < baseStart_330227 := by decide
  rcases family_descends (prefixWord ++ tailWord_330227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330241 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_330241 : Nat := 118140960795 + 330241 * 2 ^ 59
def prefixEnd_330241 : Nat := 4983230072969 + 3 ^ 40 * 330241 * 2
def baseEnd_330241 : Nat := 75365495476243406341669

theorem tailTrace_330241 : CollatzResearch.WordTrace tailWord_330241 prefixEnd_330241 75365495476243406341669 := by
  unfold tailWord_330241
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044878796600732517622577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8029919197733821678415051 12044878796600732517622577)
  ·
    refine ⟨9033659097450549388216933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12044878796600732517622577 9033659097450549388216933)
    ·
      refine ⟨1693811080771978010290675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9033659097450549388216933 1693811080771978010290675)
      ·
        refine ⟨2540716621157967015436013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693811080771978010290675 2540716621157967015436013)
        ·
          refine ⟨952768732934237630788505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2540716621157967015436013 952768732934237630788505)
          ·
            refine ⟨714576549700678223091379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952768732934237630788505 714576549700678223091379)
            ·
              refine ⟨1071864824551017334637069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714576549700678223091379 1071864824551017334637069)
              ·
                refine ⟨401949309206631500488901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071864824551017334637069 401949309206631500488901)
                ·
                  refine ⟨75365495476243406341669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401949309206631500488901 75365495476243406341669)
                  ·
                    rfl

theorem cell21_330241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_330241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330241 prefixEnd_330241 := by exact prefixLift 330241
  have htrace : WordTrace (prefixWord ++ tailWord_330241) baseStart_330241 baseEnd_330241 := by
    simpa [prefixWord, tailWord_330241, baseEnd_330241] using wordTrace_append hprefix tailTrace_330241
  have hstable : (prefixWord ++ tailWord_330241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330241).length < 2 ^ (prefixWord ++ tailWord_330241).sum := by decide
  have hdescent : baseEnd_330241 < baseStart_330241 := by decide
  rcases family_descends (prefixWord ++ tailWord_330241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330283 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_330283 : Nat := 118140960795 + 330283 * 2 ^ 59
def prefixEnd_330283 : Nat := 4983230072969 + 3 ^ 40 * 330283 * 2
def baseEnd_330283 : Nat := 75375080448460666641583

theorem tailTrace_330283 : CollatzResearch.WordTrace tailWord_330283 prefixEnd_330283 75375080448460666641583 := by
  unfold tailWord_330283
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046410662448573690651503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8030940441632382460434335 12046410662448573690651503)
  ·
    refine ⟨18069615993672860535977255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12046410662448573690651503 18069615993672860535977255)
    ·
      refine ⟨27104423990509290803965883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18069615993672860535977255 27104423990509290803965883)
      ·
        refine ⟨40656635985763936205948825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27104423990509290803965883 40656635985763936205948825)
        ·
          refine ⟨30492476989322952154461619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40656635985763936205948825 30492476989322952154461619)
          ·
            refine ⟨45738715483984428231692429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30492476989322952154461619 45738715483984428231692429)
            ·
              refine ⟨17152018306494160586884661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45738715483984428231692429 17152018306494160586884661)
              ·
                refine ⟨1608001716233827555020437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17152018306494160586884661 1608001716233827555020437)
                ·
                  refine ⟨75375080448460666641583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1608001716233827555020437 75375080448460666641583)
                  ·
                    rfl

theorem cell21_330283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_330283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330283 prefixEnd_330283 := by exact prefixLift 330283
  have htrace : WordTrace (prefixWord ++ tailWord_330283) baseStart_330283 baseEnd_330283 := by
    simpa [prefixWord, tailWord_330283, baseEnd_330283] using wordTrace_append hprefix tailTrace_330283
  have hstable : (prefixWord ++ tailWord_330283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330283).length < 2 ^ (prefixWord ++ tailWord_330283).sum := by decide
  have hdescent : baseEnd_330283 < baseStart_330283 := by decide
  rcases family_descends (prefixWord ++ tailWord_330283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330365 : List Nat := [1, 4, 1, 1, 6, 1, 2, 5]
def baseStart_330365 : Nat := 118140960795 + 330365 * 2 ^ 59
def prefixEnd_330365 : Nat := 4983230072969 + 3 ^ 40 * 330365 * 2
def baseEnd_330365 : Nat := 25131264655215582091583

theorem tailTrace_330365 : CollatzResearch.WordTrace tailWord_330365 prefixEnd_330365 25131264655215582091583 := by
  unfold tailWord_330365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12049401448151501695136549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8032934298767667796757699 12049401448151501695136549)
  ·
    refine ⟨2259262771528406567838103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12049401448151501695136549 2259262771528406567838103)
    ·
      refine ⟨3388894157292609851757155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2259262771528406567838103 3388894157292609851757155)
      ·
        refine ⟨5083341235938914777635733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388894157292609851757155 5083341235938914777635733)
        ·
          refine ⟨238281620434636630201675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5083341235938914777635733 238281620434636630201675)
          ·
            refine ⟨357422430651954945302513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238281620434636630201675 357422430651954945302513)
            ·
              refine ⟨268066822988966208976885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357422430651954945302513 268066822988966208976885)
              ·
                refine ⟨25131264655215582091583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268066822988966208976885 25131264655215582091583)
                ·
                  rfl

theorem cell21_330365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 5].length) (baseStart_330365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330365 prefixEnd_330365 := by exact prefixLift 330365
  have htrace : WordTrace (prefixWord ++ tailWord_330365) baseStart_330365 baseEnd_330365 := by
    simpa [prefixWord, tailWord_330365, baseEnd_330365] using wordTrace_append hprefix tailTrace_330365
  have hstable : (prefixWord ++ tailWord_330365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330365).length < 2 ^ (prefixWord ++ tailWord_330365).sum := by decide
  have hdescent : baseEnd_330365 < baseStart_330365 := by decide
  rcases family_descends (prefixWord ++ tailWord_330365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330396 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_330396 : Nat := 118140960795 + 330396 * 2 ^ 59
def prefixEnd_330396 : Nat := 4983230072969 + 3 ^ 40 * 330396 * 2
def baseEnd_330396 : Nat := 75400868587997581258019

theorem tailTrace_330396 : CollatzResearch.WordTrace tailWord_330396 prefixEnd_330396 75400868587997581258019 := by
  unfold tailWord_330396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025266055519596994757521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8033688074026129326343361 6025266055519596994757521)
  ·
    refine ⟨4518949541639697746068141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6025266055519596994757521 4518949541639697746068141)
    ·
      refine ⟨1694606078114886654775553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4518949541639697746068141 1694606078114886654775553)
      ·
        refine ⟨1270954558586164991081665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1694606078114886654775553 1270954558586164991081665)
        ·
          refine ⟨953215918939623743311249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1270954558586164991081665 953215918939623743311249)
          ·
            refine ⟨714911939204717807483437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953215918939623743311249 714911939204717807483437)
            ·
              refine ⟨268091977201769177806289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714911939204717807483437 268091977201769177806289)
              ·
                refine ⟨201068982901326883354717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268091977201769177806289 201068982901326883354717)
                ·
                  refine ⟨75400868587997581258019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201068982901326883354717 75400868587997581258019)
                  ·
                    rfl

theorem cell21_330396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_330396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330396 prefixEnd_330396 := by exact prefixLift 330396
  have htrace : WordTrace (prefixWord ++ tailWord_330396) baseStart_330396 baseEnd_330396 := by
    simpa [prefixWord, tailWord_330396, baseEnd_330396] using wordTrace_append hprefix tailTrace_330396
  have hstable : (prefixWord ++ tailWord_330396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330396).length < 2 ^ (prefixWord ++ tailWord_330396).sum := by decide
  have hdescent : baseEnd_330396 < baseStart_330396 := by decide
  rcases family_descends (prefixWord ++ tailWord_330396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330455 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 3]
def baseStart_330455 : Nat := 118140960795 + 330455 * 2 ^ 59
def prefixEnd_330455 : Nat := 4983230072969 + 3 ^ 40 * 330455 * 2
def baseEnd_330455 : Nat := 75414333191826589774565

theorem tailTrace_330455 : CollatzResearch.WordTrace tailWord_330455 prefixEnd_330455 75414333191826589774565 := by
  unfold tailWord_330455
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052684017825447065912819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8035122678550298043941879 12052684017825447065912819)
  ·
    refine ⟨18079026026738170598869229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12052684017825447065912819 18079026026738170598869229)
    ·
      refine ⟨6779634760026813974575961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18079026026738170598869229 6779634760026813974575961)
      ·
        refine ⟨5084726070020110480931971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779634760026813974575961 5084726070020110480931971)
        ·
          refine ⟨7627089105030165721397957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084726070020110480931971 7627089105030165721397957)
          ·
            refine ⟨1430079207193156072762117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7627089105030165721397957 1430079207193156072762117)
            ·
              refine ⟨268139851348716763642897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1430079207193156072762117 268139851348716763642897)
              ·
                refine ⟨201104888511537572732173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268139851348716763642897 201104888511537572732173)
                ·
                  refine ⟨75414333191826589774565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201104888511537572732173 75414333191826589774565)
                  ·
                    rfl

theorem cell21_330455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3].length) (baseStart_330455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330455 prefixEnd_330455 := by exact prefixLift 330455
  have htrace : WordTrace (prefixWord ++ tailWord_330455) baseStart_330455 baseEnd_330455 := by
    simpa [prefixWord, tailWord_330455, baseEnd_330455] using wordTrace_append hprefix tailTrace_330455
  have hstable : (prefixWord ++ tailWord_330455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330455).length < 2 ^ (prefixWord ++ tailWord_330455).sum := by decide
  have hdescent : baseEnd_330455 < baseStart_330455 := by decide
  rcases family_descends (prefixWord ++ tailWord_330455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330511 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_330511 : Nat := 118140960795 + 330511 * 2 ^ 59
def prefixEnd_330511 : Nat := 4983230072969 + 3 ^ 40 * 330511 * 2
def baseEnd_330511 : Nat := 75427113154782936841117

theorem tailTrace_330511 : CollatzResearch.WordTrace tailWord_330511 prefixEnd_330511 75427113154782936841117 := by
  unfold tailWord_330511
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054726505622568629951387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8036484337081712419967591 12054726505622568629951387)
  ·
    refine ⟨18082089758433852944927081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12054726505622568629951387 18082089758433852944927081)
    ·
      refine ⟨13561567318825389708695311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18082089758433852944927081 13561567318825389708695311)
      ·
        refine ⟨20342350978238084563042967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561567318825389708695311 20342350978238084563042967)
        ·
          refine ⟨30513526467357126844564451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20342350978238084563042967 30513526467357126844564451)
          ·
            refine ⟨45770289701035690266846677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30513526467357126844564451 45770289701035690266846677)
            ·
              refine ⟨1072741164868023990629219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45770289701035690266846677 1072741164868023990629219)
              ·
                refine ⟨1609111747302035985943829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072741164868023990629219 1609111747302035985943829)
                ·
                  refine ⟨75427113154782936841117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1609111747302035985943829 75427113154782936841117)
                  ·
                    rfl

theorem cell21_330511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_330511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330511 prefixEnd_330511 := by exact prefixLift 330511
  have htrace : WordTrace (prefixWord ++ tailWord_330511) baseStart_330511 baseEnd_330511 := by
    simpa [prefixWord, tailWord_330511, baseEnd_330511] using wordTrace_append hprefix tailTrace_330511
  have hstable : (prefixWord ++ tailWord_330511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330511).length < 2 ^ (prefixWord ++ tailWord_330511).sum := by decide
  have hdescent : baseEnd_330511 < baseStart_330511 := by decide
  rcases family_descends (prefixWord ++ tailWord_330511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330652 : List Nat := [2, 2, 3, 3, 2, 1, 3, 5]
def baseStart_330652 : Nat := 118140960795 + 330652 * 2 ^ 59
def prefixEnd_330652 : Nat := 4983230072969 + 3 ^ 40 * 330652 * 2
def baseEnd_330652 : Nat := 25153097091932674996943

theorem tailTrace_330652 : CollatzResearch.WordTrace tailWord_330652 prefixEnd_330652 25153097091932674996943 := by
  unfold tailWord_330652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029934599055874855417105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8039912798741166473889473 6029934599055874855417105)
  ·
    refine ⟨4522450949291906141562829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6029934599055874855417105 4522450949291906141562829)
    ·
      refine ⟨1695919105984464803086061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4522450949291906141562829 1695919105984464803086061)
      ·
        refine ⟨635969664744174301157273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1695919105984464803086061 635969664744174301157273)
        ·
          refine ⟨476977248558130725867955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635969664744174301157273 476977248558130725867955)
          ·
            refine ⟨715465872837196088801933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476977248558130725867955 715465872837196088801933)
            ·
              refine ⟨268299702313948533300725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715465872837196088801933 268299702313948533300725)
              ·
                refine ⟨25153097091932674996943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268299702313948533300725 25153097091932674996943)
                ·
                  rfl

theorem cell21_330652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_330652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330652 prefixEnd_330652 := by exact prefixLift 330652
  have htrace : WordTrace (prefixWord ++ tailWord_330652) baseStart_330652 baseEnd_330652 := by
    simpa [prefixWord, tailWord_330652, baseEnd_330652] using wordTrace_append hprefix tailTrace_330652
  have hstable : (prefixWord ++ tailWord_330652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330652).length < 2 ^ (prefixWord ++ tailWord_330652).sum := by decide
  have hdescent : baseEnd_330652 < baseStart_330652 := by decide
  rcases family_descends (prefixWord ++ tailWord_330652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330680 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_330680 : Nat := 118140960795 + 330680 * 2 ^ 59
def prefixEnd_330680 : Nat := 4983230072969 + 3 ^ 40 * 330680 * 2
def baseEnd_330680 : Nat := 75465681257276198524105

theorem tailTrace_330680 : CollatzResearch.WordTrace tailWord_330680 prefixEnd_330680 75465681257276198524105 := by
  unfold tailWord_330680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030445221005155246426747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8040593628006873661902329 6030445221005155246426747)
  ·
    refine ⟨9045667831507732869640121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6030445221005155246426747 9045667831507732869640121)
    ·
      refine ⟨6784250873630799652230091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9045667831507732869640121 6784250873630799652230091)
      ·
        refine ⟨10176376310446199478345137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784250873630799652230091 10176376310446199478345137)
        ·
          refine ⟨7632282232834649608758853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10176376310446199478345137 7632282232834649608758853)
          ·
            refine ⟨1431052918656496801642285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7632282232834649608758853 1431052918656496801642285)
            ·
              refine ⟨536644844496186300615857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431052918656496801642285 536644844496186300615857)
              ·
                refine ⟨402483633372139725461893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536644844496186300615857 402483633372139725461893)
                ·
                  refine ⟨75465681257276198524105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402483633372139725461893 75465681257276198524105)
                  ·
                    rfl

theorem cell21_330680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_330680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330680 prefixEnd_330680 := by exact prefixLift 330680
  have htrace : WordTrace (prefixWord ++ tailWord_330680) baseStart_330680 baseEnd_330680 := by
    simpa [prefixWord, tailWord_330680, baseEnd_330680] using wordTrace_append hprefix tailTrace_330680
  have hstable : (prefixWord ++ tailWord_330680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330680).length < 2 ^ (prefixWord ++ tailWord_330680).sum := by decide
  have hdescent : baseEnd_330680 < baseStart_330680 := by decide
  rcases family_descends (prefixWord ++ tailWord_330680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330742 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_330742 : Nat := 118140960795 + 330742 * 2 ^ 59
def prefixEnd_330742 : Nat := 4983230072969 + 3 ^ 40 * 330742 * 2
def baseEnd_330742 : Nat := 75479830501977868490645

theorem tailTrace_330742 : CollatzResearch.WordTrace tailWord_330742 prefixEnd_330742 75479830501977868490645 := by
  unfold tailWord_330742
  simp only [CollatzResearch.WordTrace]
  refine ⟨753946985486605942600655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8042101178523796721073653 753946985486605942600655)
  ·
    refine ⟨1130920478229908913900983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 753946985486605942600655 1130920478229908913900983)
    ·
      refine ⟨1696380717344863370851475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130920478229908913900983 1696380717344863370851475)
      ·
        refine ⟨2544571076017295056277213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696380717344863370851475 2544571076017295056277213)
        ·
          refine ⟨954214153506485646103955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2544571076017295056277213 954214153506485646103955)
          ·
            refine ⟨1431321230259728469155933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954214153506485646103955 1431321230259728469155933)
            ·
              refine ⟨536745461347398175933475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431321230259728469155933 536745461347398175933475)
              ·
                refine ⟨805118192021097263900213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536745461347398175933475 805118192021097263900213)
                ·
                  refine ⟨75479830501977868490645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805118192021097263900213 75479830501977868490645)
                  ·
                    rfl

theorem cell21_330742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_330742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330742 prefixEnd_330742 := by exact prefixLift 330742
  have htrace : WordTrace (prefixWord ++ tailWord_330742) baseStart_330742 baseEnd_330742 := by
    simpa [prefixWord, tailWord_330742, baseEnd_330742] using wordTrace_append hprefix tailTrace_330742
  have hstable : (prefixWord ++ tailWord_330742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330742).length < 2 ^ (prefixWord ++ tailWord_330742).sum := by decide
  have hdescent : baseEnd_330742 < baseStart_330742 := by decide
  rcases family_descends (prefixWord ++ tailWord_330742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330804 : List Nat := [2, 5, 1, 2, 1, 3, 1, 6]
def baseStart_330804 : Nat := 118140960795 + 330804 * 2 ^ 59
def prefixEnd_330804 : Nat := 4983230072969 + 3 ^ 40 * 330804 * 2
def baseEnd_330804 : Nat := 25164659915559846152395

theorem tailTrace_330804 : CollatzResearch.WordTrace tailWord_330804 prefixEnd_330804 25164659915559846152395 := by
  unfold tailWord_330804
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032706546780539835183733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8043608729040719780244977 6032706546780539835183733)
  ·
    refine ⟨565566238760675609548475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6032706546780539835183733 565566238760675609548475)
    ·
      refine ⟨848349358141013414322713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565566238760675609548475 848349358141013414322713)
      ·
        refine ⟨636262018605760060742035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848349358141013414322713 636262018605760060742035)
        ·
          refine ⟨954393027908640091113053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636262018605760060742035 954393027908640091113053)
          ·
            refine ⟨357897385465740034167395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 954393027908640091113053 357897385465740034167395)
            ·
              refine ⟨536846078198610051251093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357897385465740034167395 536846078198610051251093)
              ·
                refine ⟨25164659915559846152395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 536846078198610051251093 25164659915559846152395)
                ·
                  rfl

theorem cell21_330804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_330804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330804 prefixEnd_330804 := by exact prefixLift 330804
  have htrace : WordTrace (prefixWord ++ tailWord_330804) baseStart_330804 baseEnd_330804 := by
    simpa [prefixWord, tailWord_330804, baseEnd_330804] using wordTrace_append hprefix tailTrace_330804
  have hstable : (prefixWord ++ tailWord_330804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330804).length < 2 ^ (prefixWord ++ tailWord_330804).sum := by decide
  have hdescent : baseEnd_330804 < baseStart_330804 := by decide
  rcases family_descends (prefixWord ++ tailWord_330804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330911 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 5]
def baseStart_330911 : Nat := 118140960795 + 330911 * 2 ^ 59
def prefixEnd_330911 : Nat := 4983230072969 + 3 ^ 40 * 330911 * 2
def baseEnd_330911 : Nat := 75518398604471130173633

theorem tailTrace_330911 : CollatzResearch.WordTrace tailWord_330911 prefixEnd_330911 75518398604471130173633 := by
  unfold tailWord_330911
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069315704173436944512587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8046210469448957963008391 12069315704173436944512587)
  ·
    refine ⟨18103973556260155416768881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12069315704173436944512587 18103973556260155416768881)
    ·
      refine ⟨13577980167195116562576661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18103973556260155416768881 13577980167195116562576661)
      ·
        refine ⟨636467820337271088870781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13577980167195116562576661 636467820337271088870781)
        ·
          refine ⟨238675432626476658326543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636467820337271088870781 238675432626476658326543)
          ·
            refine ⟨358013148939714987489815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238675432626476658326543 358013148939714987489815)
            ·
              refine ⟨537019723409572481234723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358013148939714987489815 537019723409572481234723)
              ·
                refine ⟨805529585114358721852085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537019723409572481234723 805529585114358721852085)
                ·
                  refine ⟨75518398604471130173633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805529585114358721852085 75518398604471130173633)
                  ·
                    rfl

theorem cell21_330911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5].length) (baseStart_330911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330911 prefixEnd_330911 := by exact prefixLift 330911
  have htrace : WordTrace (prefixWord ++ tailWord_330911) baseStart_330911 baseEnd_330911 := by
    simpa [prefixWord, tailWord_330911, baseEnd_330911] using wordTrace_append hprefix tailTrace_330911
  have hstable : (prefixWord ++ tailWord_330911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330911).length < 2 ^ (prefixWord ++ tailWord_330911).sum := by decide
  have hdescent : baseEnd_330911 < baseStart_330911 := by decide
  rcases family_descends (prefixWord ++ tailWord_330911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330925 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_330925 : Nat := 118140960795 + 330925 * 2 ^ 59
def prefixEnd_330925 : Nat := 4983230072969 + 3 ^ 40 * 330925 * 2
def baseEnd_330925 : Nat := 75521593595210216940271

theorem tailTrace_330925 : CollatzResearch.WordTrace tailWord_330925 prefixEnd_330925 75521593595210216940271 := by
  unfold tailWord_330925
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069826326122717335522229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8046550884081811557014819 12069826326122717335522229)
  ·
    refine ⟨1131546218074004750205209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12069826326122717335522229 1131546218074004750205209)
    ·
      refine ⟨848659663555503562653907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131546218074004750205209 848659663555503562653907)
      ·
        refine ⟨1272989495333255343980861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848659663555503562653907 1272989495333255343980861)
        ·
          refine ⟨477371060749970753992823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1272989495333255343980861 477371060749970753992823)
          ·
            refine ⟨716056591124956130989235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477371060749970753992823 716056591124956130989235)
            ·
              refine ⟨1074084886687434196483853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716056591124956130989235 1074084886687434196483853)
              ·
                refine ⟨402781832507787823681445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074084886687434196483853 402781832507787823681445)
                ·
                  refine ⟨75521593595210216940271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402781832507787823681445 75521593595210216940271)
                  ·
                    rfl

theorem cell21_330925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_330925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330925 prefixEnd_330925 := by exact prefixLift 330925
  have htrace : WordTrace (prefixWord ++ tailWord_330925) baseStart_330925 baseEnd_330925 := by
    simpa [prefixWord, tailWord_330925, baseEnd_330925] using wordTrace_append hprefix tailTrace_330925
  have hstable : (prefixWord ++ tailWord_330925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330925).length < 2 ^ (prefixWord ++ tailWord_330925).sum := by decide
  have hdescent : baseEnd_330925 < baseStart_330925 := by decide
  rcases family_descends (prefixWord ++ tailWord_330925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330967 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_330967 : Nat := 118140960795 + 330967 * 2 ^ 59
def prefixEnd_330967 : Nat := 4983230072969 + 3 ^ 40 * 330967 * 2
def baseEnd_330967 : Nat := 75531178567427477240185

theorem tailTrace_330967 : CollatzResearch.WordTrace tailWord_330967 prefixEnd_330967 75531178567427477240185 := by
  unfold tailWord_330967
  simp only [CollatzResearch.WordTrace]
  refine ⟨12071358191970558508551155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8047572127980372339034103 12071358191970558508551155)
  ·
    refine ⟨18107037287955837762826733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12071358191970558508551155 18107037287955837762826733)
    ·
      refine ⟨6790138982983439161060025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18107037287955837762826733 6790138982983439161060025)
      ·
        refine ⟨5092604237237579370795019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6790138982983439161060025 5092604237237579370795019)
        ·
          refine ⟨7638906355856369056192529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5092604237237579370795019 7638906355856369056192529)
          ·
            refine ⟨5729179766892276792144397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638906355856369056192529 5729179766892276792144397)
            ·
              refine ⟨2148442412584603797054149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5729179766892276792144397 2148442412584603797054149)
              ·
                refine ⟨402832952359613211947653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148442412584603797054149 402832952359613211947653)
                ·
                  refine ⟨75531178567427477240185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402832952359613211947653 75531178567427477240185)
                  ·
                    rfl

theorem cell21_330967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_330967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_330967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_330967 prefixEnd_330967 := by exact prefixLift 330967
  have htrace : WordTrace (prefixWord ++ tailWord_330967) baseStart_330967 baseEnd_330967 := by
    simpa [prefixWord, tailWord_330967, baseEnd_330967] using wordTrace_append hprefix tailTrace_330967
  have hstable : (prefixWord ++ tailWord_330967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330967).length < 2 ^ (prefixWord ++ tailWord_330967).sum := by decide
  have hdescent : baseEnd_330967 < baseStart_330967 := by decide
  rcases family_descends (prefixWord ++ tailWord_330967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331139 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 3]
def baseStart_331139 : Nat := 118140960795 + 331139 * 2 ^ 59
def prefixEnd_331139 : Nat := 4983230072969 + 3 ^ 40 * 331139 * 2
def baseEnd_331139 : Nat := 75570431310793400373167

theorem tailTrace_331139 : CollatzResearch.WordTrace tailWord_331139 prefixEnd_331139 75570431310793400373167 := by
  unfold tailWord_331139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077631547347431883812471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8051754364898287922541647 12077631547347431883812471)
  ·
    refine ⟨18116447321021147825718707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12077631547347431883812471 18116447321021147825718707)
    ·
      refine ⟨27174670981531721738578061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18116447321021147825718707 27174670981531721738578061)
      ·
        refine ⟨10190501618074395651966773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27174670981531721738578061 10190501618074395651966773)
        ·
          refine ⟨955359526694474592371885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10190501618074395651966773 955359526694474592371885)
          ·
            refine ⟨358259822510427972139457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 955359526694474592371885 358259822510427972139457)
            ·
              refine ⟨268694866882820979104593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358259822510427972139457 268694866882820979104593)
              ·
                refine ⟨201521150162115734328445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268694866882820979104593 201521150162115734328445)
                ·
                  refine ⟨75570431310793400373167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201521150162115734328445 75570431310793400373167)
                  ·
                    rfl

theorem cell21_331139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3].length) (baseStart_331139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331139 prefixEnd_331139 := by exact prefixLift 331139
  have htrace : WordTrace (prefixWord ++ tailWord_331139) baseStart_331139 baseEnd_331139 := by
    simpa [prefixWord, tailWord_331139, baseEnd_331139] using wordTrace_append hprefix tailTrace_331139
  have hstable : (prefixWord ++ tailWord_331139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331139).length < 2 ^ (prefixWord ++ tailWord_331139).sum := by decide
  have hdescent : baseEnd_331139 < baseStart_331139 := by decide
  rcases family_descends (prefixWord ++ tailWord_331139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331226 : List Nat := [3, 1, 1, 2, 3, 2, 4, 5]
def baseStart_331226 : Nat := 118140960795 + 331226 * 2 ^ 59
def prefixEnd_331226 : Nat := 4983230072969 + 3 ^ 40 * 331226 * 2
def baseEnd_331226 : Nat := 25196761965366860807663

theorem tailTrace_331226 : CollatzResearch.WordTrace tailWord_331226 prefixEnd_331226 25196761965366860807663 := by
  unfold tailWord_331226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020201174508061435557383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8053869798688163828153021 3020201174508061435557383)
  ·
    refine ⟨4530301761762092153336075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3020201174508061435557383 4530301761762092153336075)
    ·
      refine ⟨6795452642643138230004113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530301761762092153336075 6795452642643138230004113)
      ·
        refine ⟨5096589481982353672503085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6795452642643138230004113 5096589481982353672503085)
        ·
          refine ⟨1911221055743382627188657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5096589481982353672503085 1911221055743382627188657)
          ·
            refine ⟨1433415791807536970391493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911221055743382627188657 1433415791807536970391493)
            ·
              refine ⟨268765460963913181948405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1433415791807536970391493 268765460963913181948405)
              ·
                refine ⟨25196761965366860807663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268765460963913181948405 25196761965366860807663)
                ·
                  rfl

theorem cell21_331226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_331226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331226 prefixEnd_331226 := by exact prefixLift 331226
  have htrace : WordTrace (prefixWord ++ tailWord_331226) baseStart_331226 baseEnd_331226 := by
    simpa [prefixWord, tailWord_331226, baseEnd_331226] using wordTrace_append hprefix tailTrace_331226
  have hstable : (prefixWord ++ tailWord_331226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331226).length < 2 ^ (prefixWord ++ tailWord_331226).sum := by decide
  have hdescent : baseEnd_331226 < baseStart_331226 := by decide
  rcases family_descends (prefixWord ++ tailWord_331226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331285 : List Nat := [1, 3, 2, 1, 3, 2, 2, 7]
def baseStart_331285 : Nat := 118140960795 + 331285 * 2 ^ 59
def prefixEnd_331285 : Nat := 4983230072969 + 3 ^ 40 * 331285 * 2
def baseEnd_331285 : Nat := 25201250166643196979845

theorem tailTrace_331285 : CollatzResearch.WordTrace tailWord_331285 prefixEnd_331285 25201250166643196979845 := by
  unfold tailWord_331285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082956604818498818627309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8055304403212332545751539 12082956604818498818627309)
  ·
    refine ⟨4531108726806937056985241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12082956604818498818627309 4531108726806937056985241)
    ·
      refine ⟨3398331545105202792738931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4531108726806937056985241 3398331545105202792738931)
      ·
        refine ⟨5097497317657804189108397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3398331545105202792738931 5097497317657804189108397)
        ·
          refine ⟨1911561494121676570915649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5097497317657804189108397 1911561494121676570915649)
          ·
            refine ⟨1433671120591257428186737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911561494121676570915649 1433671120591257428186737)
            ·
              refine ⟨1075253340443443071140053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433671120591257428186737 1075253340443443071140053)
              ·
                refine ⟨25201250166643196979845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1075253340443443071140053 25201250166643196979845)
                ·
                  rfl

theorem cell21_331285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_331285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331285 prefixEnd_331285 := by exact prefixLift 331285
  have htrace : WordTrace (prefixWord ++ tailWord_331285) baseStart_331285 baseEnd_331285 := by
    simpa [prefixWord, tailWord_331285, baseEnd_331285] using wordTrace_append hprefix tailTrace_331285
  have hstable : (prefixWord ++ tailWord_331285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331285).length < 2 ^ (prefixWord ++ tailWord_331285).sum := by decide
  have hdescent : baseEnd_331285 < baseStart_331285 := by decide
  rcases family_descends (prefixWord ++ tailWord_331285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331364 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_331364 : Nat := 118140960795 + 331364 * 2 ^ 59
def prefixEnd_331364 : Nat := 4983230072969 + 3 ^ 40 * 331364 * 2
def baseEnd_331364 : Nat := 75621779376243009122707

theorem tailTrace_331364 : CollatzResearch.WordTrace tailWord_331364 prefixEnd_331364 75621779376243009122707 := by
  unfold tailWord_331364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042918985766147655376573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8057225314354863540502097 6042918985766147655376573)
  ·
    refine ⟨2266094619662305370766215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6042918985766147655376573 2266094619662305370766215)
    ·
      refine ⟨3399141929493458056149323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266094619662305370766215 3399141929493458056149323)
      ·
        refine ⟨5098712894240187084223985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399141929493458056149323 5098712894240187084223985)
        ·
          refine ⟨3824034670680140313167989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5098712894240187084223985 3824034670680140313167989)
          ·
            refine ⟨358503250376263154359499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3824034670680140313167989 358503250376263154359499)
            ·
              refine ⟨537754875564394731539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358503250376263154359499 537754875564394731539249)
              ·
                refine ⟨403316156673296048654437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537754875564394731539249 403316156673296048654437)
                ·
                  refine ⟨75621779376243009122707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403316156673296048654437 75621779376243009122707)
                  ·
                    rfl

theorem cell21_331364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_331364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331364 prefixEnd_331364 := by exact prefixLift 331364
  have htrace : WordTrace (prefixWord ++ tailWord_331364) baseStart_331364 baseEnd_331364 := by
    simpa [prefixWord, tailWord_331364, baseEnd_331364] using wordTrace_append hprefix tailTrace_331364
  have hstable : (prefixWord ++ tailWord_331364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331364).length < 2 ^ (prefixWord ++ tailWord_331364).sum := by decide
  have hdescent : baseEnd_331364 < baseStart_331364 := by decide
  rcases family_descends (prefixWord ++ tailWord_331364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331381 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 4]
def baseStart_331381 : Nat := 118140960795 + 331381 * 2 ^ 59
def prefixEnd_331381 : Nat := 4983230072969 + 3 ^ 40 * 331381 * 2
def baseEnd_331381 : Nat := 75625659007854757339339

theorem tailTrace_331381 : CollatzResearch.WordTrace tailWord_331381 prefixEnd_331381 75625659007854757339339 := by
  unfold tailWord_331381
  simp only [CollatzResearch.WordTrace]
  refine ⟨12086458012470707214121997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8057638674980471476081331 12086458012470707214121997)
  ·
    refine ⟨4532421754676515205295749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12086458012470707214121997 4532421754676515205295749)
    ·
      refine ⟨849829079001846600992953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4532421754676515205295749 849829079001846600992953)
      ·
        refine ⟨637371809251384950744715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 849829079001846600992953 637371809251384950744715)
        ·
          refine ⟨956057713877077426117073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637371809251384950744715 956057713877077426117073)
          ·
            refine ⟨717043285407808069587805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956057713877077426117073 717043285407808069587805)
            ·
              refine ⟨268891232027928026095427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717043285407808069587805 268891232027928026095427)
              ·
                refine ⟨403336848041892039143141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268891232027928026095427 403336848041892039143141)
                ·
                  refine ⟨75625659007854757339339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403336848041892039143141 75625659007854757339339)
                  ·
                    rfl

theorem cell21_331381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_331381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331381 prefixEnd_331381 := by exact prefixLift 331381
  have htrace : WordTrace (prefixWord ++ tailWord_331381) baseStart_331381 baseEnd_331381 := by
    simpa [prefixWord, tailWord_331381, baseEnd_331381] using wordTrace_append hprefix tailTrace_331381
  have hstable : (prefixWord ++ tailWord_331381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331381).length < 2 ^ (prefixWord ++ tailWord_331381).sum := by decide
  have hdescent : baseEnd_331381 < baseStart_331381 := by decide
  rcases family_descends (prefixWord ++ tailWord_331381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331432 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_331432 : Nat := 118140960795 + 331432 * 2 ^ 59
def prefixEnd_331432 : Nat := 4983230072969 + 3 ^ 40 * 331432 * 2
def baseEnd_331432 : Nat := 75637297902690001989235

theorem tailTrace_331432 : CollatzResearch.WordTrace tailWord_331432 prefixEnd_331432 75637297902690001989235 := by
  unfold tailWord_331432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044159067642971462114275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8058878756857295282819033 6044159067642971462114275)
  ·
    refine ⟨9066238601464457193171413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6044159067642971462114275 9066238601464457193171413)
    ·
      refine ⟨212489967221823215464955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9066238601464457193171413 212489967221823215464955)
      ·
        refine ⟨318734950832734823197433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212489967221823215464955 318734950832734823197433)
        ·
          refine ⟨239051213124551117398075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318734950832734823197433 239051213124551117398075)
          ·
            refine ⟨358576819686826676097113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239051213124551117398075 358576819686826676097113)
            ·
              refine ⟨268932614765120007072835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358576819686826676097113 268932614765120007072835)
              ·
                refine ⟨403398922147680010609253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268932614765120007072835 403398922147680010609253)
                ·
                  refine ⟨75637297902690001989235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403398922147680010609253 75637297902690001989235)
                  ·
                    rfl

theorem cell21_331432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_331432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331432 prefixEnd_331432 := by exact prefixLift 331432
  have htrace : WordTrace (prefixWord ++ tailWord_331432) baseStart_331432 baseEnd_331432 := by
    simpa [prefixWord, tailWord_331432, baseEnd_331432] using wordTrace_append hprefix tailTrace_331432
  have hstable : (prefixWord ++ tailWord_331432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331432).length < 2 ^ (prefixWord ++ tailWord_331432).sum := by decide
  have hdescent : baseEnd_331432 < baseStart_331432 := by decide
  rcases family_descends (prefixWord ++ tailWord_331432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331451 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_331451 : Nat := 118140960795 + 331451 * 2 ^ 59
def prefixEnd_331451 : Nat := 4983230072969 + 3 ^ 40 * 331451 * 2
def baseEnd_331451 : Nat := 75641633961550191172529

theorem tailTrace_331451 : CollatzResearch.WordTrace tailWord_331451 prefixEnd_331451 75641633961550191172529 := by
  unfold tailWord_331451
  simp only [CollatzResearch.WordTrace]
  refine ⟨12089011122217109169170207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8059340748144739446113471 12089011122217109169170207)
  ·
    refine ⟨18133516683325663753755311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12089011122217109169170207 18133516683325663753755311)
    ·
      refine ⟨27200275024988495630632967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18133516683325663753755311 27200275024988495630632967)
      ·
        refine ⟨40800412537482743445949451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27200275024988495630632967 40800412537482743445949451)
        ·
          refine ⟨61200618806224115168924177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40800412537482743445949451 61200618806224115168924177)
          ·
            refine ⟨45900464104668086376693133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61200618806224115168924177 45900464104668086376693133)
            ·
              refine ⟨17212674039250532391259925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45900464104668086376693133 17212674039250532391259925)
              ·
                refine ⟨806844095589868705840309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17212674039250532391259925 806844095589868705840309)
                ·
                  refine ⟨75641633961550191172529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 806844095589868705840309 75641633961550191172529)
                  ·
                    rfl

theorem cell21_331451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_331451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331451 prefixEnd_331451 := by exact prefixLift 331451
  have htrace : WordTrace (prefixWord ++ tailWord_331451) baseStart_331451 baseEnd_331451 := by
    simpa [prefixWord, tailWord_331451, baseEnd_331451] using wordTrace_append hprefix tailTrace_331451
  have hstable : (prefixWord ++ tailWord_331451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331451).length < 2 ^ (prefixWord ++ tailWord_331451).sum := by decide
  have hdescent : baseEnd_331451 < baseStart_331451 := by decide
  rcases family_descends (prefixWord ++ tailWord_331451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331578 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_331578 : Nat := 118140960795 + 331578 * 2 ^ 59
def prefixEnd_331578 : Nat := 4983230072969 + 3 ^ 40 * 331578 * 2
def baseEnd_331578 : Nat := 75670617091826192555603

theorem tailTrace_331578 : CollatzResearch.WordTrace tailWord_331578 prefixEnd_331578 75670617091826192555603 := by
  unfold tailWord_331578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023410798189252464760847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8062428795171339906028925 3023410798189252464760847)
  ·
    refine ⟨4535116197283878697141271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3023410798189252464760847 4535116197283878697141271)
    ·
      refine ⟨6802674295925818045711907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4535116197283878697141271 6802674295925818045711907)
      ·
        refine ⟨10204011443888727068567861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802674295925818045711907 10204011443888727068567861)
        ·
          refine ⟨956626072864568162678237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10204011443888727068567861 956626072864568162678237)
          ·
            refine ⟨358734777324213061004339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 956626072864568162678237 358734777324213061004339)
            ·
              refine ⟨538102165986319591506509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358734777324213061004339 538102165986319591506509)
              ·
                refine ⟨201788312244869846814941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538102165986319591506509 201788312244869846814941)
                ·
                  refine ⟨75670617091826192555603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201788312244869846814941 75670617091826192555603)
                  ·
                    rfl

theorem cell21_331578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_331578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331578 prefixEnd_331578 := by exact prefixLift 331578
  have htrace : WordTrace (prefixWord ++ tailWord_331578) baseStart_331578 baseEnd_331578 := by
    simpa [prefixWord, tailWord_331578, baseEnd_331578] using wordTrace_append hprefix tailTrace_331578
  have hstable : (prefixWord ++ tailWord_331578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331578).length < 2 ^ (prefixWord ++ tailWord_331578).sum := by decide
  have hdescent : baseEnd_331578 < baseStart_331578 := by decide
  rcases family_descends (prefixWord ++ tailWord_331578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331637 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 3]
def baseStart_331637 : Nat := 118140960795 + 331637 * 2 ^ 59
def prefixEnd_331637 : Nat := 4983230072969 + 3 ^ 40 * 331637 * 2
def baseEnd_331637 : Nat := 75684081695655201072149

theorem tailTrace_331637 : CollatzResearch.WordTrace tailWord_331637 prefixEnd_331637 75684081695655201072149 := by
  unfold tailWord_331637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095795099543262935441165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8063863399695508623627443 12095795099543262935441165)
  ·
    refine ⟨4535923162328723600790437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12095795099543262935441165 4535923162328723600790437)
    ·
      refine ⟨850485592936635675148207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4535923162328723600790437 850485592936635675148207)
      ·
        refine ⟨1275728389404953512722311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850485592936635675148207 1275728389404953512722311)
        ·
          refine ⟨1913592584107430269083467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275728389404953512722311 1913592584107430269083467)
          ·
            refine ⟨2870388876161145403625201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913592584107430269083467 2870388876161145403625201)
            ·
              refine ⟨2152791657120859052718901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870388876161145403625201 2152791657120859052718901)
              ·
                refine ⟨201824217855080536192397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2152791657120859052718901 201824217855080536192397)
                ·
                  refine ⟨75684081695655201072149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201824217855080536192397 75684081695655201072149)
                  ·
                    rfl

theorem cell21_331637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_331637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331637 prefixEnd_331637 := by exact prefixLift 331637
  have htrace : WordTrace (prefixWord ++ tailWord_331637) baseStart_331637 baseEnd_331637 := by
    simpa [prefixWord, tailWord_331637, baseEnd_331637] using wordTrace_append hprefix tailTrace_331637
  have hstable : (prefixWord ++ tailWord_331637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331637).length < 2 ^ (prefixWord ++ tailWord_331637).sum := by decide
  have hdescent : baseEnd_331637 < baseStart_331637 := by decide
  rcases family_descends (prefixWord ++ tailWord_331637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331651 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_331651 : Nat := 118140960795 + 331651 * 2 ^ 59
def prefixEnd_331651 : Nat := 4983230072969 + 3 ^ 40 * 331651 * 2
def baseEnd_331651 : Nat := 75687276686394287838787

theorem tailTrace_331651 : CollatzResearch.WordTrace tailWord_331651 prefixEnd_331651 75687276686394287838787 := by
  unfold tailWord_331651
  simp only [CollatzResearch.WordTrace]
  refine ⟨12096305721492543326450807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8064203814328362217633871 12096305721492543326450807)
  ·
    refine ⟨18144458582238814989676211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12096305721492543326450807 18144458582238814989676211)
    ·
      refine ⟨27216687873358222484514317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18144458582238814989676211 27216687873358222484514317)
      ·
        refine ⟨10206257952509333431692869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27216687873358222484514317 10206257952509333431692869)
        ·
          refine ⟨1913673366095500018442413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10206257952509333431692869 1913673366095500018442413)
          ·
            refine ⟨717627512285812506915905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913673366095500018442413 717627512285812506915905)
            ·
              refine ⟨538220634214359380186929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717627512285812506915905 538220634214359380186929)
              ·
                refine ⟨403665475660769535140197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538220634214359380186929 403665475660769535140197)
                ·
                  refine ⟨75687276686394287838787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403665475660769535140197 75687276686394287838787)
                  ·
                    rfl

theorem cell21_331651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_331651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331651 prefixEnd_331651 := by exact prefixLift 331651
  have htrace : WordTrace (prefixWord ++ tailWord_331651) baseStart_331651 baseEnd_331651 := by
    simpa [prefixWord, tailWord_331651, baseEnd_331651] using wordTrace_append hprefix tailTrace_331651
  have hstable : (prefixWord ++ tailWord_331651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331651).length < 2 ^ (prefixWord ++ tailWord_331651).sum := by decide
  have hdescent : baseEnd_331651 < baseStart_331651 := by decide
  rcases family_descends (prefixWord ++ tailWord_331651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331727 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 4]
def baseStart_331727 : Nat := 118140960795 + 331727 * 2 ^ 59
def prefixEnd_331727 : Nat := 4983230072969 + 3 ^ 40 * 331727 * 2
def baseEnd_331727 : Nat := 75704620921835044571965

theorem tailTrace_331727 : CollatzResearch.WordTrace tailWord_331727 prefixEnd_331727 75704620921835044571965 := by
  unfold tailWord_331727
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099077669217208306217435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8066051779478138870811623 12099077669217208306217435)
  ·
    refine ⟨18148616503825812459326153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12099077669217208306217435 18148616503825812459326153)
    ·
      refine ⟨13611462377869359344494615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18148616503825812459326153 13611462377869359344494615)
      ·
        refine ⟨20417193566804039016741923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13611462377869359344494615 20417193566804039016741923)
        ·
          refine ⟨30625790350206058525112885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20417193566804039016741923 30625790350206058525112885)
          ·
            refine ⟨2871167845331817986729333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30625790350206058525112885 2871167845331817986729333)
            ·
              refine ⟨269171985499857936255875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2871167845331817986729333 269171985499857936255875)
              ·
                refine ⟨403757978249786904383813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269171985499857936255875 403757978249786904383813)
                ·
                  refine ⟨75704620921835044571965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403757978249786904383813 75704620921835044571965)
                  ·
                    rfl

theorem cell21_331727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 4].length) (baseStart_331727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331727 prefixEnd_331727 := by exact prefixLift 331727
  have htrace : WordTrace (prefixWord ++ tailWord_331727) baseStart_331727 baseEnd_331727 := by
    simpa [prefixWord, tailWord_331727, baseEnd_331727] using wordTrace_append hprefix tailTrace_331727
  have hstable : (prefixWord ++ tailWord_331727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331727).length < 2 ^ (prefixWord ++ tailWord_331727).sum := by decide
  have hdescent : baseEnd_331727 < baseStart_331727 := by decide
  rcases family_descends (prefixWord ++ tailWord_331727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331800 : List Nat := [2, 1, 2, 3, 2, 1, 1, 9]
def baseStart_331800 : Nat := 118140960795 + 331800 * 2 ^ 59
def prefixEnd_331800 : Nat := 4983230072969 + 3 ^ 40 * 331800 * 2
def baseEnd_331800 : Nat := 25240426838801046618383

theorem tailTrace_331800 : CollatzResearch.WordTrace tailWord_331800 prefixEnd_331800 25240426838801046618383 := by
  unfold tailWord_331800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6050870098976370886812427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8067826798635161182416569 6050870098976370886812427)
  ·
    refine ⟨9076305148464556330218641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6050870098976370886812427 9076305148464556330218641)
    ·
      refine ⟨6807228861348417247663981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9076305148464556330218641 6807228861348417247663981)
      ·
        refine ⟨2552710823005656467873993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6807228861348417247663981 2552710823005656467873993)
        ·
          refine ⟨1914533117254242350905495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2552710823005656467873993 1914533117254242350905495)
          ·
            refine ⟨2871799675881363526358243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914533117254242350905495 2871799675881363526358243)
            ·
              refine ⟨4307699513822045289537365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871799675881363526358243 4307699513822045289537365)
              ·
                refine ⟨25240426838801046618383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4307699513822045289537365 25240426838801046618383)
                ·
                  rfl

theorem cell21_331800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_331800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331800 prefixEnd_331800 := by exact prefixLift 331800
  have htrace : WordTrace (prefixWord ++ tailWord_331800) baseStart_331800 baseEnd_331800 := by
    simpa [prefixWord, tailWord_331800, baseEnd_331800] using wordTrace_append hprefix tailTrace_331800
  have hstable : (prefixWord ++ tailWord_331800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331800).length < 2 ^ (prefixWord ++ tailWord_331800).sum := by decide
  have hdescent : baseEnd_331800 < baseStart_331800 := by decide
  rcases family_descends (prefixWord ++ tailWord_331800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331845 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_331845 : Nat := 118140960795 + 331845 * 2 ^ 59
def prefixEnd_331845 : Nat := 4983230072969 + 3 ^ 40 * 331845 * 2
def baseEnd_331845 : Nat := 75731550129493061605057

theorem tailTrace_331845 : CollatzResearch.WordTrace tailWord_331845 prefixEnd_331845 75731550129493061605057 := by
  unfold tailWord_331845
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103381482789714459012989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068920988526476306008659 12103381482789714459012989)
  ·
    refine ⟨4538768056046142922129871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12103381482789714459012989 4538768056046142922129871)
    ·
      refine ⟨6808152084069214383194807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538768056046142922129871 6808152084069214383194807)
      ·
        refine ⟨10212228126103821574792211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6808152084069214383194807 10212228126103821574792211)
        ·
          refine ⟨15318342189155732362188317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10212228126103821574792211 15318342189155732362188317)
          ·
            refine ⟨5744378320933399635820619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15318342189155732362188317 5744378320933399635820619)
            ·
              refine ⟨8616567481400099453730929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744378320933399635820619 8616567481400099453730929)
              ·
                refine ⟨6462425611050074590298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8616567481400099453730929 6462425611050074590298197)
                ·
                  refine ⟨75731550129493061605057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6462425611050074590298197 75731550129493061605057)
                  ·
                    rfl

theorem cell21_331845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_331845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331845 prefixEnd_331845 := by exact prefixLift 331845
  have htrace : WordTrace (prefixWord ++ tailWord_331845) baseStart_331845 baseEnd_331845 := by
    simpa [prefixWord, tailWord_331845, baseEnd_331845] using wordTrace_append hprefix tailTrace_331845
  have hstable : (prefixWord ++ tailWord_331845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331845).length < 2 ^ (prefixWord ++ tailWord_331845).sum := by decide
  have hdescent : baseEnd_331845 < baseStart_331845 := by decide
  rcases family_descends (prefixWord ++ tailWord_331845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331907 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_331907 : Nat := 118140960795 + 331907 * 2 ^ 59
def prefixEnd_331907 : Nat := 4983230072969 + 3 ^ 40 * 331907 * 2
def baseEnd_331907 : Nat := 75745699374194731571597

theorem tailTrace_331907 : CollatzResearch.WordTrace tailWord_331907 prefixEnd_331907 75745699374194731571597 := by
  unfold tailWord_331907
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105642808565099047769975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8070428539043399365179983 12105642808565099047769975)
  ·
    refine ⟨18158464212847648571654963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12105642808565099047769975 18158464212847648571654963)
    ·
      refine ⟨27237696319271472857482445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18158464212847648571654963 27237696319271472857482445)
      ·
        refine ⟨10214136119726802321555917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27237696319271472857482445 10214136119726802321555917)
        ·
          refine ⟨3830301044897550870583469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10214136119726802321555917 3830301044897550870583469)
          ·
            refine ⟨1436362891836581576468801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3830301044897550870583469 1436362891836581576468801)
            ·
              refine ⟨1077272168877436182351601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436362891836581576468801 1077272168877436182351601)
              ·
                refine ⟨807954126658077136763701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077272168877436182351601 807954126658077136763701)
                ·
                  refine ⟨75745699374194731571597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 807954126658077136763701 75745699374194731571597)
                  ·
                    rfl

theorem cell21_331907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_331907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331907 prefixEnd_331907 := by exact prefixLift 331907
  have htrace : WordTrace (prefixWord ++ tailWord_331907) baseStart_331907 baseEnd_331907 := by
    simpa [prefixWord, tailWord_331907, baseEnd_331907] using wordTrace_append hprefix tailTrace_331907
  have hstable : (prefixWord ++ tailWord_331907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331907).length < 2 ^ (prefixWord ++ tailWord_331907).sum := by decide
  have hdescent : baseEnd_331907 < baseStart_331907 := by decide
  rcases family_descends (prefixWord ++ tailWord_331907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331941 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 3]
def baseStart_331941 : Nat := 118140960795 + 331941 * 2 ^ 59
def prefixEnd_331941 : Nat := 4983230072969 + 3 ^ 40 * 331941 * 2
def baseEnd_331941 : Nat := 75753458637418228004861

theorem tailTrace_331941 : CollatzResearch.WordTrace tailWord_331941 prefixEnd_331941 75753458637418228004861 := by
  unfold tailWord_331941
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106882890441922854507677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8071255260294615236338451 12106882890441922854507677)
  ·
    refine ⟨4540081083915721070440379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12106882890441922854507677 4540081083915721070440379)
    ·
      refine ⟨6810121625873581605660569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4540081083915721070440379 6810121625873581605660569)
      ·
        refine ⟨5107591219405186204245427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6810121625873581605660569 5107591219405186204245427)
        ·
          refine ⟨7661386829107779306368141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107591219405186204245427 7661386829107779306368141)
          ·
            refine ⟨2873020060915417239888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7661386829107779306368141 2873020060915417239888053)
            ·
              refine ⟨269345630710820366239505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2873020060915417239888053 269345630710820366239505)
              ·
                refine ⟨202009223033115274679629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269345630710820366239505 202009223033115274679629)
                ·
                  refine ⟨75753458637418228004861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202009223033115274679629 75753458637418228004861)
                  ·
                    rfl

theorem cell21_331941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_331941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_331941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_331941 prefixEnd_331941 := by exact prefixLift 331941
  have htrace : WordTrace (prefixWord ++ tailWord_331941) baseStart_331941 baseEnd_331941 := by
    simpa [prefixWord, tailWord_331941, baseEnd_331941] using wordTrace_append hprefix tailTrace_331941
  have hstable : (prefixWord ++ tailWord_331941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331941).length < 2 ^ (prefixWord ++ tailWord_331941).sum := by decide
  have hdescent : baseEnd_331941 < baseStart_331941 := by decide
  rcases family_descends (prefixWord ++ tailWord_331941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332000 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_332000 : Nat := 118140960795 + 332000 * 2 ^ 59
def prefixEnd_332000 : Nat := 4983230072969 + 3 ^ 40 * 332000 * 2
def baseEnd_332000 : Nat := 75766923241247236521407

theorem tailTrace_332000 : CollatzResearch.WordTrace tailWord_332000 prefixEnd_332000 75766923241247236521407 := by
  unfold tailWord_332000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054517398614087965452727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8072689864818783953936969 6054517398614087965452727)
  ·
    refine ⟨9081776097921131948179091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054517398614087965452727 9081776097921131948179091)
    ·
      refine ⟨13622664146881697922268637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9081776097921131948179091 13622664146881697922268637)
      ·
        refine ⟨5108499055080636720850739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13622664146881697922268637 5108499055080636720850739)
        ·
          refine ⟨7662748582620955081276109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5108499055080636720850739 7662748582620955081276109)
          ·
            refine ⟨2873530718482858155478541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7662748582620955081276109 2873530718482858155478541)
            ·
              refine ⟨1077574019431071808304453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2873530718482858155478541 1077574019431071808304453)
              ·
                refine ⟨202045128643325964057085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1077574019431071808304453 202045128643325964057085)
                ·
                  refine ⟨75766923241247236521407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202045128643325964057085 75766923241247236521407)
                  ·
                    rfl

theorem cell21_332000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_332000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332000 prefixEnd_332000 := by exact prefixLift 332000
  have htrace : WordTrace (prefixWord ++ tailWord_332000) baseStart_332000 baseEnd_332000 := by
    simpa [prefixWord, tailWord_332000, baseEnd_332000] using wordTrace_append hprefix tailTrace_332000
  have hstable : (prefixWord ++ tailWord_332000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332000).length < 2 ^ (prefixWord ++ tailWord_332000).sum := by decide
  have hdescent : baseEnd_332000 < baseStart_332000 := by decide
  rcases family_descends (prefixWord ++ tailWord_332000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332003 : List Nat := [1, 1, 1, 8, 2, 1, 1, 6]
def baseStart_332003 : Nat := 118140960795 + 332003 * 2 ^ 59
def prefixEnd_332003 : Nat := 4983230072969 + 3 ^ 40 * 332003 * 2
def baseEnd_332003 : Nat := 25255869294039965990467

theorem tailTrace_332003 : CollatzResearch.WordTrace tailWord_332003 prefixEnd_332003 25255869294039965990467 := by
  unfold tailWord_332003
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109144216217307443264663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8072762810811538295509775 12109144216217307443264663)
  ·
    refine ⟨18163716324325961164896995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12109144216217307443264663 18163716324325961164896995)
    ·
      refine ⟨27245574486488941747345493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18163716324325961164896995 27245574486488941747345493)
      ·
        refine ⟨319284076013542286101705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 27245574486488941747345493 319284076013542286101705)
        ·
          refine ⟨239463057010156714576279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319284076013542286101705 239463057010156714576279)
          ·
            refine ⟨359194585515235071864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239463057010156714576279 359194585515235071864419)
            ·
              refine ⟨538791878272852607796629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359194585515235071864419 538791878272852607796629)
              ·
                refine ⟨25255869294039965990467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 538791878272852607796629 25255869294039965990467)
                ·
                  rfl

theorem cell21_332003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 6].length) (baseStart_332003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332003 prefixEnd_332003 := by exact prefixLift 332003
  have htrace : WordTrace (prefixWord ++ tailWord_332003) baseStart_332003 baseEnd_332003 := by
    simpa [prefixWord, tailWord_332003, baseEnd_332003] using wordTrace_append hprefix tailTrace_332003
  have hstable : (prefixWord ++ tailWord_332003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332003).length < 2 ^ (prefixWord ++ tailWord_332003).sum := by decide
  have hdescent : baseEnd_332003 < baseStart_332003 := by decide
  rcases family_descends (prefixWord ++ tailWord_332003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332034 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_332034 : Nat := 118140960795 + 332034 * 2 ^ 59
def prefixEnd_332034 : Nat := 4983230072969 + 3 ^ 40 * 332034 * 2
def baseEnd_332034 : Nat := 75774682504470732954671

theorem tailTrace_332034 : CollatzResearch.WordTrace tailWord_332034 prefixEnd_332034 75774682504470732954671 := by
  unfold tailWord_332034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027568719776249934410789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8073516586069999825095437 3027568719776249934410789)
  ·
    refine ⟨567669134958046862702023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3027568719776249934410789 567669134958046862702023)
    ·
      refine ⟨851503702437070294053035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567669134958046862702023 851503702437070294053035)
      ·
        refine ⟨1277255553655605441079553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851503702437070294053035 1277255553655605441079553)
        ·
          refine ⟨957941665241704080809665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277255553655605441079553 957941665241704080809665)
          ·
            refine ⟨718456248931278060607249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957941665241704080809665 718456248931278060607249)
            ·
              refine ⟨538842186698458545455437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718456248931278060607249 538842186698458545455437)
              ·
                refine ⟨202065820011921954545789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538842186698458545455437 202065820011921954545789)
                ·
                  refine ⟨75774682504470732954671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202065820011921954545789 75774682504470732954671)
                  ·
                    rfl

theorem cell21_332034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_332034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332034 prefixEnd_332034 := by exact prefixLift 332034
  have htrace : WordTrace (prefixWord ++ tailWord_332034) baseStart_332034 baseEnd_332034 := by
    simpa [prefixWord, tailWord_332034, baseEnd_332034] using wordTrace_append hprefix tailTrace_332034
  have hstable : (prefixWord ++ tailWord_332034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332034).length < 2 ^ (prefixWord ++ tailWord_332034).sum := by decide
  have hdescent : baseEnd_332034 < baseStart_332034 := by decide
  rcases family_descends (prefixWord ++ tailWord_332034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332124 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_332124 : Nat := 118140960795 + 332124 * 2 ^ 59
def prefixEnd_332124 : Nat := 4983230072969 + 3 ^ 40 * 332124 * 2
def baseEnd_332124 : Nat := 75795221730650576454487

theorem tailTrace_332124 : CollatzResearch.WordTrace tailWord_332124 prefixEnd_332124 75795221730650576454487 := by
  unfold tailWord_332124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056778724389472554209713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8075704965852630072279617 6056778724389472554209713)
  ·
    refine ⟨4542584043292104415657285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6056778724389472554209713 4542584043292104415657285)
    ·
      refine ⟨851734508117269577935741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4542584043292104415657285 851734508117269577935741)
      ·
        refine ⟨319400440543976091725903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 851734508117269577935741 319400440543976091725903)
        ·
          refine ⟨479100660815964137588855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319400440543976091725903 479100660815964137588855)
          ·
            refine ⟨718650991223946206383283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479100660815964137588855 718650991223946206383283)
            ·
              refine ⟨1077976486835919309574925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718650991223946206383283 1077976486835919309574925)
              ·
                refine ⟨404241182563469741090597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1077976486835919309574925 404241182563469741090597)
                ·
                  refine ⟨75795221730650576454487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404241182563469741090597 75795221730650576454487)
                  ·
                    rfl

theorem cell21_332124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_332124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332124 prefixEnd_332124 := by exact prefixLift 332124
  have htrace : WordTrace (prefixWord ++ tailWord_332124) baseStart_332124 baseEnd_332124 := by
    simpa [prefixWord, tailWord_332124, baseEnd_332124] using wordTrace_append hprefix tailTrace_332124
  have hstable : (prefixWord ++ tailWord_332124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332124).length < 2 ^ (prefixWord ++ tailWord_332124).sum := by decide
  have hdescent : baseEnd_332124 < baseStart_332124 := by decide
  rcases family_descends (prefixWord ++ tailWord_332124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332163 : List Nat := [1, 1, 1, 3, 15]
def baseStart_332163 : Nat := 118140960795 + 332163 * 2 ^ 59
def prefixEnd_332163 : Nat := 4983230072969 + 3 ^ 40 * 332163 * 2
def baseEnd_332163 : Nat := 935853358790063892647

theorem tailTrace_332163 : CollatzResearch.WordTrace tailWord_332163 prefixEnd_332163 935853358790063892647 := by
  unfold tailWord_332163
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114979895637654769089143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8076653263758436512726095 12114979895637654769089143)
  ·
    refine ⟨18172469843456482153633715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12114979895637654769089143 18172469843456482153633715)
    ·
      refine ⟨27258704765184723230450573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18172469843456482153633715 27258704765184723230450573)
      ·
        refine ⟨10222014286944271211418965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27258704765184723230450573 10222014286944271211418965)
        ·
          refine ⟨935853358790063892647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 10222014286944271211418965 935853358790063892647)
          ·
            rfl

theorem cell21_332163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 15].length) (baseStart_332163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332163 prefixEnd_332163 := by exact prefixLift 332163
  have htrace : WordTrace (prefixWord ++ tailWord_332163) baseStart_332163 baseEnd_332163 := by
    simpa [prefixWord, tailWord_332163, baseEnd_332163] using wordTrace_append hprefix tailTrace_332163
  have hstable : (prefixWord ++ tailWord_332163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332163).length < 2 ^ (prefixWord ++ tailWord_332163).sum := by decide
  have hdescent : baseEnd_332163 < baseStart_332163 := by decide
  rcases family_descends (prefixWord ++ tailWord_332163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332169 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 3]
def baseStart_332169 : Nat := 118140960795 + 332169 * 2 ^ 59
def prefixEnd_332169 : Nat := 4983230072969 + 3 ^ 40 * 332169 * 2
def baseEnd_332169 : Nat := 75805491343740498204395

theorem tailTrace_332169 : CollatzResearch.WordTrace tailWord_332169 prefixEnd_332169 75805491343740498204395 := by
  unfold tailWord_332169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12115198733615917793807561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8076799155743945195871707 12115198733615917793807561)
  ·
    refine ⟨9086399050211938345355671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12115198733615917793807561 9086399050211938345355671)
    ·
      refine ⟨13629598575317907518033507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9086399050211938345355671 13629598575317907518033507)
      ·
        refine ⟨20444397862976861277050261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13629598575317907518033507 20444397862976861277050261)
        ·
          refine ⟨958331149827040372361731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20444397862976861277050261 958331149827040372361731)
          ·
            refine ⟨1437496724740560558542597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958331149827040372361731 1437496724740560558542597)
            ·
              refine ⟨269530635888855104726737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1437496724740560558542597 269530635888855104726737)
              ·
                refine ⟨202147976916641328545053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269530635888855104726737 202147976916641328545053)
                ·
                  refine ⟨75805491343740498204395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202147976916641328545053 75805491343740498204395)
                  ·
                    rfl

theorem cell21_332169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_332169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332169 prefixEnd_332169 := by exact prefixLift 332169
  have htrace : WordTrace (prefixWord ++ tailWord_332169) baseStart_332169 baseEnd_332169 := by
    simpa [prefixWord, tailWord_332169, baseEnd_332169] using wordTrace_append hprefix tailTrace_332169
  have hstable : (prefixWord ++ tailWord_332169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332169).length < 2 ^ (prefixWord ++ tailWord_332169).sum := by decide
  have hdescent : baseEnd_332169 < baseStart_332169 := by decide
  rcases family_descends (prefixWord ++ tailWord_332169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332239 : List Nat := [1, 1, 2, 1, 1, 4, 1, 10]
def baseStart_332239 : Nat := 118140960795 + 332239 * 2 ^ 59
def prefixEnd_332239 : Nat := 4983230072969 + 3 ^ 40 * 332239 * 2
def baseEnd_332239 : Nat := 25273822099145310679195

theorem tailTrace_332239 : CollatzResearch.WordTrace tailWord_332239 prefixEnd_332239 25273822099145310679195 := by
  unfold tailWord_332239
  simp only [CollatzResearch.WordTrace]
  refine ⟨12117751843362319748855771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8078501228908213165903847 12117751843362319748855771)
  ·
    refine ⟨18176627765043479623283657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12117751843362319748855771 18176627765043479623283657)
    ·
      refine ⟨13632470823782609717462743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18176627765043479623283657 13632470823782609717462743)
      ·
        refine ⟨20448706235673914576194115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13632470823782609717462743 20448706235673914576194115)
        ·
          refine ⟨30673059353510871864291173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20448706235673914576194115 30673059353510871864291173)
          ·
            refine ⟨5751198628783288474554595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30673059353510871864291173 5751198628783288474554595)
            ·
              refine ⟨8626797943174932711831893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751198628783288474554595 8626797943174932711831893)
              ·
                refine ⟨25273822099145310679195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8626797943174932711831893 25273822099145310679195)
                ·
                  rfl

theorem cell21_332239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_332239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332239 prefixEnd_332239 := by exact prefixLift 332239
  have htrace : WordTrace (prefixWord ++ tailWord_332239) baseStart_332239 baseEnd_332239 := by
    simpa [prefixWord, tailWord_332239, baseEnd_332239] using wordTrace_append hprefix tailTrace_332239
  have hstable : (prefixWord ++ tailWord_332239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332239).length < 2 ^ (prefixWord ++ tailWord_332239).sum := by decide
  have hdescent : baseEnd_332239 < baseStart_332239 := by decide
  rcases family_descends (prefixWord ++ tailWord_332239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332290 : List Nat := [3, 4, 1, 2, 2, 1, 2, 6]
def baseStart_332290 : Nat := 118140960795 + 332290 * 2 ^ 59
def prefixEnd_332290 : Nat := 4983230072969 + 3 ^ 40 * 332290 * 2
def baseEnd_332290 : Nat := 25277701730757058895827

theorem tailTrace_332290 : CollatzResearch.WordTrace tailWord_332290 prefixEnd_332290 25277701730757058895827 := by
  unfold tailWord_332290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029902991544388864740581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8079741310785036972641549 3029902991544388864740581)
  ·
    refine ⟨568106810914572912138859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3029902991544388864740581 568106810914572912138859)
    ·
      refine ⟨852160216371859368208289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568106810914572912138859 852160216371859368208289)
      ·
        refine ⟨639120162278894526156217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852160216371859368208289 639120162278894526156217)
        ·
          refine ⟨479340121709170894617163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639120162278894526156217 479340121709170894617163)
          ·
            refine ⟨719010182563756341925745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479340121709170894617163 719010182563756341925745)
            ·
              refine ⟨539257636922817256444309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719010182563756341925745 539257636922817256444309)
              ·
                refine ⟨25277701730757058895827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 539257636922817256444309 25277701730757058895827)
                ·
                  rfl

theorem cell21_332290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_332290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332290 prefixEnd_332290 := by exact prefixLift 332290
  have htrace : WordTrace (prefixWord ++ tailWord_332290) baseStart_332290 baseEnd_332290 := by
    simpa [prefixWord, tailWord_332290, baseEnd_332290] using wordTrace_append hprefix tailTrace_332290
  have hstable : (prefixWord ++ tailWord_332290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332290).length < 2 ^ (prefixWord ++ tailWord_332290).sum := by decide
  have hdescent : baseEnd_332290 < baseStart_332290 := by decide
  rcases family_descends (prefixWord ++ tailWord_332290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332349 : List Nat := [1, 4, 1, 3, 2, 3, 1, 6]
def baseStart_332349 : Nat := 118140960795 + 332349 * 2 ^ 59
def prefixEnd_332349 : Nat := 4983230072969 + 3 ^ 40 * 332349 * 2
def baseEnd_332349 : Nat := 25282189932033395068009

theorem tailTrace_332349 : CollatzResearch.WordTrace tailWord_332349 prefixEnd_332349 25282189932033395068009 := by
  unfold tailWord_332349
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121763872963808535360101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8081175915309205690240067 12121763872963808535360101)
  ·
    refine ⟨2272830726180714100380019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12121763872963808535360101 2272830726180714100380019)
    ·
      refine ⟨3409246089271071150570029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272830726180714100380019 3409246089271071150570029)
      ·
        refine ⟨1278467283476651681463761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3409246089271071150570029 1278467283476651681463761)
        ·
          refine ⟨958850462607488761097821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1278467283476651681463761 958850462607488761097821)
          ·
            refine ⟨359568923477808285411683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 958850462607488761097821 359568923477808285411683)
            ·
              refine ⟨539353385216712428117525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359568923477808285411683 539353385216712428117525)
              ·
                refine ⟨25282189932033395068009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 539353385216712428117525 25282189932033395068009)
                ·
                  rfl

theorem cell21_332349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 6].length) (baseStart_332349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332349 prefixEnd_332349 := by exact prefixLift 332349
  have htrace : WordTrace (prefixWord ++ tailWord_332349) baseStart_332349 baseEnd_332349 := by
    simpa [prefixWord, tailWord_332349, baseEnd_332349] using wordTrace_append hprefix tailTrace_332349
  have hstable : (prefixWord ++ tailWord_332349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332349).length < 2 ^ (prefixWord ++ tailWord_332349).sum := by decide
  have hdescent : baseEnd_332349 < baseStart_332349 := by decide
  rcases family_descends (prefixWord ++ tailWord_332349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332442 : List Nat := [3, 1, 1, 6, 2, 1, 7]
def baseStart_332442 : Nat := 118140960795 + 332442 * 2 ^ 59
def prefixEnd_332442 : Nat := 4983230072969 + 3 ^ 40 * 332442 * 2
def baseEnd_332442 : Nat := 8429754851461410017093

theorem tailTrace_332442 : CollatzResearch.WordTrace tailWord_332442 prefixEnd_332442 8429754851461410017093 := by
  unfold tailWord_332442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031288965406721354623895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8083437241084590278997053 3031288965406721354623895)
  ·
    refine ⟨4546933448110082031935843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3031288965406721354623895 4546933448110082031935843)
    ·
      refine ⟨6820400172165123047903765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546933448110082031935843 6820400172165123047903765)
      ·
        refine ⟨319706258070240142870489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6820400172165123047903765 319706258070240142870489)
        ·
          refine ⟨239779693552680107152867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319706258070240142870489 239779693552680107152867)
          ·
            refine ⟨359669540329020160729301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239779693552680107152867 359669540329020160729301)
            ·
              refine ⟨8429754851461410017093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 359669540329020160729301 8429754851461410017093)
              ·
                rfl

theorem cell21_332442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 7].length) (baseStart_332442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332442 prefixEnd_332442 := by exact prefixLift 332442
  have htrace : WordTrace (prefixWord ++ tailWord_332442) baseStart_332442 baseEnd_332442 := by
    simpa [prefixWord, tailWord_332442, baseEnd_332442] using wordTrace_append hprefix tailTrace_332442
  have hstable : (prefixWord ++ tailWord_332442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332442).length < 2 ^ (prefixWord ++ tailWord_332442).sum := by decide
  have hdescent : baseEnd_332442 < baseStart_332442 := by decide
  rcases family_descends (prefixWord ++ tailWord_332442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332453 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_332453 : Nat := 118140960795 + 332453 * 2 ^ 59
def prefixEnd_332453 : Nat := 4983230072969 + 3 ^ 40 * 332453 * 2
def baseEnd_332453 : Nat := 75870304013019115470481

theorem tailTrace_332453 : CollatzResearch.WordTrace tailWord_332453 prefixEnd_332453 75870304013019115470481 := by
  unfold tailWord_332453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125557064587034297146013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8083704709724689531430675 12125557064587034297146013)
  ·
    refine ⟨4547083899220137861429755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12125557064587034297146013 4547083899220137861429755)
    ·
      refine ⟨6820625848830206792144633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547083899220137861429755 6820625848830206792144633)
      ·
        refine ⟨5115469386622655094108475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6820625848830206792144633 5115469386622655094108475)
        ·
          refine ⟨7673204079933982641162713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115469386622655094108475 7673204079933982641162713)
          ·
            refine ⟨5754903059950486980872035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7673204079933982641162713 5754903059950486980872035)
            ·
              refine ⟨8632354589925730471308053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754903059950486980872035 8632354589925730471308053)
              ·
                refine ⟨404641621402768615842565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8632354589925730471308053 404641621402768615842565)
                ·
                  refine ⟨75870304013019115470481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404641621402768615842565 75870304013019115470481)
                  ·
                    rfl

theorem cell21_332453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_332453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332453 prefixEnd_332453 := by exact prefixLift 332453
  have htrace : WordTrace (prefixWord ++ tailWord_332453) baseStart_332453 baseEnd_332453 := by
    simpa [prefixWord, tailWord_332453, baseEnd_332453] using wordTrace_append hprefix tailTrace_332453
  have hstable : (prefixWord ++ tailWord_332453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332453).length < 2 ^ (prefixWord ++ tailWord_332453).sum := by decide
  have hdescent : baseEnd_332453 < baseStart_332453 := by decide
  rcases family_descends (prefixWord ++ tailWord_332453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332467 : List Nat := [1, 1, 1, 2, 3, 4, 1, 8]
def baseStart_332467 : Nat := 118140960795 + 332467 * 2 ^ 59
def prefixEnd_332467 : Nat := 4983230072969 + 3 ^ 40 * 332467 * 2
def baseEnd_332467 : Nat := 25291166334586067412373

theorem tailTrace_332467 : CollatzResearch.WordTrace tailWord_332467 prefixEnd_332467 25291166334586067412373 := by
  unfold tailWord_332467
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126067686536314688155655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8084045124357543125437103 12126067686536314688155655)
  ·
    refine ⟨18189101529804472032233483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12126067686536314688155655 18189101529804472032233483)
    ·
      refine ⟨27283652294706708048350225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18189101529804472032233483 27283652294706708048350225)
      ·
        refine ⟨20462739221030031036262669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27283652294706708048350225 20462739221030031036262669)
        ·
          refine ⟨7673527207886261638598501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20462739221030031036262669 7673527207886261638598501)
          ·
            refine ⟨1438786351478674057237219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7673527207886261638598501 1438786351478674057237219)
            ·
              refine ⟨2158179527218011085855829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438786351478674057237219 2158179527218011085855829)
              ·
                refine ⟨25291166334586067412373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2158179527218011085855829 25291166334586067412373)
                ·
                  rfl

theorem cell21_332467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_332467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332467 prefixEnd_332467 := by exact prefixLift 332467
  have htrace : WordTrace (prefixWord ++ tailWord_332467) baseStart_332467 baseEnd_332467 := by
    simpa [prefixWord, tailWord_332467, baseEnd_332467] using wordTrace_append hprefix tailTrace_332467
  have hstable : (prefixWord ++ tailWord_332467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332467).length < 2 ^ (prefixWord ++ tailWord_332467).sum := by decide
  have hdescent : baseEnd_332467 < baseStart_332467 := by decide
  rcases family_descends (prefixWord ++ tailWord_332467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332484 : List Nat := [2, 3, 3, 1, 1, 2, 2, 7]
def baseStart_332484 : Nat := 118140960795 + 332484 * 2 ^ 59
def prefixEnd_332484 : Nat := 4983230072969 + 3 ^ 40 * 332484 * 2
def baseEnd_332484 : Nat := 25292459545123316817917

theorem tailTrace_332484 : CollatzResearch.WordTrace tailWord_332484 prefixEnd_332484 25292459545123316817917 := by
  unfold tailWord_332484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063343863737363295762253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8084458484983151061016337 6063343863737363295762253)
  ·
    refine ⟨2273753948901511235910845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6063343863737363295762253 2273753948901511235910845)
    ·
      refine ⟨852657730838066713466567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2273753948901511235910845 852657730838066713466567)
      ·
        refine ⟨1278986596257100070199851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852657730838066713466567 1278986596257100070199851)
        ·
          refine ⟨1918479894385650105299777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278986596257100070199851 1918479894385650105299777)
          ·
            refine ⟨1438859920789237578974833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918479894385650105299777 1438859920789237578974833)
            ·
              refine ⟨1079144940591928184231125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438859920789237578974833 1079144940591928184231125)
              ·
                refine ⟨25292459545123316817917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1079144940591928184231125 25292459545123316817917)
                ·
                  rfl

theorem cell21_332484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_332484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332484 prefixEnd_332484 := by exact prefixLift 332484
  have htrace : WordTrace (prefixWord ++ tailWord_332484) baseStart_332484 baseEnd_332484 := by
    simpa [prefixWord, tailWord_332484, baseEnd_332484] using wordTrace_append hprefix tailTrace_332484
  have hstable : (prefixWord ++ tailWord_332484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332484).length < 2 ^ (prefixWord ++ tailWord_332484).sum := by decide
  have hdescent : baseEnd_332484 < baseStart_332484 := by decide
  rcases family_descends (prefixWord ++ tailWord_332484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332501 : List Nat := [1, 3, 2, 5, 2, 8]
def baseStart_332501 : Nat := 118140960795 + 332501 * 2 ^ 59
def prefixEnd_332501 : Nat := 4983230072969 + 3 ^ 40 * 332501 * 2
def baseEnd_332501 : Nat := 2810416972851174024829

theorem tailTrace_332501 : CollatzResearch.WordTrace tailWord_332501 prefixEnd_332501 2810416972851174024829 := by
  unfold tailWord_332501
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127307768413138494893357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8084871845608758996595571 12127307768413138494893357)
  ·
    refine ⟨4547740413154926935585009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12127307768413138494893357 4547740413154926935585009)
    ·
      refine ⟨3410805309866195201688757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4547740413154926935585009 3410805309866195201688757)
      ·
        refine ⟨319762997799955800158321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3410805309866195201688757 319762997799955800158321)
        ·
          refine ⟨239822248349966850118741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319762997799955800158321 239822248349966850118741)
          ·
            refine ⟨2810416972851174024829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 239822248349966850118741 2810416972851174024829)
            ·
              rfl

theorem cell21_332501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 8].length) (baseStart_332501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332501 prefixEnd_332501 := by exact prefixLift 332501
  have htrace : WordTrace (prefixWord ++ tailWord_332501) baseStart_332501 baseEnd_332501 := by
    simpa [prefixWord, tailWord_332501, baseEnd_332501] using wordTrace_append hprefix tailTrace_332501
  have hstable : (prefixWord ++ tailWord_332501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332501).length < 2 ^ (prefixWord ++ tailWord_332501).sum := by decide
  have hdescent : baseEnd_332501 < baseStart_332501 := by decide
  rcases family_descends (prefixWord ++ tailWord_332501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332529 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_332529 : Nat := 118140960795 + 332529 * 2 ^ 59
def prefixEnd_332529 : Nat := 4983230072969 + 3 ^ 40 * 332529 * 2
def baseEnd_332529 : Nat := 75887648248459872203659

theorem tailTrace_332529 : CollatzResearch.WordTrace tailWord_332529 prefixEnd_332529 75887648248459872203659 := by
  unfold tailWord_332529
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128329012311699276912641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8085552674874466184608427 12128329012311699276912641)
  ·
    refine ⟨9096246759233774457684481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12128329012311699276912641 9096246759233774457684481)
    ·
      refine ⟨6822185069425330843263361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9096246759233774457684481 6822185069425330843263361)
      ·
        refine ⟨5116638802068998132447521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6822185069425330843263361 5116638802068998132447521)
        ·
          refine ⟨3837479101551748599335641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116638802068998132447521 3837479101551748599335641)
          ·
            refine ⟨2878109326163811449501731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837479101551748599335641 2878109326163811449501731)
            ·
              refine ⟨4317163989245717174252597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878109326163811449501731 4317163989245717174252597)
              ·
                refine ⟨404734123991785985086181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4317163989245717174252597 404734123991785985086181)
                ·
                  refine ⟨75887648248459872203659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404734123991785985086181 75887648248459872203659)
                  ·
                    rfl

theorem cell21_332529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_332529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332529 prefixEnd_332529 := by exact prefixLift 332529
  have htrace : WordTrace (prefixWord ++ tailWord_332529) baseStart_332529 baseEnd_332529 := by
    simpa [prefixWord, tailWord_332529, baseEnd_332529] using wordTrace_append hprefix tailTrace_332529
  have hstable : (prefixWord ++ tailWord_332529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332529).length < 2 ^ (prefixWord ++ tailWord_332529).sum := by decide
  have hdescent : baseEnd_332529 < baseStart_332529 := by decide
  rcases family_descends (prefixWord ++ tailWord_332529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332625 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 3]
def baseStart_332625 : Nat := 118140960795 + 332625 * 2 ^ 59
def prefixEnd_332625 : Nat := 4983230072969 + 3 ^ 40 * 332625 * 2
def baseEnd_332625 : Nat := 75909556756385038603463

theorem tailTrace_332625 : CollatzResearch.WordTrace tailWord_332625 prefixEnd_332625 75909556756385038603463 := by
  unfold tailWord_332625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12131830419963907672407329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8087886946642605114938219 12131830419963907672407329)
  ·
    refine ⟨9098872814972930754305497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12131830419963907672407329 9098872814972930754305497)
    ·
      refine ⟨6824154611229698065729123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9098872814972930754305497 6824154611229698065729123)
      ·
        refine ⟨10236231916844547098593685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824154611229698065729123 10236231916844547098593685)
        ·
          refine ⟨479823371102088145246579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10236231916844547098593685 479823371102088145246579)
          ·
            refine ⟨719735056653132217869869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479823371102088145246579 719735056653132217869869)
            ·
              refine ⟨269900646244924581701201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 719735056653132217869869 269900646244924581701201)
              ·
                refine ⟨202425484683693436275901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269900646244924581701201 202425484683693436275901)
                ·
                  refine ⟨75909556756385038603463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202425484683693436275901 75909556756385038603463)
                  ·
                    rfl

theorem cell21_332625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_332625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332625 prefixEnd_332625 := by exact prefixLift 332625
  have htrace : WordTrace (prefixWord ++ tailWord_332625) baseStart_332625 baseEnd_332625 := by
    simpa [prefixWord, tailWord_332625, baseEnd_332625] using wordTrace_append hprefix tailTrace_332625
  have hstable : (prefixWord ++ tailWord_332625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332625).length < 2 ^ (prefixWord ++ tailWord_332625).sum := by decide
  have hdescent : baseEnd_332625 < baseStart_332625 := by decide
  rcases family_descends (prefixWord ++ tailWord_332625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332636 : List Nat := [2, 2, 4, 2, 1, 1, 1, 8]
def baseStart_332636 : Nat := 118140960795 + 332636 * 2 ^ 59
def prefixEnd_332636 : Nat := 4983230072969 + 3 ^ 40 * 332636 * 2
def baseEnd_332636 : Nat := 25304022368750487973369

theorem tailTrace_332636 : CollatzResearch.WordTrace tailWord_332636 prefixEnd_332636 25304022368750487973369 := by
  unfold tailWord_332636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066115811462028275528881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8088154415282704367371841 6066115811462028275528881)
  ·
    refine ⟨4549586858596521206646661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6066115811462028275528881 4549586858596521206646661)
    ·
      refine ⟨853047535986847726246249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4549586858596521206646661 853047535986847726246249)
      ·
        refine ⟨639785651990135794684687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 853047535986847726246249 639785651990135794684687)
        ·
          refine ⟨959678477985203692027031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639785651990135794684687 959678477985203692027031)
          ·
            refine ⟨1439517716977805538040547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959678477985203692027031 1439517716977805538040547)
            ·
              refine ⟨2159276575466708307060821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439517716977805538040547 2159276575466708307060821)
              ·
                refine ⟨25304022368750487973369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2159276575466708307060821 25304022368750487973369)
                ·
                  rfl

theorem cell21_332636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_332636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332636 prefixEnd_332636 := by exact prefixLift 332636
  have htrace : WordTrace (prefixWord ++ tailWord_332636) baseStart_332636 baseEnd_332636 := by
    simpa [prefixWord, tailWord_332636, baseEnd_332636] using wordTrace_append hprefix tailTrace_332636
  have hstable : (prefixWord ++ tailWord_332636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332636).length < 2 ^ (prefixWord ++ tailWord_332636).sum := by decide
  have hdescent : baseEnd_332636 < baseStart_332636 := by decide
  rcases family_descends (prefixWord ++ tailWord_332636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332664 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_332664 : Nat := 118140960795 + 332664 * 2 ^ 59
def prefixEnd_332664 : Nat := 4983230072969 + 3 ^ 40 * 332664 * 2
def baseEnd_332664 : Nat := 75918457087729637453383

theorem tailTrace_332664 : CollatzResearch.WordTrace tailWord_332664 prefixEnd_332664 75918457087729637453383 := by
  unfold tailWord_332664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066626433411308666538523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8088835244548411555384697 6066626433411308666538523)
  ·
    refine ⟨9099939650116962999807785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6066626433411308666538523 9099939650116962999807785)
    ·
      refine ⟨6824954737587722249855839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9099939650116962999807785 6824954737587722249855839)
      ·
        refine ⟨10237432106381583374783759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824954737587722249855839 10237432106381583374783759)
        ·
          refine ⟨15356148159572375062175639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237432106381583374783759 15356148159572375062175639)
          ·
            refine ⟨23034222239358562593263459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15356148159572375062175639 23034222239358562593263459)
            ·
              refine ⟨34551333359037843889895189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23034222239358562593263459 34551333359037843889895189)
              ·
                refine ⟨1619593751204898932338837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34551333359037843889895189 1619593751204898932338837)
                ·
                  refine ⟨75918457087729637453383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619593751204898932338837 75918457087729637453383)
                  ·
                    rfl

theorem cell21_332664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_332664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332664 prefixEnd_332664 := by exact prefixLift 332664
  have htrace : WordTrace (prefixWord ++ tailWord_332664) baseStart_332664 baseEnd_332664 := by
    simpa [prefixWord, tailWord_332664, baseEnd_332664] using wordTrace_append hprefix tailTrace_332664
  have hstable : (prefixWord ++ tailWord_332664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332664).length < 2 ^ (prefixWord ++ tailWord_332664).sum := by decide
  have hdescent : baseEnd_332664 < baseStart_332664 := by decide
  rcases family_descends (prefixWord ++ tailWord_332664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332681 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_332681 : Nat := 118140960795 + 332681 * 2 ^ 59
def prefixEnd_332681 : Nat := 4983230072969 + 3 ^ 40 * 332681 * 2
def baseEnd_332681 : Nat := 75922336719341385670015

theorem tailTrace_332681 : CollatzResearch.WordTrace tailWord_332681 prefixEnd_332681 75922336719341385670015 := by
  unfold tailWord_332681
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133872907761029236445897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089248605174019490963931 12133872907761029236445897)
  ·
    refine ⟨9100404680820771927334423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12133872907761029236445897 9100404680820771927334423)
    ·
      refine ⟨13650607021231157891001635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9100404680820771927334423 13650607021231157891001635)
      ·
        refine ⟨20475910531846736836502453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13650607021231157891001635 20475910531846736836502453)
        ·
          refine ⟨1919616612360631578422105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20475910531846736836502453 1919616612360631578422105)
          ·
            refine ⟨1439712459270473683816579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919616612360631578422105 1439712459270473683816579)
            ·
              refine ⟨2159568688905710525724869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439712459270473683816579 2159568688905710525724869)
              ·
                refine ⟨404919129169820723573413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2159568688905710525724869 404919129169820723573413)
                ·
                  refine ⟨75922336719341385670015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404919129169820723573413 75922336719341385670015)
                  ·
                    rfl

theorem cell21_332681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_332681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332681 prefixEnd_332681 := by exact prefixLift 332681
  have htrace : WordTrace (prefixWord ++ tailWord_332681) baseStart_332681 baseEnd_332681 := by
    simpa [prefixWord, tailWord_332681, baseEnd_332681] using wordTrace_append hprefix tailTrace_332681
  have hstable : (prefixWord ++ tailWord_332681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332681).length < 2 ^ (prefixWord ++ tailWord_332681).sum := by decide
  have hdescent : baseEnd_332681 < baseStart_332681 := by decide
  rcases family_descends (prefixWord ++ tailWord_332681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332684 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_332684 : Nat := 118140960795 + 332684 * 2 ^ 59
def prefixEnd_332684 : Nat := 4983230072969 + 3 ^ 40 * 332684 * 2
def baseEnd_332684 : Nat := 75923021360214047120009

theorem tailTrace_332684 : CollatzResearch.WordTrace tailWord_332684 prefixEnd_332684 75923021360214047120009 := by
  unfold tailWord_332684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066991163375080374402553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8089321551166773832536737 6066991163375080374402553)
  ·
    refine ⟨4550243372531310280801915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6066991163375080374402553 4550243372531310280801915)
    ·
      refine ⟨6825365058796965421202873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550243372531310280801915 6825365058796965421202873)
      ·
        refine ⟨5119023794097724065902155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6825365058796965421202873 5119023794097724065902155)
        ·
          refine ⟨7678535691146586098853233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119023794097724065902155 7678535691146586098853233)
          ·
            refine ⟨5758901768359939574139925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7678535691146586098853233 5758901768359939574139925)
            ·
              refine ⟨269948520391872167537809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5758901768359939574139925 269948520391872167537809)
              ·
                refine ⟨202461390293904125653357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269948520391872167537809 202461390293904125653357)
                ·
                  refine ⟨75923021360214047120009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202461390293904125653357 75923021360214047120009)
                  ·
                    rfl

theorem cell21_332684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_332684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332684 prefixEnd_332684 := by exact prefixLift 332684
  have htrace : WordTrace (prefixWord ++ tailWord_332684) baseStart_332684 baseEnd_332684 := by
    simpa [prefixWord, tailWord_332684, baseEnd_332684] using wordTrace_append hprefix tailTrace_332684
  have hstable : (prefixWord ++ tailWord_332684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332684).length < 2 ^ (prefixWord ++ tailWord_332684).sum := by decide
  have hdescent : baseEnd_332684 < baseStart_332684 := by decide
  rcases family_descends (prefixWord ++ tailWord_332684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332743 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 3]
def baseStart_332743 : Nat := 118140960795 + 332743 * 2 ^ 59
def prefixEnd_332743 : Nat := 4983230072969 + 3 ^ 40 * 332743 * 2
def baseEnd_332743 : Nat := 75936485964043055636555

theorem tailTrace_332743 : CollatzResearch.WordTrace tailWord_332743 prefixEnd_332743 75936485964043055636555 := by
  unfold tailWord_332743
  simp only [CollatzResearch.WordTrace]
  refine ⟨12136134233536413825202883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8090756155690942550135255 12136134233536413825202883)
  ·
    refine ⟨18204201350304620737804325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12136134233536413825202883 18204201350304620737804325)
    ·
      refine ⟨3413287753182116388338311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18204201350304620737804325 3413287753182116388338311)
      ·
        refine ⟨5119931629773174582507467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413287753182116388338311 5119931629773174582507467)
        ·
          refine ⟨7679897444659761873761201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119931629773174582507467 7679897444659761873761201)
          ·
            refine ⟨5759923083494821405320901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7679897444659761873761201 5759923083494821405320901)
            ·
              refine ⟨1079985578155279013497669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5759923083494821405320901 1079985578155279013497669)
              ·
                refine ⟨202497295904114815030813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1079985578155279013497669 202497295904114815030813)
                ·
                  refine ⟨75936485964043055636555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202497295904114815030813 75936485964043055636555)
                  ·
                    rfl

theorem cell21_332743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3].length) (baseStart_332743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332743 prefixEnd_332743 := by exact prefixLift 332743
  have htrace : WordTrace (prefixWord ++ tailWord_332743) baseStart_332743 baseEnd_332743 := by
    simpa [prefixWord, tailWord_332743, baseEnd_332743] using wordTrace_append hprefix tailTrace_332743
  have hstable : (prefixWord ++ tailWord_332743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332743).length < 2 ^ (prefixWord ++ tailWord_332743).sum := by decide
  have hdescent : baseEnd_332743 < baseStart_332743 := by decide
  rcases family_descends (prefixWord ++ tailWord_332743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332771 : List Nat := [1, 1, 1, 6, 1, 1, 3, 7]
def baseStart_332771 : Nat := 118140960795 + 332771 * 2 ^ 59
def prefixEnd_332771 : Nat := 4983230072969 + 3 ^ 40 * 332771 * 2
def baseEnd_332771 : Nat := 25314291981840409723277

theorem tailTrace_332771 : CollatzResearch.WordTrace tailWord_332771 prefixEnd_332771 25314291981840409723277 := by
  unfold tailWord_332771
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137155477434974607222167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8091436984956649738148111 12137155477434974607222167)
  ·
    refine ⟨18205733216152461910833251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137155477434974607222167 18205733216152461910833251)
    ·
      refine ⟨27308599824228692866249877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205733216152461910833251 27308599824228692866249877)
      ·
        refine ⟨1280090616760719978105463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27308599824228692866249877 1280090616760719978105463)
        ·
          refine ⟨1920135925141079967158195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280090616760719978105463 1920135925141079967158195)
          ·
            refine ⟨2880203887711619950737293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920135925141079967158195 2880203887711619950737293)
            ·
              refine ⟨1080076457891857481526485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2880203887711619950737293 1080076457891857481526485)
              ·
                refine ⟨25314291981840409723277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1080076457891857481526485 25314291981840409723277)
                ·
                  rfl

theorem cell21_332771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_332771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332771 prefixEnd_332771 := by exact prefixLift 332771
  have htrace : WordTrace (prefixWord ++ tailWord_332771) baseStart_332771 baseEnd_332771 := by
    simpa [prefixWord, tailWord_332771, baseEnd_332771] using wordTrace_append hprefix tailTrace_332771
  have hstable : (prefixWord ++ tailWord_332771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332771).length < 2 ^ (prefixWord ++ tailWord_332771).sum := by decide
  have hdescent : baseEnd_332771 < baseStart_332771 := by decide
  rcases family_descends (prefixWord ++ tailWord_332771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332878 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_332878 : Nat := 118140960795 + 332878 * 2 ^ 59
def prefixEnd_332878 : Nat := 4983230072969 + 3 ^ 40 * 332878 * 2
def baseEnd_332878 : Nat := 75967294803312820886279

theorem tailTrace_332878 : CollatzResearch.WordTrace tailWord_332878 prefixEnd_332878 75967294803312820886279 := by
  unfold tailWord_332878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517632261005916485170911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8094038725364887920911525 1517632261005916485170911)
  ·
    refine ⟨2276448391508874727756367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1517632261005916485170911 2276448391508874727756367)
    ·
      refine ⟨3414672587263312091634551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276448391508874727756367 3414672587263312091634551)
      ·
        refine ⟨5122008880894968137451827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414672587263312091634551 5122008880894968137451827)
        ·
          refine ⟨7683013321342452206177741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122008880894968137451827 7683013321342452206177741)
          ·
            refine ⟨2881129995503419577316653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7683013321342452206177741 2881129995503419577316653)
            ·
              refine ⟨1080423748313782341493745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2881129995503419577316653 1080423748313782341493745)
              ·
                refine ⟨810317811235336756120309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080423748313782341493745 810317811235336756120309)
                ·
                  refine ⟨75967294803312820886279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810317811235336756120309 75967294803312820886279)
                  ·
                    rfl

theorem cell21_332878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_332878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332878 prefixEnd_332878 := by exact prefixLift 332878
  have htrace : WordTrace (prefixWord ++ tailWord_332878) baseStart_332878 baseEnd_332878 := by
    simpa [prefixWord, tailWord_332878, baseEnd_332878] using wordTrace_append hprefix tailTrace_332878
  have hstable : (prefixWord ++ tailWord_332878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332878).length < 2 ^ (prefixWord ++ tailWord_332878).sum := by decide
  have hdescent : baseEnd_332878 < baseStart_332878 := by decide
  rcases family_descends (prefixWord ++ tailWord_332878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332895 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 3]
def baseStart_332895 : Nat := 118140960795 + 332895 * 2 ^ 59
def prefixEnd_332895 : Nat := 4983230072969 + 3 ^ 40 * 332895 * 2
def baseEnd_332895 : Nat := 75971174434924569102911

theorem tailTrace_332895 : CollatzResearch.WordTrace tailWord_332895 prefixEnd_332895 75971174434924569102911 := by
  unfold tailWord_332895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12141678128985743784736139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8094452085990495856490759 12141678128985743784736139)
  ·
    refine ⟨18212517193478615677104209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12141678128985743784736139 18212517193478615677104209)
    ·
      refine ⟨13659387895108961757828157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18212517193478615677104209 13659387895108961757828157)
      ·
        refine ⟨5122270460665860659185559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13659387895108961757828157 5122270460665860659185559)
        ·
          refine ⟨7683405690998790988778339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122270460665860659185559 7683405690998790988778339)
          ·
            refine ⟨11525108536498186483167509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683405690998790988778339 11525108536498186483167509)
            ·
              refine ⟨540239462648352491398477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11525108536498186483167509 540239462648352491398477)
              ·
                refine ⟨202589798493132184274429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540239462648352491398477 202589798493132184274429)
                ·
                  refine ⟨75971174434924569102911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202589798493132184274429 75971174434924569102911)
                  ·
                    rfl

theorem cell21_332895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3].length) (baseStart_332895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332895 prefixEnd_332895 := by exact prefixLift 332895
  have htrace : WordTrace (prefixWord ++ tailWord_332895) baseStart_332895 baseEnd_332895 := by
    simpa [prefixWord, tailWord_332895, baseEnd_332895] using wordTrace_append hprefix tailTrace_332895
  have hstable : (prefixWord ++ tailWord_332895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332895).length < 2 ^ (prefixWord ++ tailWord_332895).sum := by decide
  have hdescent : baseEnd_332895 < baseStart_332895 := by decide
  rcases family_descends (prefixWord ++ tailWord_332895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332909 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_332909 : Nat := 118140960795 + 332909 * 2 ^ 59
def prefixEnd_332909 : Nat := 4983230072969 + 3 ^ 40 * 332909 * 2
def baseEnd_332909 : Nat := 75974369425663655869549

theorem tailTrace_332909 : CollatzResearch.WordTrace tailWord_332909 prefixEnd_332909 75974369425663655869549 := by
  unfold tailWord_332909
  simp only [CollatzResearch.WordTrace]
  refine ⟨12142188750935024175745781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8094792500623349450497187 12142188750935024175745781)
  ·
    refine ⟨1138330195400158516476167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12142188750935024175745781 1138330195400158516476167)
    ·
      refine ⟨1707495293100237774714251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138330195400158516476167 1707495293100237774714251)
      ·
        refine ⟨2561242939650356662071377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707495293100237774714251 2561242939650356662071377)
        ·
          refine ⟨1920932204737767496553533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2561242939650356662071377 1920932204737767496553533)
          ·
            refine ⟨720349576776662811207575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1920932204737767496553533 720349576776662811207575)
            ·
              refine ⟨1080524365164994216811363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720349576776662811207575 1080524365164994216811363)
              ·
                refine ⟨1620786547747491325217045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080524365164994216811363 1620786547747491325217045)
                ·
                  refine ⟨75974369425663655869549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1620786547747491325217045 75974369425663655869549)
                  ·
                    rfl

theorem cell21_332909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_332909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332909 prefixEnd_332909 := by exact prefixLift 332909
  have htrace : WordTrace (prefixWord ++ tailWord_332909) baseStart_332909 baseEnd_332909 := by
    simpa [prefixWord, tailWord_332909, baseEnd_332909] using wordTrace_append hprefix tailTrace_332909
  have hstable : (prefixWord ++ tailWord_332909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332909).length < 2 ^ (prefixWord ++ tailWord_332909).sum := by decide
  have hdescent : baseEnd_332909 < baseStart_332909 := by decide
  rcases family_descends (prefixWord ++ tailWord_332909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332985 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_332985 : Nat := 118140960795 + 332985 * 2 ^ 59
def prefixEnd_332985 : Nat := 4983230072969 + 3 ^ 40 * 332985 * 2
def baseEnd_332985 : Nat := 75991713661104412602727

theorem tailTrace_332985 : CollatzResearch.WordTrace tailWord_332985 prefixEnd_332985 75991713661104412602727 := by
  unfold tailWord_332985
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144960698659689155512409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8096640465773126103674939 12144960698659689155512409)
  ·
    refine ⟨9108720523994766866634307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12144960698659689155512409 9108720523994766866634307)
    ·
      refine ⟨13663080785992150299951461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9108720523994766866634307 13663080785992150299951461)
      ·
        refine ⟨2561827647373528181240899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13663080785992150299951461 2561827647373528181240899)
        ·
          refine ⟨3842741471060292271861349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561827647373528181240899 3842741471060292271861349)
          ·
            refine ⟨720514025823804800974003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3842741471060292271861349 720514025823804800974003)
            ·
              refine ⟨1080771038735707201461005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720514025823804800974003 1080771038735707201461005)
              ·
                refine ⟨405289139525890200547877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080771038735707201461005 405289139525890200547877)
                ·
                  refine ⟨75991713661104412602727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405289139525890200547877 75991713661104412602727)
                  ·
                    rfl

theorem cell21_332985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_332985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_332985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_332985 prefixEnd_332985 := by exact prefixLift 332985
  have htrace : WordTrace (prefixWord ++ tailWord_332985) baseStart_332985 baseEnd_332985 := by
    simpa [prefixWord, tailWord_332985, baseEnd_332985] using wordTrace_append hprefix tailTrace_332985
  have hstable : (prefixWord ++ tailWord_332985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332985).length < 2 ^ (prefixWord ++ tailWord_332985).sum := by decide
  have hdescent : baseEnd_332985 < baseStart_332985 := by decide
  rcases family_descends (prefixWord ++ tailWord_332985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333064 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_333064 : Nat := 118140960795 + 333064 * 2 ^ 59
def prefixEnd_333064 : Nat := 4983230072969 + 3 ^ 40 * 333064 * 2
def baseEnd_333064 : Nat := 76009742537417830785899

theorem tailTrace_333064 : CollatzResearch.WordTrace tailWord_333064 prefixEnd_333064 76009742537417830785899 := by
  unfold tailWord_333064
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073921032686742823819123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8098561376915657098425497 6073921032686742823819123)
  ·
    refine ⟨9110881549030114235728685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6073921032686742823819123 9110881549030114235728685)
    ·
      refine ⟨3416580580886292838398257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9110881549030114235728685 3416580580886292838398257)
      ·
        refine ⟨2562435435664719628798693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3416580580886292838398257 2562435435664719628798693)
        ·
          refine ⟨480456644187134930399755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2562435435664719628798693 480456644187134930399755)
          ·
            refine ⟨720684966280702395599633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480456644187134930399755 720684966280702395599633)
            ·
              refine ⟨540513724710526796699725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720684966280702395599633 540513724710526796699725)
              ·
                refine ⟨202692646766447548762397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540513724710526796699725 202692646766447548762397)
                ·
                  refine ⟨76009742537417830785899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202692646766447548762397 76009742537417830785899)
                  ·
                    rfl

theorem cell21_333064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_333064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333064 prefixEnd_333064 := by exact prefixLift 333064
  have htrace : WordTrace (prefixWord ++ tailWord_333064) baseStart_333064 baseEnd_333064 := by
    simpa [prefixWord, tailWord_333064, baseEnd_333064] using wordTrace_append hprefix tailTrace_333064
  have hstable : (prefixWord ++ tailWord_333064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333064).length < 2 ^ (prefixWord ++ tailWord_333064).sum := by decide
  have hdescent : baseEnd_333064 < baseStart_333064 := by decide
  rcases family_descends (prefixWord ++ tailWord_333064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333106 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_333106 : Nat := 118140960795 + 333106 * 2 ^ 59
def prefixEnd_333106 : Nat := 4983230072969 + 3 ^ 40 * 333106 * 2
def baseEnd_333106 : Nat := 76019327509635091085813

theorem tailTrace_333106 : CollatzResearch.WordTrace tailWord_333106 prefixEnd_333106 76019327509635091085813 := by
  unfold tailWord_333106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037343482805331705166793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8099582620814217880444781 3037343482805331705166793)
  ·
    refine ⟨2278007612103998778875095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3037343482805331705166793 2278007612103998778875095)
    ·
      refine ⟨3417011418155998168312643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278007612103998778875095 3417011418155998168312643)
      ·
        refine ⟨5125517127233997252468965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417011418155998168312643 5125517127233997252468965)
        ·
          refine ⟨961034461356374484837931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5125517127233997252468965 961034461356374484837931)
          ·
            refine ⟨1441551692034561727256897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961034461356374484837931 1441551692034561727256897)
            ·
              refine ⟨1081163769025921295442673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441551692034561727256897 1081163769025921295442673)
              ·
                refine ⟨810872826769440971582005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081163769025921295442673 810872826769440971582005)
                ·
                  refine ⟨76019327509635091085813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810872826769440971582005 76019327509635091085813)
                  ·
                    rfl

theorem cell21_333106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_333106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333106 prefixEnd_333106 := by exact prefixLift 333106
  have htrace : WordTrace (prefixWord ++ tailWord_333106) baseStart_333106 baseEnd_333106 := by
    simpa [prefixWord, tailWord_333106, baseEnd_333106] using wordTrace_append hprefix tailTrace_333106
  have hstable : (prefixWord ++ tailWord_333106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333106).length < 2 ^ (prefixWord ++ tailWord_333106).sum := by decide
  have hdescent : baseEnd_333106 < baseStart_333106 := by decide
  rcases family_descends (prefixWord ++ tailWord_333106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333126 : List Nat := [6, 1, 1, 3, 1, 2, 7]
def baseStart_333126 : Nat := 118140960795 + 333126 * 2 ^ 59
def prefixEnd_333126 : Nat := 4983230072969 + 3 ^ 40 * 333126 * 2
def baseEnd_333126 : Nat := 8447099086902166750271

theorem tailTrace_333126 : CollatzResearch.WordTrace tailWord_333126 prefixEnd_333126 8447099086902166750271 := by
  unfold tailWord_333126
  simp only [CollatzResearch.WordTrace]
  refine ⟨379690730973402194887351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8100068927432580157596821 379690730973402194887351)
  ·
    refine ⟨569536096460103292331027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 379690730973402194887351 569536096460103292331027)
    ·
      refine ⟨854304144690154938496541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569536096460103292331027 854304144690154938496541)
      ·
        refine ⟨320364054258808101936203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 854304144690154938496541 320364054258808101936203)
        ·
          refine ⟨480546081388212152904305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320364054258808101936203 480546081388212152904305)
          ·
            refine ⟨360409561041159114678229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480546081388212152904305 360409561041159114678229)
            ·
              refine ⟨8447099086902166750271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 360409561041159114678229 8447099086902166750271)
              ·
                rfl

theorem cell21_333126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 7].length) (baseStart_333126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333126 prefixEnd_333126 := by exact prefixLift 333126
  have htrace : WordTrace (prefixWord ++ tailWord_333126) baseStart_333126 baseEnd_333126 := by
    simpa [prefixWord, tailWord_333126, baseEnd_333126] using wordTrace_append hprefix tailTrace_333126
  have hstable : (prefixWord ++ tailWord_333126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333126).length < 2 ^ (prefixWord ++ tailWord_333126).sum := by decide
  have hdescent : baseEnd_333126 < baseStart_333126 := by decide
  rcases family_descends (prefixWord ++ tailWord_333126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333140 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_333140 : Nat := 118140960795 + 333140 * 2 ^ 59
def prefixEnd_333140 : Nat := 4983230072969 + 3 ^ 40 * 333140 * 2
def baseEnd_333140 : Nat := 76027086772858587519077

theorem tailTrace_333140 : CollatzResearch.WordTrace tailWord_333140 prefixEnd_333140 76027086772858587519077 := by
  unfold tailWord_333140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075307006549075313702437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8100409342065433751603249 6075307006549075313702437)
  ·
    refine ⟨1139120063727951621319207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6075307006549075313702437 1139120063727951621319207)
    ·
      refine ⟨1708680095591927431978811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1139120063727951621319207 1708680095591927431978811)
      ·
        refine ⟨2563020143387891147968217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708680095591927431978811 2563020143387891147968217)
        ·
          refine ⟨1922265107540918360976163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563020143387891147968217 1922265107540918360976163)
          ·
            refine ⟨2883397661311377541464245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922265107540918360976163 2883397661311377541464245)
            ·
              refine ⟨270318530747941644512273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2883397661311377541464245 270318530747941644512273)
              ·
                refine ⟨202738898060956233384205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270318530747941644512273 202738898060956233384205)
                ·
                  refine ⟨76027086772858587519077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202738898060956233384205 76027086772858587519077)
                  ·
                    rfl

theorem cell21_333140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_333140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333140 prefixEnd_333140 := by exact prefixLift 333140
  have htrace : WordTrace (prefixWord ++ tailWord_333140) baseStart_333140 baseEnd_333140 := by
    simpa [prefixWord, tailWord_333140, baseEnd_333140] using wordTrace_append hprefix tailTrace_333140
  have hstable : (prefixWord ++ tailWord_333140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333140).length < 2 ^ (prefixWord ++ tailWord_333140).sum := by decide
  have hdescent : baseEnd_333140 < baseStart_333140 := by decide
  rcases family_descends (prefixWord ++ tailWord_333140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333202 : List Nat := [3, 2, 3, 3, 2, 1, 1, 6]
def baseStart_333202 : Nat := 118140960795 + 333202 * 2 ^ 59
def prefixEnd_333202 : Nat := 4983230072969 + 3 ^ 40 * 333202 * 2
def baseEnd_333202 : Nat := 25347078672520085828539

theorem tailTrace_333202 : CollatzResearch.WordTrace tailWord_333202 prefixEnd_333202 25347078672520085828539 := by
  unfold tailWord_333202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038218834718383804040465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8101916892582356810774573 3038218834718383804040465)
  ·
    refine ⟨2278664126038787853030349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3038218834718383804040465 2278664126038787853030349)
    ·
      refine ⟨854499047264545444886381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2278664126038787853030349 854499047264545444886381)
      ·
        refine ⟨320437142724204541832393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 854499047264545444886381 320437142724204541832393)
        ·
          refine ⟨240327857043153406374295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320437142724204541832393 240327857043153406374295)
          ·
            refine ⟨360491785564730109561443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240327857043153406374295 360491785564730109561443)
            ·
              refine ⟨540737678347095164342165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360491785564730109561443 540737678347095164342165)
              ·
                refine ⟨25347078672520085828539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 540737678347095164342165 25347078672520085828539)
                ·
                  rfl

theorem cell21_333202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_333202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333202 prefixEnd_333202 := by exact prefixLift 333202
  have htrace : WordTrace (prefixWord ++ tailWord_333202) baseStart_333202 baseEnd_333202 := by
    simpa [prefixWord, tailWord_333202, baseEnd_333202] using wordTrace_append hprefix tailTrace_333202
  have hstable : (prefixWord ++ tailWord_333202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333202).length < 2 ^ (prefixWord ++ tailWord_333202).sum := by decide
  have hdescent : baseEnd_333202 < baseStart_333202 := by decide
  rcases family_descends (prefixWord ++ tailWord_333202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333213 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_333213 : Nat := 118140960795 + 333213 * 2 ^ 59
def prefixEnd_333213 : Nat := 4983230072969 + 3 ^ 40 * 333213 * 2
def baseEnd_333213 : Nat := 76043746367426682802261

theorem tailTrace_333213 : CollatzResearch.WordTrace tailWord_333213 prefixEnd_333213 76043746367426682802261 := by
  unfold tailWord_333213
  simp only [CollatzResearch.WordTrace]
  refine ⟨12153276541833684094812293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8102184361222456063208195 12153276541833684094812293)
  ·
    refine ⟨2278739351593815767777305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12153276541833684094812293 2278739351593815767777305)
    ·
      refine ⟨1709054513695361825832979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2278739351593815767777305 1709054513695361825832979)
      ·
        refine ⟨2563581770543042738749469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709054513695361825832979 2563581770543042738749469)
        ·
          refine ⟨961343163953641027031051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2563581770543042738749469 961343163953641027031051)
          ·
            refine ⟨1442014745930461540546577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961343163953641027031051 1442014745930461540546577)
            ·
              refine ⟨1081511059447846155409933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442014745930461540546577 1081511059447846155409933)
              ·
                refine ⟨405566647292942308278725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081511059447846155409933 405566647292942308278725)
                ·
                  refine ⟨76043746367426682802261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405566647292942308278725 76043746367426682802261)
                  ·
                    rfl

theorem cell21_333213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_333213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333213 prefixEnd_333213 := by exact prefixLift 333213
  have htrace : WordTrace (prefixWord ++ tailWord_333213) baseStart_333213 baseEnd_333213 := by
    simpa [prefixWord, tailWord_333213, baseEnd_333213] using wordTrace_append hprefix tailTrace_333213
  have hstable : (prefixWord ++ tailWord_333213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333213).length < 2 ^ (prefixWord ++ tailWord_333213).sum := by decide
  have hdescent : baseEnd_333213 < baseStart_333213 := by decide
  rcases family_descends (prefixWord ++ tailWord_333213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333250 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_333250 : Nat := 118140960795 + 333250 * 2 ^ 59
def prefixEnd_333250 : Nat := 4983230072969 + 3 ^ 40 * 333250 * 2
def baseEnd_333250 : Nat := 76052190271522840685519

theorem tailTrace_333250 : CollatzResearch.WordTrace tailWord_333250 prefixEnd_333250 76052190271522840685519 := by
  unfold tailWord_333250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038656510674909853477301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8103084028466426275939469 3038656510674909853477301)
  ·
    refine ⟨284874047875772798763497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3038656510674909853477301 284874047875772798763497)
    ·
      refine ⟨213655535906829599072623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284874047875772798763497 213655535906829599072623)
      ·
        refine ⟨320483303860244398608935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213655535906829599072623 320483303860244398608935)
        ·
          refine ⟨480724955790366597913403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320483303860244398608935 480724955790366597913403)
          ·
            refine ⟨721087433685549896870105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480724955790366597913403 721087433685549896870105)
            ·
              refine ⟨540815575264162422652579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721087433685549896870105 540815575264162422652579)
              ·
                refine ⟨811223362896243633978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540815575264162422652579 811223362896243633978869)
                ·
                  refine ⟨76052190271522840685519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811223362896243633978869 76052190271522840685519)
                  ·
                    rfl

theorem cell21_333250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_333250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333250 prefixEnd_333250 := by exact prefixLift 333250
  have htrace : WordTrace (prefixWord ++ tailWord_333250) baseStart_333250 baseEnd_333250 := by
    simpa [prefixWord, tailWord_333250, baseEnd_333250] using wordTrace_append hprefix tailTrace_333250
  have hstable : (prefixWord ++ tailWord_333250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333250).length < 2 ^ (prefixWord ++ tailWord_333250).sum := by decide
  have hdescent : baseEnd_333250 < baseStart_333250 := by decide
  rcases family_descends (prefixWord ++ tailWord_333250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333258 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_333258 : Nat := 118140960795 + 333258 * 2 ^ 59
def prefixEnd_333258 : Nat := 4983230072969 + 3 ^ 40 * 333258 * 2
def baseEnd_333258 : Nat := 76054015980516604552169

theorem tailTrace_333258 : CollatzResearch.WordTrace tailWord_333258 prefixEnd_333258 76054015980516604552169 := by
  unfold tailWord_333258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038729456667664195050107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8103278551113771186800285 3038729456667664195050107)
  ·
    refine ⟨4558094185001496292575161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3038729456667664195050107 4558094185001496292575161)
    ·
      refine ⟨3418570638751122219431371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558094185001496292575161 3418570638751122219431371)
      ·
        refine ⟨5127855958126683329147057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418570638751122219431371 5127855958126683329147057)
        ·
          refine ⟨3845891968595012496860293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5127855958126683329147057 3845891968595012496860293)
          ·
            refine ⟨721104744111564843161305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3845891968595012496860293 721104744111564843161305)
            ·
              refine ⟨540828558083673632370979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721104744111564843161305 540828558083673632370979)
              ·
                refine ⟨811242837125510448556469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540828558083673632370979 811242837125510448556469)
                ·
                  refine ⟨76054015980516604552169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811242837125510448556469 76054015980516604552169)
                  ·
                    rfl

theorem cell21_333258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_333258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333258 prefixEnd_333258 := by exact prefixLift 333258
  have htrace : WordTrace (prefixWord ++ tailWord_333258) baseStart_333258 baseEnd_333258 := by
    simpa [prefixWord, tailWord_333258, baseEnd_333258] using wordTrace_append hprefix tailTrace_333258
  have hstable : (prefixWord ++ tailWord_333258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333258).length < 2 ^ (prefixWord ++ tailWord_333258).sum := by decide
  have hdescent : baseEnd_333258 < baseStart_333258 := by decide
  rcases family_descends (prefixWord ++ tailWord_333258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333272 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_333272 : Nat := 118140960795 + 333272 * 2 ^ 59
def prefixEnd_333272 : Nat := 4983230072969 + 3 ^ 40 * 333272 * 2
def baseEnd_333272 : Nat := 76057210971255691318807

theorem tailTrace_333272 : CollatzResearch.WordTrace tailWord_333272 prefixEnd_333272 76057210971255691318807 := by
  unfold tailWord_333272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077714224309968585605035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8103618965746624780806713 6077714224309968585605035)
  ·
    refine ⟨9116571336464952878407553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6077714224309968585605035 9116571336464952878407553)
    ·
      refine ⟨6837428502348714658805665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9116571336464952878407553 6837428502348714658805665)
      ·
        refine ⟨5128071376761535994104249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6837428502348714658805665 5128071376761535994104249)
        ·
          refine ⟨3846053532571151995578187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5128071376761535994104249 3846053532571151995578187)
          ·
            refine ⟨5769080298856727993367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846053532571151995578187 5769080298856727993367281)
            ·
              refine ⟨4326810224142545995025461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769080298856727993367281 4326810224142545995025461)
              ·
                refine ⟨405638458513363687033637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4326810224142545995025461 405638458513363687033637)
                ·
                  refine ⟨76057210971255691318807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405638458513363687033637 76057210971255691318807)
                  ·
                    rfl

theorem cell21_333272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_333272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333272 prefixEnd_333272 := by exact prefixLift 333272
  have htrace : WordTrace (prefixWord ++ tailWord_333272) baseStart_333272 baseEnd_333272 := by
    simpa [prefixWord, tailWord_333272, baseEnd_333272] using wordTrace_append hprefix tailTrace_333272
  have hstable : (prefixWord ++ tailWord_333272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333272).length < 2 ^ (prefixWord ++ tailWord_333272).sum := by decide
  have hdescent : baseEnd_333272 < baseStart_333272 := by decide
  rcases family_descends (prefixWord ++ tailWord_333272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333323 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 4]
def baseStart_333323 : Nat := 118140960795 + 333323 * 2 ^ 59
def prefixEnd_333323 : Nat := 4983230072969 + 3 ^ 40 * 333323 * 2
def baseEnd_333323 : Nat := 76068849866090935968703

theorem tailTrace_333323 : CollatzResearch.WordTrace tailWord_333323 prefixEnd_333323 76068849866090935968703 := by
  unfold tailWord_333323
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157288571435172881316623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8104859047623448587544415 12157288571435172881316623)
  ·
    refine ⟨18235932857152759321974935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12157288571435172881316623 18235932857152759321974935)
    ·
      refine ⟨27353899285729138982962403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18235932857152759321974935 27353899285729138982962403)
      ·
        refine ⟨41030848928593708474443605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27353899285729138982962403 41030848928593708474443605)
        ·
          refine ⟨240415130440978760592443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 41030848928593708474443605 240415130440978760592443)
          ·
            refine ⟨360622695661468140888665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240415130440978760592443 360622695661468140888665)
            ·
              refine ⟨270467021746101105666499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360622695661468140888665 270467021746101105666499)
              ·
                refine ⟨405700532619151658499749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270467021746101105666499 405700532619151658499749)
                ·
                  refine ⟨76068849866090935968703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405700532619151658499749 76068849866090935968703)
                  ·
                    rfl

theorem cell21_333323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4].length) (baseStart_333323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333323 prefixEnd_333323 := by exact prefixLift 333323
  have htrace : WordTrace (prefixWord ++ tailWord_333323) baseStart_333323 baseEnd_333323 := by
    simpa [prefixWord, tailWord_333323, baseEnd_333323] using wordTrace_append hprefix tailTrace_333323
  have hstable : (prefixWord ++ tailWord_333323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333323).length < 2 ^ (prefixWord ++ tailWord_333323).sum := by decide
  have hdescent : baseEnd_333323 < baseStart_333323 := by decide
  rcases family_descends (prefixWord ++ tailWord_333323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333365 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_333365 : Nat := 118140960795 + 333365 * 2 ^ 59
def prefixEnd_333365 : Nat := 4983230072969 + 3 ^ 40 * 333365 * 2
def baseEnd_333365 : Nat := 76078434838308196268617

theorem tailTrace_333365 : CollatzResearch.WordTrace tailWord_333365 prefixEnd_333365 76078434838308196268617 := by
  unfold tailWord_333365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158820437283014054345549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8105880291522009369563699 12158820437283014054345549)
  ·
    refine ⟨4559557663981130270379581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12158820437283014054345549 4559557663981130270379581)
    ·
      refine ⟨1709834123992923851392343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4559557663981130270379581 1709834123992923851392343)
      ·
        refine ⟨2564751185989385777088515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709834123992923851392343 2564751185989385777088515)
        ·
          refine ⟨3847126778984078665632773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564751185989385777088515 3847126778984078665632773)
          ·
            refine ⟨721336271059514749806145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3847126778984078665632773 721336271059514749806145)
            ·
              refine ⟨541002203294636062354609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721336271059514749806145 541002203294636062354609)
              ·
                refine ⟨405751652470977046765957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541002203294636062354609 405751652470977046765957)
                ·
                  refine ⟨76078434838308196268617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405751652470977046765957 76078434838308196268617)
                  ·
                    rfl

theorem cell21_333365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_333365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333365 prefixEnd_333365 := by exact prefixLift 333365
  have htrace : WordTrace (prefixWord ++ tailWord_333365) baseStart_333365 baseEnd_333365 := by
    simpa [prefixWord, tailWord_333365, baseEnd_333365] using wordTrace_append hprefix tailTrace_333365
  have hstable : (prefixWord ++ tailWord_333365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333365).length < 2 ^ (prefixWord ++ tailWord_333365).sum := by decide
  have hdescent : baseEnd_333365 < baseStart_333365 := by decide
  rcases family_descends (prefixWord ++ tailWord_333365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333368 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_333368 : Nat := 118140960795 + 333368 * 2 ^ 59
def prefixEnd_333368 : Nat := 4983230072969 + 3 ^ 40 * 333368 * 2
def baseEnd_333368 : Nat := 76079119479180857718611

theorem tailTrace_333368 : CollatzResearch.WordTrace tailWord_333368 prefixEnd_333368 76079119479180857718611 := by
  unfold tailWord_333368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6079464928136072783352379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8105953237514763711136505 6079464928136072783352379)
  ·
    refine ⟨9119197392204109175028569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6079464928136072783352379 9119197392204109175028569)
    ·
      refine ⟨6839398044153081881271427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9119197392204109175028569 6839398044153081881271427)
      ·
        refine ⟨10259097066229622821907141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839398044153081881271427 10259097066229622821907141)
        ·
          refine ⟨1923580699918054279107589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10259097066229622821907141 1923580699918054279107589)
          ·
            refine ⟨360671381234635177332673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1923580699918054279107589 360671381234635177332673)
            ·
              refine ⟨270503535925976382999505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360671381234635177332673 270503535925976382999505)
              ·
                refine ⟨202877651944482287249629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270503535925976382999505 202877651944482287249629)
                ·
                  refine ⟨76079119479180857718611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202877651944482287249629 76079119479180857718611)
                  ·
                    rfl

theorem cell21_333368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_333368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333368 prefixEnd_333368 := by exact prefixLift 333368
  have htrace : WordTrace (prefixWord ++ tailWord_333368) baseStart_333368 baseEnd_333368 := by
    simpa [prefixWord, tailWord_333368, baseEnd_333368] using wordTrace_append hprefix tailTrace_333368
  have hstable : (prefixWord ++ tailWord_333368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333368).length < 2 ^ (prefixWord ++ tailWord_333368).sum := by decide
  have hdescent : baseEnd_333368 < baseStart_333368 := by decide
  rcases family_descends (prefixWord ++ tailWord_333368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333393 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_333393 : Nat := 118140960795 + 333393 * 2 ^ 59
def prefixEnd_333393 : Nat := 4983230072969 + 3 ^ 40 * 333393 * 2
def baseEnd_333393 : Nat := 76084824819786369801893

theorem tailTrace_333393 : CollatzResearch.WordTrace tailWord_333393 prefixEnd_333393 76084824819786369801893 := by
  unfold tailWord_333393
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159841681181574836364833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8106561120787716557576555 12159841681181574836364833)
  ·
    refine ⟨9119881260886181127273625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12159841681181574836364833 9119881260886181127273625)
    ·
      refine ⟨6839910945664635845455219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9119881260886181127273625 6839910945664635845455219)
      ·
        refine ⟨10259866418496953768182829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839910945664635845455219 10259866418496953768182829)
        ·
          refine ⟨3847449906936357663068561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10259866418496953768182829 3847449906936357663068561)
          ·
            refine ⟨2885587430202268247301421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847449906936357663068561 2885587430202268247301421)
            ·
              refine ⟨1082095286325850592738033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2885587430202268247301421 1082095286325850592738033)
              ·
                refine ⟨811571464744387944553525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082095286325850592738033 811571464744387944553525)
                ·
                  refine ⟨76084824819786369801893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811571464744387944553525 76084824819786369801893)
                  ·
                    rfl

theorem cell21_333393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_333393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333393 prefixEnd_333393 := by exact prefixLift 333393
  have htrace : WordTrace (prefixWord ++ tailWord_333393) baseStart_333393 baseEnd_333393 := by
    simpa [prefixWord, tailWord_333393, baseEnd_333393] using wordTrace_append hprefix tailTrace_333393
  have hstable : (prefixWord ++ tailWord_333393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333393).length < 2 ^ (prefixWord ++ tailWord_333393).sum := by decide
  have hdescent : baseEnd_333393 < baseStart_333393 := by decide
  rcases family_descends (prefixWord ++ tailWord_333393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333424 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_333424 : Nat := 118140960795 + 333424 * 2 ^ 59
def prefixEnd_333424 : Nat := 4983230072969 + 3 ^ 40 * 333424 * 2
def baseEnd_333424 : Nat := 76091899442137204785163

theorem tailTrace_333424 : CollatzResearch.WordTrace tailWord_333424 prefixEnd_333424 76091899442137204785163 := by
  unfold tailWord_333424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080486172034633565371663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8107314896046178087162217 6080486172034633565371663)
  ·
    refine ⟨9120729258051950348057495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6080486172034633565371663 9120729258051950348057495)
    ·
      refine ⟨13681093887077925522086243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9120729258051950348057495 13681093887077925522086243)
      ·
        refine ⟨20521640830616888283129365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13681093887077925522086243 20521640830616888283129365)
        ·
          refine ⟨961951913935166638271689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20521640830616888283129365 961951913935166638271689)
          ·
            refine ⟨721463935451374978703767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 961951913935166638271689 721463935451374978703767)
            ·
              refine ⟨1082195903177062468055651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721463935451374978703767 1082195903177062468055651)
              ·
                refine ⟨1623293854765593702083477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082195903177062468055651 1623293854765593702083477)
                ·
                  refine ⟨76091899442137204785163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1623293854765593702083477 76091899442137204785163)
                  ·
                    rfl

theorem cell21_333424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_333424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333424 prefixEnd_333424 := by exact prefixLift 333424
  have htrace : WordTrace (prefixWord ++ tailWord_333424) baseStart_333424 baseEnd_333424 := by
    simpa [prefixWord, tailWord_333424, baseEnd_333424] using wordTrace_append hprefix tailTrace_333424
  have hstable : (prefixWord ++ tailWord_333424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333424).length < 2 ^ (prefixWord ++ tailWord_333424).sum := by decide
  have hdescent : baseEnd_333424 < baseStart_333424 := by decide
  rcases family_descends (prefixWord ++ tailWord_333424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333537 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 3]
def baseStart_333537 : Nat := 118140960795 + 333537 * 2 ^ 59
def prefixEnd_333537 : Nat := 4983230072969 + 3 ^ 40 * 333537 * 2
def baseEnd_333537 : Nat := 76117687581674119401599

theorem tailTrace_333537 : CollatzResearch.WordTrace tailWord_333537 prefixEnd_333537 76117687581674119401599 := by
  unfold tailWord_333537
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165093792659887429606865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8110062528439924953071243 12165093792659887429606865)
  ·
    refine ⟨9123820344494915572205149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12165093792659887429606865 9123820344494915572205149)
    ·
      refine ⟨3421432629185593339576931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9123820344494915572205149 3421432629185593339576931)
      ·
        refine ⟨5132148943778390009365397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3421432629185593339576931 5132148943778390009365397)
        ·
          refine ⟨240569481739612031689003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5132148943778390009365397 240569481739612031689003)
          ·
            refine ⟨360854222609418047533505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240569481739612031689003 360854222609418047533505)
            ·
              refine ⟨270640666957063535650129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360854222609418047533505 270640666957063535650129)
              ·
                refine ⟨202980500217797651737597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270640666957063535650129 202980500217797651737597)
                ·
                  refine ⟨76117687581674119401599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202980500217797651737597 76117687581674119401599)
                  ·
                    rfl

theorem cell21_333537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_333537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333537 prefixEnd_333537 := by exact prefixLift 333537
  have htrace : WordTrace (prefixWord ++ tailWord_333537) baseStart_333537 baseEnd_333537 := by
    simpa [prefixWord, tailWord_333537, baseEnd_333537] using wordTrace_append hprefix tailTrace_333537
  have hstable : (prefixWord ++ tailWord_333537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333537).length < 2 ^ (prefixWord ++ tailWord_333537).sum := by decide
  have hdescent : baseEnd_333537 < baseStart_333537 := by decide
  rcases family_descends (prefixWord ++ tailWord_333537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333635 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_333635 : Nat := 118140960795 + 333635 * 2 ^ 59
def prefixEnd_333635 : Nat := 4983230072969 + 3 ^ 40 * 333635 * 2
def baseEnd_333635 : Nat := 76140052516847726768065

theorem tailTrace_333635 : CollatzResearch.WordTrace tailWord_333635 prefixEnd_333635 76140052516847726768065 := by
  unfold tailWord_333635
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168668146304850166674359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8112445430869900111116239 12168668146304850166674359)
  ·
    refine ⟨18253002219457275250011539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12168668146304850166674359 18253002219457275250011539)
    ·
      refine ⟨27379503329185912875017309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18253002219457275250011539 27379503329185912875017309)
      ·
        refine ⟨10267313748444717328131491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27379503329185912875017309 10267313748444717328131491)
        ·
          refine ⟨15400970622667075992197237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10267313748444717328131491 15400970622667075992197237)
          ·
            refine ⟨1443840995875038374268491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15400970622667075992197237 1443840995875038374268491)
            ·
              refine ⟨2165761493812557561402737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443840995875038374268491 2165761493812557561402737)
              ·
                refine ⟨1624321120359418171052053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165761493812557561402737 1624321120359418171052053)
                ·
                  refine ⟨76140052516847726768065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1624321120359418171052053 76140052516847726768065)
                  ·
                    rfl

theorem cell21_333635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_333635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333635 prefixEnd_333635 := by exact prefixLift 333635
  have htrace : WordTrace (prefixWord ++ tailWord_333635) baseStart_333635 baseEnd_333635 := by
    simpa [prefixWord, tailWord_333635, baseEnd_333635] using wordTrace_append hprefix tailTrace_333635
  have hstable : (prefixWord ++ tailWord_333635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333635).length < 2 ^ (prefixWord ++ tailWord_333635).sum := by decide
  have hdescent : baseEnd_333635 < baseStart_333635 := by decide
  rcases family_descends (prefixWord ++ tailWord_333635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333652 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_333652 : Nat := 118140960795 + 333652 * 2 ^ 59
def prefixEnd_333652 : Nat := 4983230072969 + 3 ^ 40 * 333652 * 2
def baseEnd_333652 : Nat := 76143932148459474984697

theorem tailTrace_333652 : CollatzResearch.WordTrace tailWord_333652 prefixEnd_333652 76143932148459474984697 := by
  unfold tailWord_333652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084644093621631035021605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8112858791495508046695473 6084644093621631035021605)
  ·
    refine ⟨1140870767554055819066551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6084644093621631035021605 1140870767554055819066551)
    ·
      refine ⟨1711306151331083728599827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140870767554055819066551 1711306151331083728599827)
      ·
        refine ⟨2566959226996625592899741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711306151331083728599827 2566959226996625592899741)
        ·
          refine ⟨962609710123734597337403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2566959226996625592899741 962609710123734597337403)
          ·
            refine ⟨1443914565185601896006105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962609710123734597337403 1443914565185601896006105)
            ·
              refine ⟨1082935923889201422004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1443914565185601896006105 1082935923889201422004579)
              ·
                refine ⟨1624403885833802133006869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082935923889201422004579 1624403885833802133006869)
                ·
                  refine ⟨76143932148459474984697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1624403885833802133006869 76143932148459474984697)
                  ·
                    rfl

theorem cell21_333652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_333652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333652 prefixEnd_333652 := by exact prefixLift 333652
  have htrace : WordTrace (prefixWord ++ tailWord_333652) baseStart_333652 baseEnd_333652 := by
    simpa [prefixWord, tailWord_333652, baseEnd_333652] using wordTrace_append hprefix tailTrace_333652
  have hstable : (prefixWord ++ tailWord_333652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333652).length < 2 ^ (prefixWord ++ tailWord_333652).sum := by decide
  have hdescent : baseEnd_333652 < baseStart_333652 := by decide
  rcases family_descends (prefixWord ++ tailWord_333652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333655 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 5]
def baseStart_333655 : Nat := 118140960795 + 333655 * 2 ^ 59
def prefixEnd_333655 : Nat := 4983230072969 + 3 ^ 40 * 333655 * 2
def baseEnd_333655 : Nat := 76144616789332136434691

theorem tailTrace_333655 : CollatzResearch.WordTrace tailWord_333655 prefixEnd_333655 76144616789332136434691 := by
  unfold tailWord_333655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169397606232393582402419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8112931737488262388268279 12169397606232393582402419)
  ·
    refine ⟨18254096409348590373603629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12169397606232393582402419 18254096409348590373603629)
    ·
      refine ⟨6845286153505721390101361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18254096409348590373603629 6845286153505721390101361)
      ·
        refine ⟨5133964615129291042576021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6845286153505721390101361 5133964615129291042576021)
        ·
          refine ⟨240654591334185517620751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5133964615129291042576021 240654591334185517620751)
          ·
            refine ⟨360981887001278276431127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240654591334185517620751 360981887001278276431127)
            ·
              refine ⟨541472830501917414646691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360981887001278276431127 541472830501917414646691)
              ·
                refine ⟨812209245752876121970037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541472830501917414646691 812209245752876121970037)
                ·
                  refine ⟨76144616789332136434691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 812209245752876121970037 76144616789332136434691)
                  ·
                    rfl

theorem cell21_333655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5].length) (baseStart_333655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333655 prefixEnd_333655 := by exact prefixLift 333655
  have htrace : WordTrace (prefixWord ++ tailWord_333655) baseStart_333655 baseEnd_333655 := by
    simpa [prefixWord, tailWord_333655, baseEnd_333655] using wordTrace_append hprefix tailTrace_333655
  have hstable : (prefixWord ++ tailWord_333655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333655).length < 2 ^ (prefixWord ++ tailWord_333655).sum := by decide
  have hdescent : baseEnd_333655 < baseStart_333655 := by decide
  rcases family_descends (prefixWord ++ tailWord_333655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333680 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_333680 : Nat := 118140960795 + 333680 * 2 ^ 59
def prefixEnd_333680 : Nat := 4983230072969 + 3 ^ 40 * 333680 * 2
def baseEnd_333680 : Nat := 76150322129937648517973

theorem tailTrace_333680 : CollatzResearch.WordTrace tailWord_333680 prefixEnd_333680 76150322129937648517973 := by
  unfold tailWord_333680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085154715570911426031247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8113539620761215234708329 6085154715570911426031247)
  ·
    refine ⟨9127732073356367139046871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6085154715570911426031247 9127732073356367139046871)
    ·
      refine ⟨13691598110034550708570307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127732073356367139046871 13691598110034550708570307)
      ·
        refine ⟨20537397165051826062855461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13691598110034550708570307 20537397165051826062855461)
        ·
          refine ⟨3850761968447217386785399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20537397165051826062855461 3850761968447217386785399)
          ·
            refine ⟨5776142952670826080178099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850761968447217386785399 5776142952670826080178099)
            ·
              refine ⟨8664214429006239120267149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5776142952670826080178099 8664214429006239120267149)
              ·
                refine ⟨3249080410877339670100181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8664214429006239120267149 3249080410877339670100181)
                ·
                  refine ⟨76150322129937648517973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3249080410877339670100181 76150322129937648517973)
                  ·
                    rfl

theorem cell21_333680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_333680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333680 prefixEnd_333680 := by exact prefixLift 333680
  have htrace : WordTrace (prefixWord ++ tailWord_333680) baseStart_333680 baseEnd_333680 := by
    simpa [prefixWord, tailWord_333680, baseEnd_333680] using wordTrace_append hprefix tailTrace_333680
  have hstable : (prefixWord ++ tailWord_333680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333680).length < 2 ^ (prefixWord ++ tailWord_333680).sum := by decide
  have hdescent : baseEnd_333680 < baseStart_333680 := by decide
  rcases family_descends (prefixWord ++ tailWord_333680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333830 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_333830 : Nat := 118140960795 + 333830 * 2 ^ 59
def prefixEnd_333830 : Nat := 4983230072969 + 3 ^ 40 * 333830 * 2
def baseEnd_333830 : Nat := 76184554173570721017667

theorem tailTrace_333830 : CollatzResearch.WordTrace tailWord_333830 prefixEnd_333830 76184554173570721017667 := by
  unfold tailWord_333830
  simp only [CollatzResearch.WordTrace]
  refine ⟨380493136893699952188217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8117186920398932313348629 380493136893699952188217)
  ·
    refine ⟨285369852670274964141163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 380493136893699952188217 285369852670274964141163)
    ·
      refine ⟨428054779005412446211745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285369852670274964141163 428054779005412446211745)
      ·
        refine ⟨321041084254059334658809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428054779005412446211745 321041084254059334658809)
        ·
          refine ⟨240780813190544500994107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321041084254059334658809 240780813190544500994107)
          ·
            refine ⟨361171219785816751491161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240780813190544500994107 361171219785816751491161)
            ·
              refine ⟨270878414839362563618371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361171219785816751491161 270878414839362563618371)
              ·
                refine ⟨406317622259043845427557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270878414839362563618371 406317622259043845427557)
                ·
                  refine ⟨76184554173570721017667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406317622259043845427557 76184554173570721017667)
                  ·
                    rfl

theorem cell21_333830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_333830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333830 prefixEnd_333830 := by exact prefixLift 333830
  have htrace : WordTrace (prefixWord ++ tailWord_333830) baseStart_333830 baseEnd_333830 := by
    simpa [prefixWord, tailWord_333830, baseEnd_333830] using wordTrace_append hprefix tailTrace_333830
  have hstable : (prefixWord ++ tailWord_333830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333830).length < 2 ^ (prefixWord ++ tailWord_333830).sum := by decide
  have hdescent : baseEnd_333830 < baseStart_333830 := by decide
  rcases family_descends (prefixWord ++ tailWord_333830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333942 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_333942 : Nat := 118140960795 + 333942 * 2 ^ 59
def prefixEnd_333942 : Nat := 4983230072969 + 3 ^ 40 * 333942 * 2
def baseEnd_333942 : Nat := 76210114099483415150771

theorem tailTrace_333942 : CollatzResearch.WordTrace tailWord_333942 prefixEnd_333942 76210114099483415150771 := by
  unfold tailWord_333942
  simp only [CollatzResearch.WordTrace]
  refine ⟨761241584762040099881255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8119910237461761065400053 761241584762040099881255)
  ·
    refine ⟨1141862377143060149821883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761241584762040099881255 1141862377143060149821883)
    ·
      refine ⟨1712793565714590224732825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141862377143060149821883 1712793565714590224732825)
      ·
        refine ⟨1284595174285942668549619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712793565714590224732825 1284595174285942668549619)
        ·
          refine ⟨1926892761428914002824429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284595174285942668549619 1926892761428914002824429)
          ·
            refine ⟨722584785535842751059161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1926892761428914002824429 722584785535842751059161)
            ·
              refine ⟨541938589151882063294371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722584785535842751059161 541938589151882063294371)
              ·
                refine ⟨812907883727823094941557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541938589151882063294371 812907883727823094941557)
                ·
                  refine ⟨76210114099483415150771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 812907883727823094941557 76210114099483415150771)
                  ·
                    rfl

theorem cell21_333942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_333942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333942 prefixEnd_333942 := by exact prefixLift 333942
  have htrace : WordTrace (prefixWord ++ tailWord_333942) baseStart_333942 baseEnd_333942 := by
    simpa [prefixWord, tailWord_333942, baseEnd_333942] using wordTrace_append hprefix tailTrace_333942
  have hstable : (prefixWord ++ tailWord_333942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333942).length < 2 ^ (prefixWord ++ tailWord_333942).sum := by decide
  have hdescent : baseEnd_333942 < baseStart_333942 := by decide
  rcases family_descends (prefixWord ++ tailWord_333942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333970 : List Nat := [3, 2, 3, 1, 1, 1, 3, 7]
def baseStart_333970 : Nat := 118140960795 + 333970 * 2 ^ 59
def prefixEnd_333970 : Nat := 4983230072969 + 3 ^ 40 * 333970 * 2
def baseEnd_333970 : Nat := 25405501360320529561349

theorem tailTrace_333970 : CollatzResearch.WordTrace tailWord_333970 prefixEnd_333970 25405501360320529561349 := by
  unfold tailWord_333970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045221650022800595029841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8120591066727468253412909 3045221650022800595029841)
  ·
    refine ⟨2283916237517100446272381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3045221650022800595029841 2283916237517100446272381)
    ·
      refine ⟨856468589068912667352143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2283916237517100446272381 856468589068912667352143)
      ·
        refine ⟨1284702883603369001028215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856468589068912667352143 1284702883603369001028215)
        ·
          refine ⟨1927054325405053501542323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284702883603369001028215 1927054325405053501542323)
          ·
            refine ⟨2890581488107580252313485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927054325405053501542323 2890581488107580252313485)
            ·
              refine ⟨1083968058040342594617557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2890581488107580252313485 1083968058040342594617557)
              ·
                refine ⟨25405501360320529561349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1083968058040342594617557 25405501360320529561349)
                ·
                  rfl

theorem cell21_333970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_333970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333970 prefixEnd_333970 := by exact prefixLift 333970
  have htrace : WordTrace (prefixWord ++ tailWord_333970) baseStart_333970 baseEnd_333970 := by
    simpa [prefixWord, tailWord_333970, baseEnd_333970] using wordTrace_append hprefix tailTrace_333970
  have hstable : (prefixWord ++ tailWord_333970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333970).length < 2 ^ (prefixWord ++ tailWord_333970).sum := by decide
  have hdescent : baseEnd_333970 < baseStart_333970 := by decide
  rcases family_descends (prefixWord ++ tailWord_333970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333976 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_333976 : Nat := 118140960795 + 333976 * 2 ^ 59
def prefixEnd_333976 : Nat := 4983230072969 + 3 ^ 40 * 333976 * 2
def baseEnd_333976 : Nat := 76217873362706911584035

theorem tailTrace_333976 : CollatzResearch.WordTrace tailWord_333976 prefixEnd_333976 76217873362706911584035 := by
  unfold tailWord_333976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090552719034732702418891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8120736958712976936558521 6090552719034732702418891)
  ·
    refine ⟨9135829078552099053628337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6090552719034732702418891 9135829078552099053628337)
    ·
      refine ⟨6851871808914074290221253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9135829078552099053628337 6851871808914074290221253)
      ·
        refine ⟨1284725964171388929416485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6851871808914074290221253 1284725964171388929416485)
        ·
          refine ⟨240886118282135424265591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1284725964171388929416485 240886118282135424265591)
          ·
            refine ⟨361329177423203136398387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240886118282135424265591 361329177423203136398387)
            ·
              refine ⟨541993766134804704597581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361329177423203136398387 541993766134804704597581)
              ·
                refine ⟨203247662300551764224093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 541993766134804704597581 203247662300551764224093)
                ·
                  refine ⟨76217873362706911584035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203247662300551764224093 76217873362706911584035)
                  ·
                    rfl

theorem cell21_333976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_333976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_333976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_333976 prefixEnd_333976 := by exact prefixLift 333976
  have htrace : WordTrace (prefixWord ++ tailWord_333976) baseStart_333976 baseEnd_333976 := by
    simpa [prefixWord, tailWord_333976, baseEnd_333976] using wordTrace_append hprefix tailTrace_333976
  have hstable : (prefixWord ++ tailWord_333976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333976).length < 2 ^ (prefixWord ++ tailWord_333976).sum := by decide
  have hdescent : baseEnd_333976 < baseStart_333976 := by decide
  rcases family_descends (prefixWord ++ tailWord_333976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334060 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_334060 : Nat := 118140960795 + 334060 * 2 ^ 59
def prefixEnd_334060 : Nat := 4983230072969 + 3 ^ 40 * 334060 * 2
def baseEnd_334060 : Nat := 76237043307141432183863

theorem tailTrace_334060 : CollatzResearch.WordTrace tailWord_334060 prefixEnd_334060 76237043307141432183863 := by
  unfold tailWord_334060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092084584882573875447817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8122779446510098500597089 6092084584882573875447817)
  ·
    refine ⟨4569063438661930406585863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6092084584882573875447817 4569063438661930406585863)
    ·
      refine ⟨6853595157992895609878795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4569063438661930406585863 6853595157992895609878795)
      ·
        refine ⟨10280392736989343414818193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6853595157992895609878795 10280392736989343414818193)
        ·
          refine ⟨7710294552742007561113645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10280392736989343414818193 7710294552742007561113645)
          ·
            refine ⟨2891360457278252835417617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7710294552742007561113645 2891360457278252835417617)
            ·
              refine ⟨2168520342958689626563213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891360457278252835417617 2168520342958689626563213)
              ·
                refine ⟨813195128609508609961205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2168520342958689626563213 813195128609508609961205)
                ·
                  refine ⟨76237043307141432183863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 813195128609508609961205 76237043307141432183863)
                  ·
                    rfl

theorem cell21_334060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_334060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334060 prefixEnd_334060 := by exact prefixLift 334060
  have htrace : WordTrace (prefixWord ++ tailWord_334060) baseStart_334060 baseEnd_334060 := by
    simpa [prefixWord, tailWord_334060, baseEnd_334060] using wordTrace_append hprefix tailTrace_334060
  have hstable : (prefixWord ++ tailWord_334060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334060).length < 2 ^ (prefixWord ++ tailWord_334060).sum := by decide
  have hdescent : baseEnd_334060 < baseStart_334060 := by decide
  rcases family_descends (prefixWord ++ tailWord_334060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334094 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_334094 : Nat := 118140960795 + 334094 * 2 ^ 59
def prefixEnd_334094 : Nat := 4983230072969 + 3 ^ 40 * 334094 * 2
def baseEnd_334094 : Nat := 76244802570364928617127

theorem tailTrace_334094 : CollatzResearch.WordTrace tailWord_334094 prefixEnd_334094 76244802570364928617127 := by
  unfold tailWord_334094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523176156455246444704167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8123606167761314371755557 1523176156455246444704167)
  ·
    refine ⟨2284764234682869667056251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1523176156455246444704167 2284764234682869667056251)
    ·
      refine ⟨3427146352024304500584377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284764234682869667056251 3427146352024304500584377)
      ·
        refine ⟨2570359764018228375438283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3427146352024304500584377 2570359764018228375438283)
        ·
          refine ⟨3855539646027342563157425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570359764018228375438283 3855539646027342563157425)
          ·
            refine ⟨2891654734520506922368069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855539646027342563157425 2891654734520506922368069)
            ·
              refine ⟨542185262722595047944013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2891654734520506922368069 542185262722595047944013)
              ·
                refine ⟨203319473520973142979005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542185262722595047944013 203319473520973142979005)
                ·
                  refine ⟨76244802570364928617127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203319473520973142979005 76244802570364928617127)
                  ·
                    rfl

theorem cell21_334094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_334094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334094 prefixEnd_334094 := by exact prefixLift 334094
  have htrace : WordTrace (prefixWord ++ tailWord_334094) baseStart_334094 baseEnd_334094 := by
    simpa [prefixWord, tailWord_334094, baseEnd_334094] using wordTrace_append hprefix tailTrace_334094
  have hstable : (prefixWord ++ tailWord_334094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334094).length < 2 ^ (prefixWord ++ tailWord_334094).sum := by decide
  have hdescent : baseEnd_334094 < baseStart_334094 := by decide
  rcases family_descends (prefixWord ++ tailWord_334094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334136 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_334136 : Nat := 118140960795 + 334136 * 2 ^ 59
def prefixEnd_334136 : Nat := 4983230072969 + 3 ^ 40 * 334136 * 2
def baseEnd_334136 : Nat := 76254387542582188917041

theorem tailTrace_334136 : CollatzResearch.WordTrace tailWord_334136 prefixEnd_334136 76254387542582188917041 := by
  unfold tailWord_334136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093470558744906365331131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8124627411659875153774841 6093470558744906365331131)
  ·
    refine ⟨9140205838117359547996697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6093470558744906365331131 9140205838117359547996697)
    ·
      refine ⟨6855154378588019660997523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9140205838117359547996697 6855154378588019660997523)
      ·
        refine ⟨10282731567882029491496285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6855154378588019660997523 10282731567882029491496285)
        ·
          refine ⟨3856024337955761059311107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10282731567882029491496285 3856024337955761059311107)
          ·
            refine ⟨5784036506933641588966661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856024337955761059311107 5784036506933641588966661)
            ·
              refine ⟨1084506845050057797931249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5784036506933641588966661 1084506845050057797931249)
              ·
                refine ⟨813380133787543348448437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084506845050057797931249 813380133787543348448437)
                ·
                  refine ⟨76254387542582188917041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 813380133787543348448437 76254387542582188917041)
                  ·
                    rfl

theorem cell21_334136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_334136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334136 prefixEnd_334136 := by exact prefixLift 334136
  have htrace : WordTrace (prefixWord ++ tailWord_334136) baseStart_334136 baseEnd_334136 := by
    simpa [prefixWord, tailWord_334136, baseEnd_334136] using wordTrace_append hprefix tailTrace_334136
  have hstable : (prefixWord ++ tailWord_334136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334136).length < 2 ^ (prefixWord ++ tailWord_334136).sum := by decide
  have hdescent : baseEnd_334136 < baseStart_334136 := by decide
  rcases family_descends (prefixWord ++ tailWord_334136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334167 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_334167 : Nat := 118140960795 + 334167 * 2 ^ 59
def prefixEnd_334167 : Nat := 4983230072969 + 3 ^ 40 * 334167 * 2
def baseEnd_334167 : Nat := 76261462164933023900311

theorem tailTrace_334167 : CollatzResearch.WordTrace tailWord_334167 prefixEnd_334167 76261462164933023900311 := by
  unfold tailWord_334167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188071780377505025040755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8125381186918336683360503 12188071780377505025040755)
  ·
    refine ⟨18282107670566257537561133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12188071780377505025040755 18282107670566257537561133)
    ·
      refine ⟨6855790376462346576585425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18282107670566257537561133 6855790376462346576585425)
      ·
        refine ⟨5141842782346759932439069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6855790376462346576585425 5141842782346759932439069)
        ·
          refine ⟨1928191043380034974664651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5141842782346759932439069 1928191043380034974664651)
          ·
            refine ⟨2892286565070052461996977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928191043380034974664651 2892286565070052461996977)
            ·
              refine ⟨2169214923802539346497733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892286565070052461996977 2169214923802539346497733)
              ·
                refine ⟨406727798212976127468325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2169214923802539346497733 406727798212976127468325)
                ·
                  refine ⟨76261462164933023900311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406727798212976127468325 76261462164933023900311)
                  ·
                    rfl

theorem cell21_334167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_334167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334167 prefixEnd_334167 := by exact prefixLift 334167
  have htrace : WordTrace (prefixWord ++ tailWord_334167) baseStart_334167 baseEnd_334167 := by
    simpa [prefixWord, tailWord_334167, baseEnd_334167] using wordTrace_append hprefix tailTrace_334167
  have hstable : (prefixWord ++ tailWord_334167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334167).length < 2 ^ (prefixWord ++ tailWord_334167).sum := by decide
  have hdescent : baseEnd_334167 < baseStart_334167 := by decide
  rcases family_descends (prefixWord ++ tailWord_334167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334181 : List Nat := [1, 3, 1, 3, 1, 3, 1, 8]
def baseStart_334181 : Nat := 118140960795 + 334181 * 2 ^ 59
def prefixEnd_334181 : Nat := 4983230072969 + 3 ^ 40 * 334181 * 2
def baseEnd_334181 : Nat := 25421552385224036888983

theorem tailTrace_334181 : CollatzResearch.WordTrace tailWord_334181 prefixEnd_334181 25421552385224036888983 := by
  unfold tailWord_334181
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188582402326785416050397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8125721601551190277366931 12188582402326785416050397)
  ·
    refine ⟨4570718400872544531018899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12188582402326785416050397 4570718400872544531018899)
    ·
      refine ⟨6856077601308816796528349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4570718400872544531018899 6856077601308816796528349)
      ·
        refine ⟨2571029100490806298698131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6856077601308816796528349 2571029100490806298698131)
        ·
          refine ⟨3856543650736209448047197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571029100490806298698131 3856543650736209448047197)
          ·
            refine ⟨1446203869026078543017699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3856543650736209448047197 1446203869026078543017699)
            ·
              refine ⟨2169305803539117814526549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446203869026078543017699 2169305803539117814526549)
              ·
                refine ⟨25421552385224036888983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2169305803539117814526549 25421552385224036888983)
                ·
                  rfl

theorem cell21_334181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_334181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334181 prefixEnd_334181 := by exact prefixLift 334181
  have htrace : WordTrace (prefixWord ++ tailWord_334181) baseStart_334181 baseEnd_334181 := by
    simpa [prefixWord, tailWord_334181, baseEnd_334181] using wordTrace_append hprefix tailTrace_334181
  have hstable : (prefixWord ++ tailWord_334181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334181).length < 2 ^ (prefixWord ++ tailWord_334181).sum := by decide
  have hdescent : baseEnd_334181 < baseStart_334181 := by decide
  rcases family_descends (prefixWord ++ tailWord_334181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334184 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_334184 : Nat := 118140960795 + 334184 * 2 ^ 59
def prefixEnd_334184 : Nat := 4983230072969 + 3 ^ 40 * 334184 * 2
def baseEnd_334184 : Nat := 76265341796544772116943

theorem tailTrace_334184 : CollatzResearch.WordTrace tailWord_334184 prefixEnd_334184 76265341796544772116943 := by
  unfold tailWord_334184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094345910657958464204803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8125794547543944618939737 6094345910657958464204803)
  ·
    refine ⟨9141518865986937696307205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6094345910657958464204803 9141518865986937696307205)
    ·
      refine ⟨1714034787372550818057601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9141518865986937696307205 1714034787372550818057601)
      ·
        refine ⟨1285526090529413113543201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1714034787372550818057601 1285526090529413113543201)
        ·
          refine ⟨964144567897059835157401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285526090529413113543201 964144567897059835157401)
          ·
            refine ⟨723108425922794876368051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964144567897059835157401 723108425922794876368051)
            ·
              refine ⟨1084662638884192314552077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723108425922794876368051 1084662638884192314552077)
              ·
                refine ⟨406748489581572117957029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1084662638884192314552077 406748489581572117957029)
                ·
                  refine ⟨76265341796544772116943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406748489581572117957029 76265341796544772116943)
                  ·
                    rfl

theorem cell21_334184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_334184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334184 prefixEnd_334184 := by exact prefixLift 334184
  have htrace : WordTrace (prefixWord ++ tailWord_334184) baseStart_334184 baseEnd_334184 := by
    simpa [prefixWord, tailWord_334184, baseEnd_334184] using wordTrace_append hprefix tailTrace_334184
  have hstable : (prefixWord ++ tailWord_334184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334184).length < 2 ^ (prefixWord ++ tailWord_334184).sum := by decide
  have hdescent : baseEnd_334184 < baseStart_334184 := by decide
  rcases family_descends (prefixWord ++ tailWord_334184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334243 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_334243 : Nat := 118140960795 + 334243 * 2 ^ 59
def prefixEnd_334243 : Nat := 4983230072969 + 3 ^ 40 * 334243 * 2
def baseEnd_334243 : Nat := 76278806400373780633489

theorem tailTrace_334243 : CollatzResearch.WordTrace tailWord_334243 prefixEnd_334243 76278806400373780633489 := by
  unfold tailWord_334243
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190843728102170004807383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8127229152068113336538255 12190843728102170004807383)
  ·
    refine ⟨18286265592153255007211075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12190843728102170004807383 18286265592153255007211075)
    ·
      refine ⟨27429398388229882510816613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18286265592153255007211075 27429398388229882510816613)
      ·
        refine ⟨5143012197793102970778115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27429398388229882510816613 5143012197793102970778115)
        ·
          refine ⟨7714518296689654456167173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143012197793102970778115 7714518296689654456167173)
          ·
            refine ⟨1446472180629310210531345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7714518296689654456167173 1446472180629310210531345)
            ·
              refine ⟨1084854135471982657898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446472180629310210531345 1084854135471982657898509)
              ·
                refine ⟨406820300801993496711941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1084854135471982657898509 406820300801993496711941)
                ·
                  refine ⟨76278806400373780633489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406820300801993496711941 76278806400373780633489)
                  ·
                    rfl

theorem cell21_334243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_334243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334243 prefixEnd_334243 := by exact prefixLift 334243
  have htrace : WordTrace (prefixWord ++ tailWord_334243) baseStart_334243 baseEnd_334243 := by
    simpa [prefixWord, tailWord_334243, baseEnd_334243] using wordTrace_append hprefix tailTrace_334243
  have hstable : (prefixWord ++ tailWord_334243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334243).length < 2 ^ (prefixWord ++ tailWord_334243).sum := by decide
  have hdescent : baseEnd_334243 < baseStart_334243 := by decide
  rcases family_descends (prefixWord ++ tailWord_334243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334350 : List Nat := [4, 1, 1, 2, 3, 2, 2, 6]
def baseStart_334350 : Nat := 118140960795 + 334350 * 2 ^ 59
def prefixEnd_334350 : Nat := 4983230072969 + 3 ^ 40 * 334350 * 2
def baseEnd_334350 : Nat := 25434408419388457449979

theorem tailTrace_334350 : CollatzResearch.WordTrace tailWord_334350 prefixEnd_334350 25434408419388457449979 := by
  unfold tailWord_334350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524343292339315909869063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8129830892476351519301669 1524343292339315909869063)
  ·
    refine ⟨2286514938508973864803595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524343292339315909869063 2286514938508973864803595)
    ·
      refine ⟨3429772407763460797205393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286514938508973864803595 3429772407763460797205393)
      ·
        refine ⟨2572329305822595597904045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3429772407763460797205393 2572329305822595597904045)
        ·
          refine ⟨964623489683473349214017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2572329305822595597904045 964623489683473349214017)
          ·
            refine ⟨723467617262605011910513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964623489683473349214017 723467617262605011910513)
            ·
              refine ⟨542600712946953758932885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723467617262605011910513 542600712946953758932885)
              ·
                refine ⟨25434408419388457449979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 542600712946953758932885 25434408419388457449979)
                ·
                  rfl

theorem cell21_334350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_334350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334350 prefixEnd_334350 := by exact prefixLift 334350
  have htrace : WordTrace (prefixWord ++ tailWord_334350) baseStart_334350 baseEnd_334350 := by
    simpa [prefixWord, tailWord_334350, baseEnd_334350] using wordTrace_append hprefix tailTrace_334350
  have hstable : (prefixWord ++ tailWord_334350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334350).length < 2 ^ (prefixWord ++ tailWord_334350).sum := by decide
  have hdescent : baseEnd_334350 < baseStart_334350 := by decide
  rcases family_descends (prefixWord ++ tailWord_334350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334457 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 3]
def baseStart_334457 : Nat := 118140960795 + 334457 * 2 ^ 59
def prefixEnd_334457 : Nat := 4983230072969 + 3 ^ 40 * 334457 * 2
def baseEnd_334457 : Nat := 76327644115956964066385

theorem tailTrace_334457 : CollatzResearch.WordTrace tailWord_334457 prefixEnd_334457 76327644115956964066385 := by
  unfold tailWord_334457
  simp only [CollatzResearch.WordTrace]
  refine ⟨12198648949326884553097625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8132432632884589702065083 12198648949326884553097625)
  ·
    refine ⟨9148986711995163414823219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12198648949326884553097625 9148986711995163414823219)
    ·
      refine ⟨13723480067992745122234829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9148986711995163414823219 13723480067992745122234829)
      ·
        refine ⟨5146305025497279420838061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13723480067992745122234829 5146305025497279420838061)
        ·
          refine ⟨1929864384561479782814273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5146305025497279420838061 1929864384561479782814273)
          ·
            refine ⟨1447398288421109837110705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1929864384561479782814273 1447398288421109837110705)
            ·
              refine ⟨1085548716315832377833029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447398288421109837110705 1085548716315832377833029)
              ·
                refine ⟨203540384309218570843693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1085548716315832377833029 203540384309218570843693)
                ·
                  refine ⟨76327644115956964066385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203540384309218570843693 76327644115956964066385)
                  ·
                    rfl

theorem cell21_334457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_334457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334457 prefixEnd_334457 := by exact prefixLift 334457
  have htrace : WordTrace (prefixWord ++ tailWord_334457) baseStart_334457 baseEnd_334457 := by
    simpa [prefixWord, tailWord_334457, baseEnd_334457] using wordTrace_append hprefix tailTrace_334457
  have hstable : (prefixWord ++ tailWord_334457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334457).length < 2 ^ (prefixWord ++ tailWord_334457).sum := by decide
  have hdescent : baseEnd_334457 < baseStart_334457 := by decide
  rcases family_descends (prefixWord ++ tailWord_334457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334578 : List Nat := [3, 2, 1, 3, 1, 4, 1, 6]
def baseStart_334578 : Nat := 118140960795 + 334578 * 2 ^ 59
def prefixEnd_334578 : Nat := 4983230072969 + 3 ^ 40 * 334578 * 2
def baseEnd_334578 : Nat := 25451752654829214183157

theorem tailTrace_334578 : CollatzResearch.WordTrace tailWord_334578 prefixEnd_334578 25451752654829214183157 := by
  unfold tailWord_334578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050765545472130554563097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8135374787925681478834925 3050765545472130554563097)
  ·
    refine ⟨2288074159104097915922323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3050765545472130554563097 2288074159104097915922323)
    ·
      refine ⟨3432111238656146873883485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288074159104097915922323 3432111238656146873883485)
      ·
        refine ⟨1287041714496055077706307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3432111238656146873883485 1287041714496055077706307)
        ·
          refine ⟨1930562571744082616559461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287041714496055077706307 1930562571744082616559461)
          ·
            refine ⟨361980482202015490604899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1930562571744082616559461 361980482202015490604899)
            ·
              refine ⟨542970723303023235907349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361980482202015490604899 542970723303023235907349)
              ·
                refine ⟨25451752654829214183157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 542970723303023235907349 25451752654829214183157)
                ·
                  rfl

theorem cell21_334578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_334578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334578 prefixEnd_334578 := by exact prefixLift 334578
  have htrace : WordTrace (prefixWord ++ tailWord_334578) baseStart_334578 baseEnd_334578 := by
    simpa [prefixWord, tailWord_334578, baseEnd_334578] using wordTrace_append hprefix tailTrace_334578
  have hstable : (prefixWord ++ tailWord_334578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334578).length < 2 ^ (prefixWord ++ tailWord_334578).sum := by decide
  have hdescent : baseEnd_334578 < baseStart_334578 := by decide
  rcases family_descends (prefixWord ++ tailWord_334578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334606 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_334606 : Nat := 118140960795 + 334606 * 2 ^ 59
def prefixEnd_334606 : Nat := 4983230072969 + 3 ^ 40 * 334606 * 2
def baseEnd_334606 : Nat := 76361647945965816082747

theorem tailTrace_334606 : CollatzResearch.WordTrace tailWord_334606 prefixEnd_334606 76361647945965816082747 := by
  unfold tailWord_334606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525510428223385375033959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8136055617191388666847781 1525510428223385375033959)
  ·
    refine ⟨2288265642335078062550939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525510428223385375033959 2288265642335078062550939)
    ·
      refine ⟨3432398463502617093826409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288265642335078062550939 3432398463502617093826409)
      ·
        refine ⟨2574298847626962820369807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432398463502617093826409 2574298847626962820369807)
        ·
          refine ⟨3861448271440444230554711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574298847626962820369807 3861448271440444230554711)
          ·
            refine ⟨5792172407160666345832067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3861448271440444230554711 5792172407160666345832067)
            ·
              refine ⟨8688258610740999518748101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792172407160666345832067 8688258610740999518748101)
              ·
                refine ⟨1629048489513937409765269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8688258610740999518748101 1629048489513937409765269)
                ·
                  refine ⟨76361647945965816082747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1629048489513937409765269 76361647945965816082747)
                  ·
                    rfl

theorem cell21_334606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_334606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334606 prefixEnd_334606 := by exact prefixLift 334606
  have htrace : WordTrace (prefixWord ++ tailWord_334606) baseStart_334606 baseEnd_334606 := by
    simpa [prefixWord, tailWord_334606, baseEnd_334606] using wordTrace_append hprefix tailTrace_334606
  have hstable : (prefixWord ++ tailWord_334606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334606).length < 2 ^ (prefixWord ++ tailWord_334606).sum := by decide
  have hdescent : baseEnd_334606 < baseStart_334606 := by decide
  rcases family_descends (prefixWord ++ tailWord_334606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334623 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_334623 : Nat := 118140960795 + 334623 * 2 ^ 59
def prefixEnd_334623 : Nat := 4983230072969 + 3 ^ 40 * 334623 * 2
def baseEnd_334623 : Nat := 76365527577577564299379

theorem tailTrace_334623 : CollatzResearch.WordTrace tailWord_334623 prefixEnd_334623 76365527577577564299379 := by
  unfold tailWord_334623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204703466725494903640523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8136468977816996602427015 12204703466725494903640523)
  ·
    refine ⟨18307055200088242355460785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12204703466725494903640523 18307055200088242355460785)
    ·
      refine ⟨13730291400066181766595589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18307055200088242355460785 13730291400066181766595589)
      ·
        refine ⟨2574429637512409081236673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13730291400066181766595589 2574429637512409081236673)
        ·
          refine ⟨1930822228134306810927505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574429637512409081236673 1930822228134306810927505)
          ·
            refine ⟨1448116671100730108195629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930822228134306810927505 1448116671100730108195629)
            ·
              refine ⟨543043751662773790573361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1448116671100730108195629 543043751662773790573361)
              ·
                refine ⟨407282813747080342930021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543043751662773790573361 407282813747080342930021)
                ·
                  refine ⟨76365527577577564299379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407282813747080342930021 76365527577577564299379)
                  ·
                    rfl

theorem cell21_334623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_334623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334623 prefixEnd_334623 := by exact prefixLift 334623
  have htrace : WordTrace (prefixWord ++ tailWord_334623) baseStart_334623 baseEnd_334623 := by
    simpa [prefixWord, tailWord_334623, baseEnd_334623] using wordTrace_append hprefix tailTrace_334623
  have hstable : (prefixWord ++ tailWord_334623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334623).length < 2 ^ (prefixWord ++ tailWord_334623).sum := by decide
  have hdescent : baseEnd_334623 < baseStart_334623 := by decide
  rcases family_descends (prefixWord ++ tailWord_334623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334654 : List Nat := [4, 2, 1, 2, 3, 1, 1, 7]
def baseStart_334654 : Nat := 118140960795 + 334654 * 2 ^ 59
def prefixEnd_334654 : Nat := 4983230072969 + 3 ^ 40 * 334654 * 2
def baseEnd_334654 : Nat := 25457534066642799760883

theorem tailTrace_334654 : CollatzResearch.WordTrace tailWord_334654 prefixEnd_334654 25457534066642799760883 := by
  unfold tailWord_334654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525729266201648399752377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8137222753075458132012677 1525729266201648399752377)
  ·
    refine ⟨1144296949651236299814283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1525729266201648399752377 1144296949651236299814283)
    ·
      refine ⟨1716445424476854449721425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144296949651236299814283 1716445424476854449721425)
      ·
        refine ⟨1287334068357640837291069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716445424476854449721425 1287334068357640837291069)
        ·
          refine ⟨482750275634115313984151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1287334068357640837291069 482750275634115313984151)
          ·
            refine ⟨724125413451172970976227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482750275634115313984151 724125413451172970976227)
            ·
              refine ⟨1086188120176759456464341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724125413451172970976227 1086188120176759456464341)
              ·
                refine ⟨25457534066642799760883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1086188120176759456464341 25457534066642799760883)
                ·
                  rfl

theorem cell21_334654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_334654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334654 prefixEnd_334654 := by exact prefixLift 334654
  have htrace : WordTrace (prefixWord ++ tailWord_334654) baseStart_334654 baseEnd_334654 := by
    simpa [prefixWord, tailWord_334654, baseEnd_334654] using wordTrace_append hprefix tailTrace_334654
  have hstable : (prefixWord ++ tailWord_334654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334654).length < 2 ^ (prefixWord ++ tailWord_334654).sum := by decide
  have hdescent : baseEnd_334654 < baseStart_334654 := by decide
  rcases family_descends (prefixWord ++ tailWord_334654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334660 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_334660 : Nat := 118140960795 + 334660 * 2 ^ 59
def prefixEnd_334660 : Nat := 4983230072969 + 3 ^ 40 * 334660 * 2
def baseEnd_334660 : Nat := 76373971481673722182637

theorem tailTrace_334660 : CollatzResearch.WordTrace tailWord_334660 prefixEnd_334660 76373971481673722182637 := by
  unfold tailWord_334660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103026483795725111368717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8137368645060966815158289 6103026483795725111368717)
  ·
    refine ⟨2288634931423396916763269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6103026483795725111368717 2288634931423396916763269)
    ·
      refine ⟨429119049641886921893113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2288634931423396916763269 429119049641886921893113)
      ·
        refine ⟨321839287231415191419835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429119049641886921893113 321839287231415191419835)
        ·
          refine ⟨482758930847122787129753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321839287231415191419835 482758930847122787129753)
          ·
            refine ⟨362069198135342090347315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482758930847122787129753 362069198135342090347315)
            ·
              refine ⟨543103797203013135520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362069198135342090347315 543103797203013135520973)
              ·
                refine ⟨203663923951129925820365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543103797203013135520973 203663923951129925820365)
                ·
                  refine ⟨76373971481673722182637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203663923951129925820365 76373971481673722182637)
                  ·
                    rfl

theorem cell21_334660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_334660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334660 prefixEnd_334660 := by exact prefixLift 334660
  have htrace : WordTrace (prefixWord ++ tailWord_334660) baseStart_334660 baseEnd_334660 := by
    simpa [prefixWord, tailWord_334660, baseEnd_334660] using wordTrace_append hprefix tailTrace_334660
  have hstable : (prefixWord ++ tailWord_334660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334660).length < 2 ^ (prefixWord ++ tailWord_334660).sum := by decide
  have hdescent : baseEnd_334660 < baseStart_334660 := by decide
  rcases family_descends (prefixWord ++ tailWord_334660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334682 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_334682 : Nat := 118140960795 + 334682 * 2 ^ 59
def prefixEnd_334682 : Nat := 4983230072969 + 3 ^ 40 * 334682 * 2
def baseEnd_334682 : Nat := 76378992181406572815925

theorem tailTrace_334682 : CollatzResearch.WordTrace tailWord_334682 prefixEnd_334682 76378992181406572815925 := by
  unfold tailWord_334682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051713843377936995009575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8137903582341165320025533 3051713843377936995009575)
  ·
    refine ⟨4577570765066905492514363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3051713843377936995009575 4577570765066905492514363)
    ·
      refine ⟨6866356147600358238771545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577570765066905492514363 6866356147600358238771545)
      ·
        refine ⟨5149767110700268679078659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6866356147600358238771545 5149767110700268679078659)
        ·
          refine ⟨7724650666050403018617989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149767110700268679078659 7724650666050403018617989)
          ·
            refine ⟨1448371999884450565990873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7724650666050403018617989 1448371999884450565990873)
            ·
              refine ⟨1086278999913337924493155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448371999884450565990873 1086278999913337924493155)
              ·
                refine ⟨1629418499870006886739733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086278999913337924493155 1629418499870006886739733)
                ·
                  refine ⟨76378992181406572815925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1629418499870006886739733 76378992181406572815925)
                  ·
                    rfl

theorem cell21_334682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_334682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334682 prefixEnd_334682 := by exact prefixLift 334682
  have htrace : WordTrace (prefixWord ++ tailWord_334682) baseStart_334682 baseEnd_334682 := by
    simpa [prefixWord, tailWord_334682, baseEnd_334682] using wordTrace_append hprefix tailTrace_334682
  have hstable : (prefixWord ++ tailWord_334682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334682).length < 2 ^ (prefixWord ++ tailWord_334682).sum := by decide
  have hdescent : baseEnd_334682 < baseStart_334682 := by decide
  rcases family_descends (prefixWord ++ tailWord_334682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334699 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 4]
def baseStart_334699 : Nat := 118140960795 + 334699 * 2 ^ 59
def prefixEnd_334699 : Nat := 4983230072969 + 3 ^ 40 * 334699 * 2
def baseEnd_334699 : Nat := 76382871813018321032557

theorem tailTrace_334699 : CollatzResearch.WordTrace tailWord_334699 prefixEnd_334699 76382871813018321032557 := by
  unfold tailWord_334699
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207475414450159883407151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8138316942966773255604767 12207475414450159883407151)
  ·
    refine ⟨18311213121675239825110727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12207475414450159883407151 18311213121675239825110727)
    ·
      refine ⟨27466819682512859737666091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18311213121675239825110727 27466819682512859737666091)
      ·
        refine ⟨41200229523769289606499137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27466819682512859737666091 41200229523769289606499137)
        ·
          refine ⟨30900172142826967204874353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41200229523769289606499137 30900172142826967204874353)
          ·
            refine ⟨23175129107120225403655765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30900172142826967204874353 23175129107120225403655765)
            ·
              refine ⟨271583544224065141449091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 23175129107120225403655765 271583544224065141449091)
              ·
                refine ⟨407375316336097712173637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271583544224065141449091 407375316336097712173637)
                ·
                  refine ⟨76382871813018321032557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407375316336097712173637 76382871813018321032557)
                  ·
                    rfl

theorem cell21_334699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4].length) (baseStart_334699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334699 prefixEnd_334699 := by exact prefixLift 334699
  have htrace : WordTrace (prefixWord ++ tailWord_334699) baseStart_334699 baseEnd_334699 := by
    simpa [prefixWord, tailWord_334699, baseEnd_334699] using wordTrace_append hprefix tailTrace_334699
  have hstable : (prefixWord ++ tailWord_334699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334699).length < 2 ^ (prefixWord ++ tailWord_334699).sum := by decide
  have hdescent : baseEnd_334699 < baseStart_334699 := by decide
  rcases family_descends (prefixWord ++ tailWord_334699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334792 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_334792 : Nat := 118140960795 + 334792 * 2 ^ 59
def prefixEnd_334792 : Nat := 4983230072969 + 3 ^ 40 * 334792 * 2
def baseEnd_334792 : Nat := 76404095680070825982367

theorem tailTrace_334792 : CollatzResearch.WordTrace tailWord_334792 prefixEnd_334792 76404095680070825982367 := by
  unfold tailWord_334792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105433701556618383271315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8140578268742157844361753 6105433701556618383271315)
  ·
    refine ⟨9158150552334927574906973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6105433701556618383271315 9158150552334927574906973)
    ·
      refine ⟨3434306457125597840590115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9158150552334927574906973 3434306457125597840590115)
      ·
        refine ⟨5151459685688396760885173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434306457125597840590115 5151459685688396760885173)
        ·
          refine ⟨482949345533287196332985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5151459685688396760885173 482949345533287196332985)
          ·
            refine ⟨362212009149965397249739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482949345533287196332985 362212009149965397249739)
            ·
              refine ⟨543318013724948095874609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362212009149965397249739 543318013724948095874609)
              ·
                refine ⟨407488510293711071905957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543318013724948095874609 407488510293711071905957)
                ·
                  refine ⟨76404095680070825982367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407488510293711071905957 76404095680070825982367)
                  ·
                    rfl

theorem cell21_334792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_334792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334792 prefixEnd_334792 := by exact prefixLift 334792
  have htrace : WordTrace (prefixWord ++ tailWord_334792) baseStart_334792 baseEnd_334792 := by
    simpa [prefixWord, tailWord_334792, baseEnd_334792] using wordTrace_append hprefix tailTrace_334792
  have hstable : (prefixWord ++ tailWord_334792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334792).length < 2 ^ (prefixWord ++ tailWord_334792).sum := by decide
  have hdescent : baseEnd_334792 < baseStart_334792 := by decide
  rcases family_descends (prefixWord ++ tailWord_334792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334896 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_334896 : Nat := 118140960795 + 334896 * 2 ^ 59
def prefixEnd_334896 : Nat := 4983230072969 + 3 ^ 40 * 334896 * 2
def baseEnd_334896 : Nat := 76427829896989756248821

theorem tailTrace_334896 : CollatzResearch.WordTrace tailWord_334896 prefixEnd_334896 76427829896989756248821 := by
  unfold tailWord_334896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6107330297368231264164271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8143107063157641685552361 6107330297368231264164271)
  ·
    refine ⟨9160995446052346896246407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6107330297368231264164271 9160995446052346896246407)
    ·
      refine ⟨13741493169078520344369611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9160995446052346896246407 13741493169078520344369611)
      ·
        refine ⟨20612239753617780516554417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13741493169078520344369611 20612239753617780516554417)
        ·
          refine ⟨15459179815213335387415813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20612239753617780516554417 15459179815213335387415813)
          ·
            refine ⟨2898596215352500385140465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15459179815213335387415813 2898596215352500385140465)
            ·
              refine ⟨2173947161514375288855349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898596215352500385140465 2173947161514375288855349)
              ·
                refine ⟨203807546391972683330189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2173947161514375288855349 203807546391972683330189)
                ·
                  refine ⟨76427829896989756248821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203807546391972683330189 76427829896989756248821)
                  ·
                    rfl

theorem cell21_334896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_334896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334896 prefixEnd_334896 := by exact prefixLift 334896
  have htrace : WordTrace (prefixWord ++ tailWord_334896) baseStart_334896 baseEnd_334896 := by
    simpa [prefixWord, tailWord_334896, baseEnd_334896] using wordTrace_append hprefix tailTrace_334896
  have hstable : (prefixWord ++ tailWord_334896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334896).length < 2 ^ (prefixWord ++ tailWord_334896).sum := by decide
  have hdescent : baseEnd_334896 < baseStart_334896 := by decide
  rcases family_descends (prefixWord ++ tailWord_334896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334972 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_334972 : Nat := 118140960795 + 334972 * 2 ^ 59
def prefixEnd_334972 : Nat := 4983230072969 + 3 ^ 40 * 334972 * 2
def baseEnd_334972 : Nat := 76445174132430512981999

theorem tailTrace_334972 : CollatzResearch.WordTrace tailWord_334972 prefixEnd_334972 76445174132430512981999 := by
  unfold tailWord_334972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108716271230563754047585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8144955028307418338730113 6108716271230563754047585)
  ·
    refine ⟨4581537203422922815535689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6108716271230563754047585 4581537203422922815535689)
    ·
      refine ⟨3436152902567192111651767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4581537203422922815535689 3436152902567192111651767)
      ·
        refine ⟨5154229353850788167477651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436152902567192111651767 5154229353850788167477651)
        ·
          refine ⟨7731344030776182251216477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5154229353850788167477651 7731344030776182251216477)
          ·
            refine ⟨2899254011541068344206179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7731344030776182251216477 2899254011541068344206179)
            ·
              refine ⟨4348881017311602516309269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899254011541068344206179 4348881017311602516309269)
              ·
                refine ⟨203853797686481367951997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4348881017311602516309269 203853797686481367951997)
                ·
                  refine ⟨76445174132430512981999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203853797686481367951997 76445174132430512981999)
                  ·
                    rfl

theorem cell21_334972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_334972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_334972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_334972 prefixEnd_334972 := by exact prefixLift 334972
  have htrace : WordTrace (prefixWord ++ tailWord_334972) baseStart_334972 baseEnd_334972 := by
    simpa [prefixWord, tailWord_334972, baseEnd_334972] using wordTrace_append hprefix tailTrace_334972
  have hstable : (prefixWord ++ tailWord_334972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334972).length < 2 ^ (prefixWord ++ tailWord_334972).sum := by decide
  have hdescent : baseEnd_334972 < baseStart_334972 := by decide
  rcases family_descends (prefixWord ++ tailWord_334972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335006 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_335006 : Nat := 118140960795 + 335006 * 2 ^ 59
def prefixEnd_335006 : Nat := 4983230072969 + 3 ^ 40 * 335006 * 2
def baseEnd_335006 : Nat := 76452933395654009415263

theorem tailTrace_335006 : CollatzResearch.WordTrace tailWord_335006 prefixEnd_335006 76452933395654009415263 := by
  unfold tailWord_335006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527334078042243914354109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8145781749558634209888581 1527334078042243914354109)
  ·
    refine ⟨572750279265841467882791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1527334078042243914354109 572750279265841467882791)
    ·
      refine ⟨859125418898762201824187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572750279265841467882791 859125418898762201824187)
      ·
        refine ⟨1288688128348143302736281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859125418898762201824187 1288688128348143302736281)
        ·
          refine ⟨966516096261107477052211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288688128348143302736281 966516096261107477052211)
          ·
            refine ⟨1449774144391661215578317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966516096261107477052211 1449774144391661215578317)
            ·
              refine ⟨543665304146872955841869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1449774144391661215578317 543665304146872955841869)
              ·
                refine ⟨203874489055077358440701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543665304146872955841869 203874489055077358440701)
                ·
                  refine ⟨76452933395654009415263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203874489055077358440701 76452933395654009415263)
                  ·
                    rfl

theorem cell21_335006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_335006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335006 prefixEnd_335006 := by exact prefixLift 335006
  have htrace : WordTrace (prefixWord ++ tailWord_335006) baseStart_335006 baseEnd_335006 := by
    simpa [prefixWord, tailWord_335006, baseEnd_335006] using wordTrace_append hprefix tailTrace_335006
  have hstable : (prefixWord ++ tailWord_335006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335006).length < 2 ^ (prefixWord ++ tailWord_335006).sum := by decide
  have hdescent : baseEnd_335006 < baseStart_335006 := by decide
  rcases family_descends (prefixWord ++ tailWord_335006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335082 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_335082 : Nat := 118140960795 + 335082 * 2 ^ 59
def prefixEnd_335082 : Nat := 4983230072969 + 3 ^ 40 * 335082 * 2
def baseEnd_335082 : Nat := 76470277631094766148441

theorem tailTrace_335082 : CollatzResearch.WordTrace tailWord_335082 prefixEnd_335082 76470277631094766148441 := by
  unfold tailWord_335082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055361143015654073649875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8147629714708410863066333 3055361143015654073649875)
  ·
    refine ⟨4583041714523481110474813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055361143015654073649875 4583041714523481110474813)
    ·
      refine ⟨1718640642946305416428055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4583041714523481110474813 1718640642946305416428055)
      ·
        refine ⟨2577960964419458124642083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718640642946305416428055 2577960964419458124642083)
        ·
          refine ⟨3866941446629187186963125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577960964419458124642083 3866941446629187186963125)
          ·
            refine ⟨362525760621486298777793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3866941446629187186963125 362525760621486298777793)
            ·
              refine ⟨271894320466114724083345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362525760621486298777793 271894320466114724083345)
              ·
                refine ⟨203920740349586043062509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271894320466114724083345 203920740349586043062509)
                ·
                  refine ⟨76470277631094766148441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203920740349586043062509 76470277631094766148441)
                  ·
                    rfl

theorem cell21_335082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_335082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335082 prefixEnd_335082 := by exact prefixLift 335082
  have htrace : WordTrace (prefixWord ++ tailWord_335082) baseStart_335082 baseEnd_335082 := by
    simpa [prefixWord, tailWord_335082, baseEnd_335082] using wordTrace_append hprefix tailTrace_335082
  have hstable : (prefixWord ++ tailWord_335082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335082).length < 2 ^ (prefixWord ++ tailWord_335082).sum := by decide
  have hdescent : baseEnd_335082 < baseStart_335082 := by decide
  rcases family_descends (prefixWord ++ tailWord_335082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335107 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_335107 : Nat := 118140960795 + 335107 * 2 ^ 59
def prefixEnd_335107 : Nat := 4983230072969 + 3 ^ 40 * 335107 * 2
def baseEnd_335107 : Nat := 76475982971700278231723

theorem tailTrace_335107 : CollatzResearch.WordTrace tailWord_335107 prefixEnd_335107 76475982971700278231723 := by
  unfold tailWord_335107
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222356396972045564259575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148237597981363709506383 12222356396972045564259575)
  ·
    refine ⟨18333534595458068346389363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12222356396972045564259575 18333534595458068346389363)
    ·
      refine ⟨27500301893187102519584045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18333534595458068346389363 27500301893187102519584045)
      ·
        refine ⟨10312613209945163444844017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27500301893187102519584045 10312613209945163444844017)
        ·
          refine ⟨7734459907458872583633013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10312613209945163444844017 7734459907458872583633013)
          ·
            refine ⟨725105616324269304715595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7734459907458872583633013 725105616324269304715595)
            ·
              refine ⟨1087658424486403957073393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725105616324269304715595 1087658424486403957073393)
              ·
                refine ⟨815743818364802967805045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087658424486403957073393 815743818364802967805045)
                ·
                  refine ⟨76475982971700278231723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 815743818364802967805045 76475982971700278231723)
                  ·
                    rfl

theorem cell21_335107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_335107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335107 prefixEnd_335107 := by exact prefixLift 335107
  have htrace : WordTrace (prefixWord ++ tailWord_335107) baseStart_335107 baseEnd_335107 := by
    simpa [prefixWord, tailWord_335107, baseEnd_335107] using wordTrace_append hprefix tailTrace_335107
  have hstable : (prefixWord ++ tailWord_335107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335107).length < 2 ^ (prefixWord ++ tailWord_335107).sum := by decide
  have hdescent : baseEnd_335107 < baseStart_335107 := by decide
  rcases family_descends (prefixWord ++ tailWord_335107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335121 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_335121 : Nat := 118140960795 + 335121 * 2 ^ 59
def prefixEnd_335121 : Nat := 4983230072969 + 3 ^ 40 * 335121 * 2
def baseEnd_335121 : Nat := 76479177962439364998361

theorem tailTrace_335121 : CollatzResearch.WordTrace tailWord_335121 prefixEnd_335121 76479177962439364998361 := by
  unfold tailWord_335121
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222867018921325955269217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148578012614217303512811 12222867018921325955269217)
  ·
    refine ⟨9167150264190994466451913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12222867018921325955269217 9167150264190994466451913)
    ·
      refine ⟨6875362698143245849838935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9167150264190994466451913 6875362698143245849838935)
      ·
        refine ⟨10313044047214868774758403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6875362698143245849838935 10313044047214868774758403)
        ·
          refine ⟨15469566070822303162137605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10313044047214868774758403 15469566070822303162137605)
          ·
            refine ⟨2900543638279181842900801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15469566070822303162137605 2900543638279181842900801)
            ·
              refine ⟨2175407728709386382175601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900543638279181842900801 2175407728709386382175601)
              ·
                refine ⟨1631555796532039786631701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2175407728709386382175601 1631555796532039786631701)
                ·
                  refine ⟨76479177962439364998361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1631555796532039786631701 76479177962439364998361)
                  ·
                    rfl

theorem cell21_335121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_335121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335121 prefixEnd_335121 := by exact prefixLift 335121
  have htrace : WordTrace (prefixWord ++ tailWord_335121) baseStart_335121 baseEnd_335121 := by
    simpa [prefixWord, tailWord_335121, baseEnd_335121] using wordTrace_append hprefix tailTrace_335121
  have hstable : (prefixWord ++ tailWord_335121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335121).length < 2 ^ (prefixWord ++ tailWord_335121).sum := by decide
  have hdescent : baseEnd_335121 < baseStart_335121 := by decide
  rcases family_descends (prefixWord ++ tailWord_335121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335155 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 4]
def baseStart_335155 : Nat := 118140960795 + 335155 * 2 ^ 59
def prefixEnd_335155 : Nat := 4983230072969 + 3 ^ 40 * 335155 * 2
def baseEnd_335155 : Nat := 76486937225662861431625

theorem tailTrace_335155 : CollatzResearch.WordTrace tailWord_335155 prefixEnd_335155 76486937225662861431625 := by
  unfold tailWord_335155
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224107100798149762006919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8149404733865433174671279 12224107100798149762006919)
  ·
    refine ⟨18336160651197224643010379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224107100798149762006919 18336160651197224643010379)
    ·
      refine ⟨27504240976795836964515569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18336160651197224643010379 27504240976795836964515569)
      ·
        refine ⟨20628180732596877723386677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27504240976795836964515569 20628180732596877723386677)
        ·
          refine ⟨1933891943680957286567501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20628180732596877723386677 1933891943680957286567501)
          ·
            refine ⟨725209478880358982462813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1933891943680957286567501 725209478880358982462813)
            ·
              refine ⟨271953554580134618423555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725209478880358982462813 271953554580134618423555)
              ·
                refine ⟨407930331870201927635333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271953554580134618423555 407930331870201927635333)
                ·
                  refine ⟨76486937225662861431625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407930331870201927635333 76486937225662861431625)
                  ·
                    rfl

theorem cell21_335155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4].length) (baseStart_335155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335155 prefixEnd_335155 := by exact prefixLift 335155
  have htrace : WordTrace (prefixWord ++ tailWord_335155) baseStart_335155 baseEnd_335155 := by
    simpa [prefixWord, tailWord_335155, baseEnd_335155] using wordTrace_append hprefix tailTrace_335155
  have hstable : (prefixWord ++ tailWord_335155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335155).length < 2 ^ (prefixWord ++ tailWord_335155).sum := by decide
  have hdescent : baseEnd_335155 < baseStart_335155 := by decide
  rcases family_descends (prefixWord ++ tailWord_335155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335169 : List Nat := [1, 2, 5, 2, 1, 2, 1, 7]
def baseStart_335169 : Nat := 118140960795 + 335169 * 2 ^ 59
def prefixEnd_335169 : Nat := 4983230072969 + 3 ^ 40 * 335169 * 2
def baseEnd_335169 : Nat := 25496710738800649399421

theorem tailTrace_335169 : CollatzResearch.WordTrace tailWord_335169 prefixEnd_335169 25496710738800649399421 := by
  unfold tailWord_335169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224617722747430153016561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8149745148498286768677707 12224617722747430153016561)
  ·
    refine ⟨9168463292060572614762421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12224617722747430153016561 9168463292060572614762421)
    ·
      refine ⟨859543433630678682633977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9168463292060572614762421 859543433630678682633977)
      ·
        refine ⟨644657575223009011975483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 859543433630678682633977 644657575223009011975483)
        ·
          refine ⟨966986362834513517963225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644657575223009011975483 966986362834513517963225)
          ·
            refine ⟨725239772125885138472419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966986362834513517963225 725239772125885138472419)
            ·
              refine ⟨1087859658188827707708629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725239772125885138472419 1087859658188827707708629)
              ·
                refine ⟨25496710738800649399421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1087859658188827707708629 25496710738800649399421)
                ·
                  rfl

theorem cell21_335169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_335169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335169 prefixEnd_335169 := by exact prefixLift 335169
  have htrace : WordTrace (prefixWord ++ tailWord_335169) baseStart_335169 baseEnd_335169 := by
    simpa [prefixWord, tailWord_335169, baseEnd_335169] using wordTrace_append hprefix tailTrace_335169
  have hstable : (prefixWord ++ tailWord_335169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335169).length < 2 ^ (prefixWord ++ tailWord_335169).sum := by decide
  have hdescent : baseEnd_335169 < baseStart_335169 := by decide
  rcases family_descends (prefixWord ++ tailWord_335169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335200 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_335200 : Nat := 118140960795 + 335200 * 2 ^ 59
def prefixEnd_335200 : Nat := 4983230072969 + 3 ^ 40 * 335200 * 2
def baseEnd_335200 : Nat := 76497206838752783181533

theorem tailTrace_335200 : CollatzResearch.WordTrace tailWord_335200 prefixEnd_335200 76497206838752783181533 := by
  unfold tailWord_335200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112874192817561223697527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8150498923756748298263369 6112874192817561223697527)
  ·
    refine ⟨9169311289226341835546291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6112874192817561223697527 9169311289226341835546291)
    ·
      refine ⟨13753966933839512753319437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9169311289226341835546291 13753966933839512753319437)
      ·
        refine ⟨5157737600189817282494789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13753966933839512753319437 5157737600189817282494789)
        ·
          refine ⟨967075800035590740467773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5157737600189817282494789 967075800035590740467773)
          ·
            refine ⟨362653425013346527675415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 967075800035590740467773 362653425013346527675415)
            ·
              refine ⟨543980137520019791513123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362653425013346527675415 543980137520019791513123)
              ·
                refine ⟨815970206280029687269685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543980137520019791513123 815970206280029687269685)
                ·
                  refine ⟨76497206838752783181533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 815970206280029687269685 76497206838752783181533)
                  ·
                    rfl

theorem cell21_335200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_335200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335200 prefixEnd_335200 := by exact prefixLift 335200
  have htrace : WordTrace (prefixWord ++ tailWord_335200) baseStart_335200 baseEnd_335200 := by
    simpa [prefixWord, tailWord_335200, baseEnd_335200] using wordTrace_append hprefix tailTrace_335200
  have hstable : (prefixWord ++ tailWord_335200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335200).length < 2 ^ (prefixWord ++ tailWord_335200).sum := by decide
  have hdescent : baseEnd_335200 < baseStart_335200 := by decide
  rcases family_descends (prefixWord ++ tailWord_335200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335335 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_335335 : Nat := 118140960795 + 335335 * 2 ^ 59
def prefixEnd_335335 : Nat := 4983230072969 + 3 ^ 40 * 335335 * 2
def baseEnd_335335 : Nat := 76528015678022548431257

theorem tailTrace_335335 : CollatzResearch.WordTrace tailWord_335335 prefixEnd_335335 76528015678022548431257 := by
  unfold tailWord_335335
  simp only [CollatzResearch.WordTrace]
  refine ⟨12230672240146040503559459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8153781493430693669039639 12230672240146040503559459)
  ·
    refine ⟨18346008360219060755339189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12230672240146040503559459 18346008360219060755339189)
    ·
      refine ⟨1719938283770536945813049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18346008360219060755339189 1719938283770536945813049)
      ·
        refine ⟨1289953712827902709359787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1719938283770536945813049 1289953712827902709359787)
        ·
          refine ⟨1934930569241854064039681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289953712827902709359787 1934930569241854064039681)
          ·
            refine ⟨1451197926931390548029761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1934930569241854064039681 1451197926931390548029761)
            ·
              refine ⟨1088398445198542911022321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451197926931390548029761 1088398445198542911022321)
              ·
                refine ⟨816298833898907183266741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088398445198542911022321 816298833898907183266741)
                ·
                  refine ⟨76528015678022548431257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 816298833898907183266741 76528015678022548431257)
                  ·
                    rfl

theorem cell21_335335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_335335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335335 prefixEnd_335335 := by exact prefixLift 335335
  have htrace : WordTrace (prefixWord ++ tailWord_335335) baseStart_335335 baseEnd_335335 := by
    simpa [prefixWord, tailWord_335335, baseEnd_335335] using wordTrace_append hprefix tailTrace_335335
  have hstable : (prefixWord ++ tailWord_335335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335335).length < 2 ^ (prefixWord ++ tailWord_335335).sum := by decide
  have hdescent : baseEnd_335335 < baseStart_335335 := by decide
  rcases family_descends (prefixWord ++ tailWord_335335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335338 : List Nat := [3, 1, 3, 1, 4, 2, 2, 5]
def baseStart_335338 : Nat := 118140960795 + 335338 * 2 ^ 59
def prefixEnd_335338 : Nat := 4983230072969 + 3 ^ 40 * 335338 * 2
def baseEnd_335338 : Nat := 25509566772965069960417

theorem tailTrace_335338 : CollatzResearch.WordTrace tailWord_335338 prefixEnd_335338 25509566772965069960417 := by
  unfold tailWord_335338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057695414783793003979667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8153854439423448010612445 3057695414783793003979667)
  ·
    refine ⟨4586543122175689505969501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3057695414783793003979667 4586543122175689505969501)
    ·
      refine ⟨1719953670815883564738563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4586543122175689505969501 1719953670815883564738563)
      ·
        refine ⟨2579930506223825347107845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719953670815883564738563 2579930506223825347107845)
        ·
          refine ⟨483736969916967252582721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2579930506223825347107845 483736969916967252582721)
          ·
            refine ⟨362802727437725439437041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483736969916967252582721 362802727437725439437041)
            ·
              refine ⟨272102045578294079577781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362802727437725439437041 272102045578294079577781)
              ·
                refine ⟨25509566772965069960417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272102045578294079577781 25509566772965069960417)
                ·
                  rfl

theorem cell21_335338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_335338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335338 prefixEnd_335338 := by exact prefixLift 335338
  have htrace : WordTrace (prefixWord ++ tailWord_335338) baseStart_335338 baseEnd_335338 := by
    simpa [prefixWord, tailWord_335338, baseEnd_335338] using wordTrace_append hprefix tailTrace_335338
  have hstable : (prefixWord ++ tailWord_335338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335338).length < 2 ^ (prefixWord ++ tailWord_335338).sum := by decide
  have hdescent : baseEnd_335338 < baseStart_335338 := by decide
  rcases family_descends (prefixWord ++ tailWord_335338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335352 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_335352 : Nat := 118140960795 + 335352 * 2 ^ 59
def prefixEnd_335352 : Nat := 4983230072969 + 3 ^ 40 * 335352 * 2
def baseEnd_335352 : Nat := 76531895309634296647889

theorem tailTrace_335352 : CollatzResearch.WordTrace tailWord_335352 prefixEnd_335352 76531895309634296647889 := by
  unfold tailWord_335352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115646140542226203464155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8154194854056301604618873 6115646140542226203464155)
  ·
    refine ⟨9173469210813339305196233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6115646140542226203464155 9173469210813339305196233)
    ·
      refine ⟨6880101908110004478897175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9173469210813339305196233 6880101908110004478897175)
      ·
        refine ⟨10320152862165006718345763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880101908110004478897175 10320152862165006718345763)
        ·
          refine ⟨15480229293247510077518645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10320152862165006718345763 15480229293247510077518645)
          ·
            refine ⟨1451271496241954069767373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15480229293247510077518645 1451271496241954069767373)
            ·
              refine ⟨544226811090732776162765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451271496241954069767373 544226811090732776162765)
              ·
                refine ⟨204085054159024791061037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544226811090732776162765 204085054159024791061037)
                ·
                  refine ⟨76531895309634296647889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204085054159024791061037 76531895309634296647889)
                  ·
                    rfl

theorem cell21_335352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_335352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335352 prefixEnd_335352 := by exact prefixLift 335352
  have htrace : WordTrace (prefixWord ++ tailWord_335352) baseStart_335352 baseEnd_335352 := by
    simpa [prefixWord, tailWord_335352, baseEnd_335352] using wordTrace_append hprefix tailTrace_335352
  have hstable : (prefixWord ++ tailWord_335352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335352).length < 2 ^ (prefixWord ++ tailWord_335352).sum := by decide
  have hdescent : baseEnd_335352 < baseStart_335352 := by decide
  rcases family_descends (prefixWord ++ tailWord_335352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335442 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_335442 : Nat := 118140960795 + 335442 * 2 ^ 59
def prefixEnd_335442 : Nat := 4983230072969 + 3 ^ 40 * 335442 * 2
def baseEnd_335442 : Nat := 76552434535814140147705

theorem tailTrace_335442 : CollatzResearch.WordTrace tailWord_335442 prefixEnd_335442 76552434535814140147705 := by
  unfold tailWord_335442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058643712689599444426145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8156383233838931851803053 3058643712689599444426145)
  ·
    refine ⟨2293982784517199583319609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3058643712689599444426145 2293982784517199583319609)
    ·
      refine ⟨1720487088387899687489707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2293982784517199583319609 1720487088387899687489707)
      ·
        refine ⟨2580730632581849531234561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720487088387899687489707 2580730632581849531234561)
        ·
          refine ⟨1935547974436387148425921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580730632581849531234561 1935547974436387148425921)
          ·
            refine ⟨1451660980827290361319441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935547974436387148425921 1451660980827290361319441)
            ·
              refine ⟨1088745735620467770989581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451660980827290361319441 1088745735620467770989581)
              ·
                refine ⟨408279650857675414121093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1088745735620467770989581 408279650857675414121093)
                ·
                  refine ⟨76552434535814140147705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408279650857675414121093 76552434535814140147705)
                  ·
                    rfl

theorem cell21_335442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_335442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335442 prefixEnd_335442 := by exact prefixLift 335442
  have htrace : WordTrace (prefixWord ++ tailWord_335442) baseStart_335442 baseEnd_335442 := by
    simpa [prefixWord, tailWord_335442, baseEnd_335442] using wordTrace_append hprefix tailTrace_335442
  have hstable : (prefixWord ++ tailWord_335442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335442).length < 2 ^ (prefixWord ++ tailWord_335442).sum := by decide
  have hdescent : baseEnd_335442 < baseStart_335442 := by decide
  rcases family_descends (prefixWord ++ tailWord_335442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335518 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_335518 : Nat := 118140960795 + 335518 * 2 ^ 59
def prefixEnd_335518 : Nat := 4983230072969 + 3 ^ 40 * 335518 * 2
def baseEnd_335518 : Nat := 76569778771254896880883

theorem tailTrace_335518 : CollatzResearch.WordTrace tailWord_335518 prefixEnd_335518 76569778771254896880883 := by
  unfold tailWord_335518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529668349810382844683901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8158231198988708504980805 1529668349810382844683901)
  ·
    refine ⟨573625631178893566756463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1529668349810382844683901 573625631178893566756463)
    ·
      refine ⟨860438446768340350134695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573625631178893566756463 860438446768340350134695)
      ·
        refine ⟨1290657670152510525202043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860438446768340350134695 1290657670152510525202043)
        ·
          refine ⟨1935986505228765787803065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290657670152510525202043 1935986505228765787803065)
          ·
            refine ⟨1451989878921574340852299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935986505228765787803065 1451989878921574340852299)
            ·
              refine ⟨2177984818382361511278449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451989878921574340852299 2177984818382361511278449)
              ·
                refine ⟨1633488613786771133458837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177984818382361511278449 1633488613786771133458837)
                ·
                  refine ⟨76569778771254896880883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1633488613786771133458837 76569778771254896880883)
                  ·
                    rfl

theorem cell21_335518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_335518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335518 prefixEnd_335518 := by exact prefixLift 335518
  have htrace : WordTrace (prefixWord ++ tailWord_335518) baseStart_335518 baseEnd_335518 := by
    simpa [prefixWord, tailWord_335518, baseEnd_335518] using wordTrace_append hprefix tailTrace_335518
  have hstable : (prefixWord ++ tailWord_335518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335518).length < 2 ^ (prefixWord ++ tailWord_335518).sum := by decide
  have hdescent : baseEnd_335518 < baseStart_335518 := by decide
  rcases family_descends (prefixWord ++ tailWord_335518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335521 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 3]
def baseStart_335521 : Nat := 118140960795 + 335521 * 2 ^ 59
def prefixEnd_335521 : Nat := 4983230072969 + 3 ^ 40 * 335521 * 2
def baseEnd_335521 : Nat := 76570463412127558330877

theorem tailTrace_335521 : CollatzResearch.WordTrace tailWord_335521 prefixEnd_335521 76570463412127558330877 := by
  unfold tailWord_335521
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237456217472194269830417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8158304144981462846553611 12237456217472194269830417)
  ·
    refine ⟨9178092163104145702372813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12237456217472194269830417 9178092163104145702372813)
    ·
      refine ⟨3441784561164054638389805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9178092163104145702372813 3441784561164054638389805)
      ·
        refine ⟨1290669210436520489396177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3441784561164054638389805 1290669210436520489396177)
        ·
          refine ⟨968001907827390367047133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290669210436520489396177 968001907827390367047133)
          ·
            refine ⟨363000715435271387642675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 968001907827390367047133 363000715435271387642675)
            ·
              refine ⟨544501073152907081464013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363000715435271387642675 544501073152907081464013)
              ·
                refine ⟨204187902432340155549005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544501073152907081464013 204187902432340155549005)
                ·
                  refine ⟨76570463412127558330877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204187902432340155549005 76570463412127558330877)
                  ·
                    rfl

theorem cell21_335521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_335521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335521 prefixEnd_335521 := by exact prefixLift 335521
  have htrace : WordTrace (prefixWord ++ tailWord_335521) baseStart_335521 baseEnd_335521 := by
    simpa [prefixWord, tailWord_335521, baseEnd_335521] using wordTrace_append hprefix tailTrace_335521
  have hstable : (prefixWord ++ tailWord_335521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335521).length < 2 ^ (prefixWord ++ tailWord_335521).sum := by decide
  have hdescent : baseEnd_335521 < baseStart_335521 := by decide
  rcases family_descends (prefixWord ++ tailWord_335521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335597 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 3]
def baseStart_335597 : Nat := 118140960795 + 335597 * 2 ^ 59
def prefixEnd_335597 : Nat := 4983230072969 + 3 ^ 40 * 335597 * 2
def baseEnd_335597 : Nat := 76587807647568315064055

theorem tailTrace_335597 : CollatzResearch.WordTrace tailWord_335597 prefixEnd_335597 76587807647568315064055 := by
  unfold tailWord_335597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240228165196859249597045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8160152110131239499731363 12240228165196859249597045)
  ·
    refine ⟨1147521390487205554649723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12240228165196859249597045 1147521390487205554649723)
    ·
      refine ⟨1721282085730808331974585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147521390487205554649723 1721282085730808331974585)
      ·
        refine ⟨1290961564298106248980939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721282085730808331974585 1290961564298106248980939)
        ·
          refine ⟨1936442346447159373471409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290961564298106248980939 1936442346447159373471409)
          ·
            refine ⟨1452331759835369530103557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1936442346447159373471409 1452331759835369530103557)
            ·
              refine ⟨272312204969131786894417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1452331759835369530103557 272312204969131786894417)
              ·
                refine ⟨204234153726848840170813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272312204969131786894417 204234153726848840170813)
                ·
                  refine ⟨76587807647568315064055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204234153726848840170813 76587807647568315064055)
                  ·
                    rfl

theorem cell21_335597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_335597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335597 prefixEnd_335597 := by exact prefixLift 335597
  have htrace : WordTrace (prefixWord ++ tailWord_335597) baseStart_335597 baseEnd_335597 := by
    simpa [prefixWord, tailWord_335597, baseEnd_335597] using wordTrace_append hprefix tailTrace_335597
  have hstable : (prefixWord ++ tailWord_335597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335597).length < 2 ^ (prefixWord ++ tailWord_335597).sum := by decide
  have hdescent : baseEnd_335597 < baseStart_335597 := by decide
  rcases family_descends (prefixWord ++ tailWord_335597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335653 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_335653 : Nat := 118140960795 + 335653 * 2 ^ 59
def prefixEnd_335653 : Nat := 4983230072969 + 3 ^ 40 * 335653 * 2
def baseEnd_335653 : Nat := 76600587610524662130607

theorem tailTrace_335653 : CollatzResearch.WordTrace tailWord_335653 prefixEnd_335653 76600587610524662130607 := by
  unfold tailWord_335653
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242270652993980813635613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8161513768662653875757075 12242270652993980813635613)
  ·
    refine ⟨4590851494872742805113355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12242270652993980813635613 4590851494872742805113355)
    ·
      refine ⟨6886277242309114207670033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590851494872742805113355 6886277242309114207670033)
      ·
        refine ⟨5164707931731835655752525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6886277242309114207670033 5164707931731835655752525)
        ·
          refine ⟨1936765474399438370907197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5164707931731835655752525 1936765474399438370907197)
          ·
            refine ⟨726287052899789389090199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936765474399438370907197 726287052899789389090199)
            ·
              refine ⟨1089430579349684083635299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726287052899789389090199 1089430579349684083635299)
              ·
                refine ⟨1634145869024526125452949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089430579349684083635299 1634145869024526125452949)
                ·
                  refine ⟨76600587610524662130607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1634145869024526125452949 76600587610524662130607)
                  ·
                    rfl

theorem cell21_335653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_335653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335653 prefixEnd_335653 := by exact prefixLift 335653
  have htrace : WordTrace (prefixWord ++ tailWord_335653) baseStart_335653 baseEnd_335653 := by
    simpa [prefixWord, tailWord_335653, baseEnd_335653] using wordTrace_append hprefix tailTrace_335653
  have hstable : (prefixWord ++ tailWord_335653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335653).length < 2 ^ (prefixWord ++ tailWord_335653).sum := by decide
  have hdescent : baseEnd_335653 < baseStart_335653 := by decide
  rcases family_descends (prefixWord ++ tailWord_335653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335656 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_335656 : Nat := 118140960795 + 335656 * 2 ^ 59
def prefixEnd_335656 : Nat := 4983230072969 + 3 ^ 40 * 335656 * 2
def baseEnd_335656 : Nat := 76601272251397323580601

theorem tailTrace_335656 : CollatzResearch.WordTrace tailWord_335656 prefixEnd_335656 76601272251397323580601 := by
  unfold tailWord_335656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121190035991556162997411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8161586714655408217329881 6121190035991556162997411)
  ·
    refine ⟨9181785053987334244496117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6121190035991556162997411 9181785053987334244496117)
    ·
      refine ⟨860792348811312585421511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9181785053987334244496117 860792348811312585421511)
      ·
        refine ⟨1291188523216968878132267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860792348811312585421511 1291188523216968878132267)
        ·
          refine ⟨1936782784825453317198401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291188523216968878132267 1936782784825453317198401)
          ·
            refine ⟨1452587088619089987898801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1936782784825453317198401 1452587088619089987898801)
            ·
              refine ⟨1089440316464317490924101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452587088619089987898801 1089440316464317490924101)
              ·
                refine ⟨204270059337059529548269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1089440316464317490924101 204270059337059529548269)
                ·
                  refine ⟨76601272251397323580601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204270059337059529548269 76601272251397323580601)
                  ·
                    rfl

theorem cell21_335656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_335656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335656 prefixEnd_335656 := by exact prefixLift 335656
  have htrace : WordTrace (prefixWord ++ tailWord_335656) baseStart_335656 baseEnd_335656 := by
    simpa [prefixWord, tailWord_335656, baseEnd_335656] using wordTrace_append hprefix tailTrace_335656
  have hstable : (prefixWord ++ tailWord_335656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335656).length < 2 ^ (prefixWord ++ tailWord_335656).sum := by decide
  have hdescent : baseEnd_335656 < baseStart_335656 := by decide
  rcases family_descends (prefixWord ++ tailWord_335656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335729 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_335729 : Nat := 118140960795 + 335729 * 2 ^ 59
def prefixEnd_335729 : Nat := 4983230072969 + 3 ^ 40 * 335729 * 2
def baseEnd_335729 : Nat := 76617931845965418863785

theorem tailTrace_335729 : CollatzResearch.WordTrace tailWord_335729 prefixEnd_335729 76617931845965418863785 := by
  unfold tailWord_335729
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245042600718645793402241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8163361733812430528934827 12245042600718645793402241)
  ·
    refine ⟨9183781950538984345051681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12245042600718645793402241 9183781950538984345051681)
    ·
      refine ⟨6887836462904238258788761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9183781950538984345051681 6887836462904238258788761)
      ·
        refine ⟨5165877347178178694091571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887836462904238258788761 5165877347178178694091571)
        ·
          refine ⟨7748816020767268041137357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165877347178178694091571 7748816020767268041137357)
          ·
            refine ⟨2905806007787725515426509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7748816020767268041137357 2905806007787725515426509)
            ·
              refine ⟨1089677252920397068284941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2905806007787725515426509 1089677252920397068284941)
              ·
                refine ⟨408628969845148900606853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089677252920397068284941 408628969845148900606853)
                ·
                  refine ⟨76617931845965418863785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408628969845148900606853 76617931845965418863785)
                  ·
                    rfl

theorem cell21_335729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_335729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335729 prefixEnd_335729 := by exact prefixLift 335729
  have htrace : WordTrace (prefixWord ++ tailWord_335729) baseStart_335729 baseEnd_335729 := by
    simpa [prefixWord, tailWord_335729, baseEnd_335729] using wordTrace_append hprefix tailTrace_335729
  have hstable : (prefixWord ++ tailWord_335729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335729).length < 2 ^ (prefixWord ++ tailWord_335729).sum := by decide
  have hdescent : baseEnd_335729 < baseStart_335729 := by decide
  rcases family_descends (prefixWord ++ tailWord_335729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335777 : List Nat := [1, 2, 3, 4, 2, 2, 1, 6]
def baseStart_335777 : Nat := 118140960795 + 335777 * 2 ^ 59
def prefixEnd_335777 : Nat := 4983230072969 + 3 ^ 40 * 335777 * 2
def baseEnd_335777 : Nat := 25542962033309334021229

theorem tailTrace_335777 : CollatzResearch.WordTrace tailWord_335777 prefixEnd_335777 25542962033309334021229 := by
  unfold tailWord_335777
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246793304544749991149585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8164528869696499994099723 12246793304544749991149585)
  ·
    refine ⟨9185094978408562493362189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12246793304544749991149585 9185094978408562493362189)
    ·
      refine ⟨3444410616903210935010821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9185094978408562493362189 3444410616903210935010821)
      ·
        refine ⟨645826990669352050314529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3444410616903210935010821 645826990669352050314529)
        ·
          refine ⟨484370243002014037735897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645826990669352050314529 484370243002014037735897)
          ·
            refine ⟨363277682251510528301923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484370243002014037735897 363277682251510528301923)
            ·
              refine ⟨544916523377265792452885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363277682251510528301923 544916523377265792452885)
              ·
                refine ⟨25542962033309334021229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544916523377265792452885 25542962033309334021229)
                ·
                  rfl

theorem cell21_335777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 6].length) (baseStart_335777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335777 prefixEnd_335777 := by exact prefixLift 335777
  have htrace : WordTrace (prefixWord ++ tailWord_335777) baseStart_335777 baseEnd_335777 := by
    simpa [prefixWord, tailWord_335777, baseEnd_335777] using wordTrace_append hprefix tailTrace_335777
  have hstable : (prefixWord ++ tailWord_335777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335777).length < 2 ^ (prefixWord ++ tailWord_335777).sum := by decide
  have hdescent : baseEnd_335777 < baseStart_335777 := by decide
  rcases family_descends (prefixWord ++ tailWord_335777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335850 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_335850 : Nat := 118140960795 + 335850 * 2 ^ 59
def prefixEnd_335850 : Nat := 4983230072969 + 3 ^ 40 * 335850 * 2
def baseEnd_335850 : Nat := 76645545694496097346871

theorem tailTrace_335850 : CollatzResearch.WordTrace tailWord_335850 prefixEnd_335850 76645545694496097346871 := by
  unfold tailWord_335850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062363958320070864639251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8166303888853522305704669 3062363958320070864639251)
  ·
    refine ⟨4593545937480106296958877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3062363958320070864639251 4593545937480106296958877)
    ·
      refine ⟨1722579726555039861359579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4593545937480106296958877 1722579726555039861359579)
      ·
        refine ⟨2583869589832559792039369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722579726555039861359579 2583869589832559792039369)
        ·
          refine ⟨1937902192374419844029527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2583869589832559792039369 1937902192374419844029527)
          ·
            refine ⟨2906853288561629766044291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937902192374419844029527 2906853288561629766044291)
            ·
              refine ⟨4360279932842444649066437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906853288561629766044291 4360279932842444649066437)
              ·
                refine ⟨817552487407958371699957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4360279932842444649066437 817552487407958371699957)
                ·
                  refine ⟨76645545694496097346871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 817552487407958371699957 76645545694496097346871)
                  ·
                    rfl

theorem cell21_335850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_335850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335850 prefixEnd_335850 := by exact prefixLift 335850
  have htrace : WordTrace (prefixWord ++ tailWord_335850) baseStart_335850 baseEnd_335850 := by
    simpa [prefixWord, tailWord_335850, baseEnd_335850] using wordTrace_append hprefix tailTrace_335850
  have hstable : (prefixWord ++ tailWord_335850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335850).length < 2 ^ (prefixWord ++ tailWord_335850).sum := by decide
  have hdescent : baseEnd_335850 < baseStart_335850 := by decide
  rcases family_descends (prefixWord ++ tailWord_335850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335853 : List Nat := [1, 5, 1, 4, 1, 1, 1, 7]
def baseStart_335853 : Nat := 118140960795 + 335853 * 2 ^ 59
def prefixEnd_335853 : Nat := 4983230072969 + 3 ^ 40 * 335853 * 2
def baseEnd_335853 : Nat := 25548743445122919598955

theorem tailTrace_335853 : CollatzResearch.WordTrace tailWord_335853 prefixEnd_335853 25548743445122919598955 := by
  unfold tailWord_335853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12249565252269414970916213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8166376834846276647277475 12249565252269414970916213)
  ·
    refine ⟨1148396742400257653523395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12249565252269414970916213 1148396742400257653523395)
    ·
      refine ⟨1722595113600386480285093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148396742400257653523395 1722595113600386480285093)
      ·
        refine ⟨322986583800072465053455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1722595113600386480285093 322986583800072465053455)
        ·
          refine ⟨484479875700108697580183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322986583800072465053455 484479875700108697580183)
          ·
            refine ⟨726719813550163046370275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484479875700108697580183 726719813550163046370275)
            ·
              refine ⟨1090079720325244569555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726719813550163046370275 1090079720325244569555413)
              ·
                refine ⟨25548743445122919598955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1090079720325244569555413 25548743445122919598955)
                ·
                  rfl

theorem cell21_335853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 7].length) (baseStart_335853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335853 prefixEnd_335853 := by exact prefixLift 335853
  have htrace : WordTrace (prefixWord ++ tailWord_335853) baseStart_335853 baseEnd_335853 := by
    simpa [prefixWord, tailWord_335853, baseEnd_335853] using wordTrace_append hprefix tailTrace_335853
  have hstable : (prefixWord ++ tailWord_335853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335853).length < 2 ^ (prefixWord ++ tailWord_335853).sum := by decide
  have hdescent : baseEnd_335853 < baseStart_335853 := by decide
  rcases family_descends (prefixWord ++ tailWord_335853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335864 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_335864 : Nat := 118140960795 + 335864 * 2 ^ 59
def prefixEnd_335864 : Nat := 4983230072969 + 3 ^ 40 * 335864 * 2
def baseEnd_335864 : Nat := 76648740685235184113509

theorem tailTrace_335864 : CollatzResearch.WordTrace tailWord_335864 prefixEnd_335864 76648740685235184113509 := by
  unfold tailWord_335864
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124983227614781924783323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8166644303486375899711097 6124983227614781924783323)
  ·
    refine ⟨9187474841422172887174985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124983227614781924783323 9187474841422172887174985)
    ·
      refine ⟨6890606131066629665381239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9187474841422172887174985 6890606131066629665381239)
      ·
        refine ⟨10335909196599944498071859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890606131066629665381239 10335909196599944498071859)
        ·
          refine ⟨15503863794899916747107789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335909196599944498071859 15503863794899916747107789)
          ·
            refine ⟨5813948923087468780165421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15503863794899916747107789 5813948923087468780165421)
            ·
              refine ⟨2180230846157800792562033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5813948923087468780165421 2180230846157800792562033)
              ·
                refine ⟨1635173134618350594421525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180230846157800792562033 1635173134618350594421525)
                ·
                  refine ⟨76648740685235184113509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1635173134618350594421525 76648740685235184113509)
                  ·
                    rfl

theorem cell21_335864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_335864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335864 prefixEnd_335864 := by exact prefixLift 335864
  have htrace : WordTrace (prefixWord ++ tailWord_335864) baseStart_335864 baseEnd_335864 := by
    simpa [prefixWord, tailWord_335864, baseEnd_335864] using wordTrace_append hprefix tailTrace_335864
  have hstable : (prefixWord ++ tailWord_335864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335864).length < 2 ^ (prefixWord ++ tailWord_335864).sum := by decide
  have hdescent : baseEnd_335864 < baseStart_335864 := by decide
  rcases family_descends (prefixWord ++ tailWord_335864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335867 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 3]
def baseStart_335867 : Nat := 118140960795 + 335867 * 2 ^ 59
def prefixEnd_335867 : Nat := 4983230072969 + 3 ^ 40 * 335867 * 2
def baseEnd_335867 : Nat := 76649425326107845563503

theorem tailTrace_335867 : CollatzResearch.WordTrace tailWord_335867 prefixEnd_335867 76649425326107845563503 := by
  unfold tailWord_335867
  simp only [CollatzResearch.WordTrace]
  refine ⟨12250075874218695361925855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8166717249479130241283903 12250075874218695361925855)
  ·
    refine ⟨18375113811328043042888783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12250075874218695361925855 18375113811328043042888783)
    ·
      refine ⟨27562670716992064564333175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18375113811328043042888783 27562670716992064564333175)
      ·
        refine ⟨41344006075488096846499763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27562670716992064564333175 41344006075488096846499763)
        ·
          refine ⟨62016009113232145269749645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41344006075488096846499763 62016009113232145269749645)
          ·
            refine ⟨23256003417462054476156117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62016009113232145269749645 23256003417462054476156117)
            ·
              refine ⟨545062580096766901784909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23256003417462054476156117 545062580096766901784909)
              ·
                refine ⟨204398467536287588169341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545062580096766901784909 204398467536287588169341)
                ·
                  refine ⟨76649425326107845563503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204398467536287588169341 76649425326107845563503)
                  ·
                    rfl

theorem cell21_335867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 3].length) (baseStart_335867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335867 prefixEnd_335867 := by exact prefixLift 335867
  have htrace : WordTrace (prefixWord ++ tailWord_335867) baseStart_335867 baseEnd_335867 := by
    simpa [prefixWord, tailWord_335867, baseEnd_335867] using wordTrace_append hprefix tailTrace_335867
  have hstable : (prefixWord ++ tailWord_335867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335867).length < 2 ^ (prefixWord ++ tailWord_335867).sum := by decide
  have hdescent : baseEnd_335867 < baseStart_335867 := by decide
  rcases family_descends (prefixWord ++ tailWord_335867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335884 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_335884 : Nat := 118140960795 + 335884 * 2 ^ 59
def prefixEnd_335884 : Nat := 4983230072969 + 3 ^ 40 * 335884 * 2
def baseEnd_335884 : Nat := 76653304957719593780135

theorem tailTrace_335884 : CollatzResearch.WordTrace tailWord_335884 prefixEnd_335884 76653304957719593780135 := by
  unfold tailWord_335884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125347957578553632647353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8167130610104738176863137 6125347957578553632647353)
  ·
    refine ⟨4594010968183915224485515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6125347957578553632647353 4594010968183915224485515)
    ·
      refine ⟨6891016452275872836728273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4594010968183915224485515 6891016452275872836728273)
      ·
        refine ⟨5168262339206904627546205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6891016452275872836728273 5168262339206904627546205)
        ·
          refine ⟨1938098377202589235329827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5168262339206904627546205 1938098377202589235329827)
          ·
            refine ⟨2907147565803883852994741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938098377202589235329827 2907147565803883852994741)
            ·
              refine ⟨272545084294114111218257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2907147565803883852994741 272545084294114111218257)
              ·
                refine ⟨204408813220585583413693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272545084294114111218257 204408813220585583413693)
                ·
                  refine ⟨76653304957719593780135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204408813220585583413693 76653304957719593780135)
                  ·
                    rfl

theorem cell21_335884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_335884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335884 prefixEnd_335884 := by exact prefixLift 335884
  have htrace : WordTrace (prefixWord ++ tailWord_335884) baseStart_335884 baseEnd_335884 := by
    simpa [prefixWord, tailWord_335884, baseEnd_335884] using wordTrace_append hprefix tailTrace_335884
  have hstable : (prefixWord ++ tailWord_335884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335884).length < 2 ^ (prefixWord ++ tailWord_335884).sum := by decide
  have hdescent : baseEnd_335884 < baseStart_335884 := by decide
  rcases family_descends (prefixWord ++ tailWord_335884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335898 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_335898 : Nat := 118140960795 + 335898 * 2 ^ 59
def prefixEnd_335898 : Nat := 4983230072969 + 3 ^ 40 * 335898 * 2
def baseEnd_335898 : Nat := 76656499948458680546773

theorem tailTrace_335898 : CollatzResearch.WordTrace tailWord_335898 prefixEnd_335898 76656499948458680546773 := by
  unfold tailWord_335898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062801634276596914076087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8167471024737591770869565 3062801634276596914076087)
  ·
    refine ⟨4594202451414895371114131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3062801634276596914076087 4594202451414895371114131)
    ·
      refine ⟨6891303677122343056671197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4594202451414895371114131 6891303677122343056671197)
      ·
        refine ⟨2584238878920878646251699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6891303677122343056671197 2584238878920878646251699)
        ·
          refine ⟨3876358318381317969377549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584238878920878646251699 3876358318381317969377549)
          ·
            refine ⟨1453634369392994238516581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3876358318381317969377549 1453634369392994238516581)
            ·
              refine ⟨272556444261186419721859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1453634369392994238516581 272556444261186419721859)
              ·
                refine ⟨408834666391779629582789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272556444261186419721859 408834666391779629582789)
                ·
                  refine ⟨76656499948458680546773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408834666391779629582789 76656499948458680546773)
                  ·
                    rfl

theorem cell21_335898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_335898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335898 prefixEnd_335898 := by exact prefixLift 335898
  have htrace : WordTrace (prefixWord ++ tailWord_335898) baseStart_335898 baseEnd_335898 := by
    simpa [prefixWord, tailWord_335898, baseEnd_335898] using wordTrace_append hprefix tailTrace_335898
  have hstable : (prefixWord ++ tailWord_335898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335898).length < 2 ^ (prefixWord ++ tailWord_335898).sum := by decide
  have hdescent : baseEnd_335898 < baseStart_335898 := by decide
  rcases family_descends (prefixWord ++ tailWord_335898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335943 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 3]
def baseStart_335943 : Nat := 118140960795 + 335943 * 2 ^ 59
def prefixEnd_335943 : Nat := 4983230072969 + 3 ^ 40 * 335943 * 2
def baseEnd_335943 : Nat := 76666769561548602296681

theorem tailTrace_335943 : CollatzResearch.WordTrace tailWord_335943 prefixEnd_335943 76666769561548602296681 := by
  unfold tailWord_335943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12252847821943360341692483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8168565214628906894461655 12252847821943360341692483)
  ·
    refine ⟨18379271732915040512538725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12252847821943360341692483 18379271732915040512538725)
    ·
      refine ⟨3446113449921570096101011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18379271732915040512538725 3446113449921570096101011)
      ·
        refine ⟨5169170174882355144151517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446113449921570096101011 5169170174882355144151517)
        ·
          refine ⟨1938438815580883179056819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5169170174882355144151517 1938438815580883179056819)
          ·
            refine ⟨2907658223371324768585229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938438815580883179056819 2907658223371324768585229)
            ·
              refine ⟨1090371833764246788219461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2907658223371324768585229 1090371833764246788219461)
              ·
                refine ⟨204444718830796272791149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1090371833764246788219461 204444718830796272791149)
                ·
                  refine ⟨76666769561548602296681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204444718830796272791149 76666769561548602296681)
                  ·
                    rfl

theorem cell21_335943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 3].length) (baseStart_335943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335943 prefixEnd_335943 := by exact prefixLift 335943
  have htrace : WordTrace (prefixWord ++ tailWord_335943) baseStart_335943 baseEnd_335943 := by
    simpa [prefixWord, tailWord_335943, baseEnd_335943] using wordTrace_append hprefix tailTrace_335943
  have hstable : (prefixWord ++ tailWord_335943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335943).length < 2 ^ (prefixWord ++ tailWord_335943).sum := by decide
  have hdescent : baseEnd_335943 < baseStart_335943 := by decide
  rcases family_descends (prefixWord ++ tailWord_335943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335957 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_335957 : Nat := 118140960795 + 335957 * 2 ^ 59
def prefixEnd_335957 : Nat := 4983230072969 + 3 ^ 40 * 335957 * 2
def baseEnd_335957 : Nat := 76669964552287689063319

theorem tailTrace_335957 : CollatzResearch.WordTrace tailWord_335957 prefixEnd_335957 76669964552287689063319 := by
  unfold tailWord_335957
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253358443892640732702125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8168905629261760488468083 12253358443892640732702125)
  ·
    refine ⟨4595009416459740274763297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12253358443892640732702125 4595009416459740274763297)
    ·
      refine ⟨3446257062344805206072473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4595009416459740274763297 3446257062344805206072473)
      ·
        refine ⟨2584692796758603904554355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3446257062344805206072473 2584692796758603904554355)
        ·
          refine ⟨3877039195137905856831533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584692796758603904554355 3877039195137905856831533)
          ·
            refine ⟨1453889698176714696311825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3877039195137905856831533 1453889698176714696311825)
            ·
              refine ⟨1090417273632536022233869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453889698176714696311825 1090417273632536022233869)
              ·
                refine ⟨408906477612201008337701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1090417273632536022233869 408906477612201008337701)
                ·
                  refine ⟨76669964552287689063319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408906477612201008337701 76669964552287689063319)
                  ·
                    rfl

theorem cell21_335957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_335957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335957 prefixEnd_335957 := by exact prefixLift 335957
  have htrace : WordTrace (prefixWord ++ tailWord_335957) baseStart_335957 baseEnd_335957 := by
    simpa [prefixWord, tailWord_335957, baseEnd_335957] using wordTrace_append hprefix tailTrace_335957
  have hstable : (prefixWord ++ tailWord_335957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335957).length < 2 ^ (prefixWord ++ tailWord_335957).sum := by decide
  have hdescent : baseEnd_335957 < baseStart_335957 := by decide
  rcases family_descends (prefixWord ++ tailWord_335957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335985 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_335985 : Nat := 118140960795 + 335985 * 2 ^ 59
def prefixEnd_335985 : Nat := 4983230072969 + 3 ^ 40 * 335985 * 2
def baseEnd_335985 : Nat := 76676354533765862596595

theorem tailTrace_335985 : CollatzResearch.WordTrace tailWord_335985 prefixEnd_335985 76676354533765862596595 := by
  unfold tailWord_335985
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254379687791201514721409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8169586458527467676480939 12254379687791201514721409)
  ·
    refine ⟨9190784765843401136041057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254379687791201514721409 9190784765843401136041057)
    ·
      refine ⟨6893088574382550852030793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9190784765843401136041057 6893088574382550852030793)
      ·
        refine ⟨5169816430786913139023095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6893088574382550852030793 5169816430786913139023095)
        ·
          refine ⟨7754724646180369708534643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169816430786913139023095 7754724646180369708534643)
          ·
            refine ⟨11632086969270554562801965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754724646180369708534643 11632086969270554562801965)
            ·
              refine ⟨4362032613476457961050737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11632086969270554562801965 4362032613476457961050737)
              ·
                refine ⟨3271524460107343470788053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4362032613476457961050737 3271524460107343470788053)
                ·
                  refine ⟨76676354533765862596595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3271524460107343470788053 76676354533765862596595)
                  ·
                    rfl

theorem cell21_335985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_335985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_335985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_335985 prefixEnd_335985 := by exact prefixLift 335985
  have htrace : WordTrace (prefixWord ++ tailWord_335985) baseStart_335985 baseEnd_335985 := by
    simpa [prefixWord, tailWord_335985, baseEnd_335985] using wordTrace_append hprefix tailTrace_335985
  have hstable : (prefixWord ++ tailWord_335985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335985).length < 2 ^ (prefixWord ++ tailWord_335985).sum := by decide
  have hdescent : baseEnd_335985 < baseStart_335985 := by decide
  rcases family_descends (prefixWord ++ tailWord_335985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336053 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 5]
def baseStart_336053 : Nat := 118140960795 + 336053 * 2 ^ 59
def prefixEnd_336053 : Nat := 4983230072969 + 3 ^ 40 * 336053 * 2
def baseEnd_336053 : Nat := 76691873060212855463123

theorem tailTrace_336053 : CollatzResearch.WordTrace tailWord_336053 prefixEnd_336053 76691873060212855463123 := by
  unfold tailWord_336053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256859851544849128196813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8171239901029899418797875 12256859851544849128196813)
  ·
    refine ⟨4596322444329318423073805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12256859851544849128196813 4596322444329318423073805)
    ·
      refine ⟨1723620916623494408652677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4596322444329318423073805 1723620916623494408652677)
      ·
        refine ⟨323178921866905201622377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1723620916623494408652677 323178921866905201622377)
        ·
          refine ⟨242384191400178901216783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323178921866905201622377 242384191400178901216783)
          ·
            refine ⟨363576287100268351825175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242384191400178901216783 363576287100268351825175)
            ·
              refine ⟨545364430650402527737763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363576287100268351825175 545364430650402527737763)
              ·
                refine ⟨818046645975603791606645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545364430650402527737763 818046645975603791606645)
                ·
                  refine ⟨76691873060212855463123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 818046645975603791606645 76691873060212855463123)
                  ·
                    rfl

theorem cell21_336053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_336053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336053 prefixEnd_336053 := by exact prefixLift 336053
  have htrace : WordTrace (prefixWord ++ tailWord_336053) baseStart_336053 baseEnd_336053 := by
    simpa [prefixWord, tailWord_336053, baseEnd_336053] using wordTrace_append hprefix tailTrace_336053
  have hstable : (prefixWord ++ tailWord_336053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336053).length < 2 ^ (prefixWord ++ tailWord_336053).sum := by decide
  have hdescent : baseEnd_336053 < baseStart_336053 := by decide
  rcases family_descends (prefixWord ++ tailWord_336053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336098 : List Nat := [3, 3, 4, 1, 2, 8]
def baseStart_336098 : Nat := 118140960795 + 336098 * 2 ^ 59
def prefixEnd_336098 : Nat := 4983230072969 + 3 ^ 40 * 336098 * 2
def baseEnd_336098 : Nat := 2840820099011213970853

theorem tailTrace_336098 : CollatzResearch.WordTrace tailWord_336098 prefixEnd_336098 2840820099011213970853 := by
  unfold tailWord_336098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064625284095455453396237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8172334090921214542389965 3064625284095455453396237)
  ·
    refine ⟨1149234481535795795023589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3064625284095455453396237 1149234481535795795023589)
    ·
      refine ⟨215481465287961711566923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1149234481535795795023589 215481465287961711566923)
      ·
        refine ⟨323222197931942567350385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215481465287961711566923 323222197931942567350385)
        ·
          refine ⟨242416648448956925512789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323222197931942567350385 242416648448956925512789)
          ·
            refine ⟨2840820099011213970853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 242416648448956925512789 2840820099011213970853)
            ·
              rfl

theorem cell21_336098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 8].length) (baseStart_336098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336098 prefixEnd_336098 := by exact prefixLift 336098
  have htrace : WordTrace (prefixWord ++ tailWord_336098) baseStart_336098 baseEnd_336098 := by
    simpa [prefixWord, tailWord_336098, baseEnd_336098] using wordTrace_append hprefix tailTrace_336098
  have hstable : (prefixWord ++ tailWord_336098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336098).length < 2 ^ (prefixWord ++ tailWord_336098).sum := by decide
  have hdescent : baseEnd_336098 < baseStart_336098 := by decide
  rcases family_descends (prefixWord ++ tailWord_336098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336137 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_336137 : Nat := 118140960795 + 336137 * 2 ^ 59
def prefixEnd_336137 : Nat := 4983230072969 + 3 ^ 40 * 336137 * 2
def baseEnd_336137 : Nat := 76711043004647376062951

theorem tailTrace_336137 : CollatzResearch.WordTrace tailWord_336137 prefixEnd_336137 76711043004647376062951 := by
  unfold tailWord_336137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259923583240531474254665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8173282388827020982836443 12259923583240531474254665)
  ·
    refine ⟨9194942687430398605690999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12259923583240531474254665 9194942687430398605690999)
    ·
      refine ⟨13792414031145597908536499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194942687430398605690999 13792414031145597908536499)
      ·
        refine ⟨20688621046718396862804749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13792414031145597908536499 20688621046718396862804749)
        ·
          refine ⟨7758232892519398823551781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20688621046718396862804749 7758232892519398823551781)
          ·
            refine ⟨1454668667347387279415959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7758232892519398823551781 1454668667347387279415959)
            ·
              refine ⟨2182003001021080919123939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454668667347387279415959 2182003001021080919123939)
              ·
                refine ⟨3273004501531621378685909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182003001021080919123939 3273004501531621378685909)
                ·
                  refine ⟨76711043004647376062951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3273004501531621378685909 76711043004647376062951)
                  ·
                    rfl

theorem cell21_336137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_336137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336137 prefixEnd_336137 := by exact prefixLift 336137
  have htrace : WordTrace (prefixWord ++ tailWord_336137) baseStart_336137 baseEnd_336137 := by
    simpa [prefixWord, tailWord_336137, baseEnd_336137] using wordTrace_append hprefix tailTrace_336137
  have hstable : (prefixWord ++ tailWord_336137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336137).length < 2 ^ (prefixWord ++ tailWord_336137).sum := by decide
  have hdescent : baseEnd_336137 < baseStart_336137 := by decide
  rcases family_descends (prefixWord ++ tailWord_336137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336303 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_336303 : Nat := 118140960795 + 336303 * 2 ^ 59
def prefixEnd_336303 : Nat := 4983230072969 + 3 ^ 40 * 336303 * 2
def baseEnd_336303 : Nat := 76748926466267976295945

theorem tailTrace_336303 : CollatzResearch.WordTrace tailWord_336303 prefixEnd_336303 76748926466267976295945 := by
  unfold tailWord_336303
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265978100639141824797563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8177318733759427883198375 12265978100639141824797563)
  ·
    refine ⟨18398967150958712737196345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12265978100639141824797563 18398967150958712737196345)
    ·
      refine ⟨13799225363219034552897259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18398967150958712737196345 13799225363219034552897259)
      ·
        refine ⟨20698838044828551829345889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13799225363219034552897259 20698838044828551829345889)
        ·
          refine ⟨15524128533621413872009417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20698838044828551829345889 15524128533621413872009417)
          ·
            refine ⟨11643096400216060404007063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15524128533621413872009417 11643096400216060404007063)
            ·
              refine ⟨17464644600324090606010595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11643096400216060404007063 17464644600324090606010595)
              ·
                refine ⟨26196966900486135909015893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17464644600324090606010595 26196966900486135909015893)
                ·
                  refine ⟨76748926466267976295945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26196966900486135909015893 76748926466267976295945)
                  ·
                    rfl

theorem cell21_336303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_336303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336303 prefixEnd_336303 := by exact prefixLift 336303
  have htrace : WordTrace (prefixWord ++ tailWord_336303) baseStart_336303 baseEnd_336303 := by
    simpa [prefixWord, tailWord_336303, baseEnd_336303] using wordTrace_append hprefix tailTrace_336303
  have hstable : (prefixWord ++ tailWord_336303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336303).length < 2 ^ (prefixWord ++ tailWord_336303).sum := by decide
  have hdescent : baseEnd_336303 < baseStart_336303 := by decide
  rcases family_descends (prefixWord ++ tailWord_336303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336396 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_336396 : Nat := 118140960795 + 336396 * 2 ^ 59
def prefixEnd_336396 : Nat := 4983230072969 + 3 ^ 40 * 336396 * 2
def baseEnd_336396 : Nat := 76770150333320481245755

theorem tailTrace_336396 : CollatzResearch.WordTrace tailWord_336396 prefixEnd_336396 76770150333320481245755 := by
  unfold tailWord_336396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134685044651109353966521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8179580059534812471955361 6134685044651109353966521)
  ·
    refine ⟨4601013783488332015474891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6134685044651109353966521 4601013783488332015474891)
    ·
      refine ⟨6901520675232498023212337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601013783488332015474891 6901520675232498023212337)
      ·
        refine ⟨5176140506424373517409253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6901520675232498023212337 5176140506424373517409253)
        ·
          refine ⟨970526344954570034514235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5176140506424373517409253 970526344954570034514235)
          ·
            refine ⟨1455789517431855051771353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970526344954570034514235 1455789517431855051771353)
            ·
              refine ⟨1091842138073891288828515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455789517431855051771353 1091842138073891288828515)
              ·
                refine ⟨1637763207110836933242773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091842138073891288828515 1637763207110836933242773)
                ·
                  refine ⟨76770150333320481245755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1637763207110836933242773 76770150333320481245755)
                  ·
                    rfl

theorem cell21_336396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_336396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336396 prefixEnd_336396 := by exact prefixLift 336396
  have htrace : WordTrace (prefixWord ++ tailWord_336396) baseStart_336396 baseEnd_336396 := by
    simpa [prefixWord, tailWord_336396, baseEnd_336396] using wordTrace_append hprefix tailTrace_336396
  have hstable : (prefixWord ++ tailWord_336396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336396).length < 2 ^ (prefixWord ++ tailWord_336396).sum := by decide
  have hdescent : baseEnd_336396 < baseStart_336396 := by decide
  rcases family_descends (prefixWord ++ tailWord_336396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336410 : List Nat := [3, 1, 1, 3, 1, 1, 3, 8]
def baseStart_336410 : Nat := 118140960795 + 336410 * 2 ^ 59
def prefixEnd_336410 : Nat := 4983230072969 + 3 ^ 40 * 336410 * 2
def baseEnd_336410 : Nat := 25591115108019856004131

theorem tailTrace_336410 : CollatzResearch.WordTrace tailWord_336410 prefixEnd_336410 25591115108019856004131 := by
  unfold tailWord_336410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067470177812874774735671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8179920474167666065961789 3067470177812874774735671)
  ·
    refine ⟨4601205266719312162103507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3067470177812874774735671 4601205266719312162103507)
    ·
      refine ⟨6901807900078968243155261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601205266719312162103507 6901807900078968243155261)
      ·
        refine ⟨2588177962529613091183223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6901807900078968243155261 2588177962529613091183223)
        ·
          refine ⟨3882266943794419636774835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588177962529613091183223 3882266943794419636774835)
          ·
            refine ⟨5823400415691629455162253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882266943794419636774835 5823400415691629455162253)
            ·
              refine ⟨2183775155884361045685845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5823400415691629455162253 2183775155884361045685845)
              ·
                refine ⟨25591115108019856004131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2183775155884361045685845 25591115108019856004131)
                ·
                  rfl

theorem cell21_336410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_336410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336410 prefixEnd_336410 := by exact prefixLift 336410
  have htrace : WordTrace (prefixWord ++ tailWord_336410) baseStart_336410 baseEnd_336410 := by
    simpa [prefixWord, tailWord_336410, baseEnd_336410] using wordTrace_append hprefix tailTrace_336410
  have hstable : (prefixWord ++ tailWord_336410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336410).length < 2 ^ (prefixWord ++ tailWord_336410).sum := by decide
  have hdescent : baseEnd_336410 < baseStart_336410 := by decide
  rcases family_descends (prefixWord ++ tailWord_336410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336413 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_336413 : Nat := 118140960795 + 336413 * 2 ^ 59
def prefixEnd_336413 : Nat := 4983230072969 + 3 ^ 40 * 336413 * 2
def baseEnd_336413 : Nat := 76774029964932229462387

theorem tailTrace_336413 : CollatzResearch.WordTrace tailWord_336413 prefixEnd_336413 76774029964932229462387 := by
  unfold tailWord_336413
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269990130240630611301893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8179993420160420407534595 12269990130240630611301893)
  ·
    refine ⟨2300623149420118239619105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12269990130240630611301893 2300623149420118239619105)
    ·
      refine ⟨1725467362065088679714329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300623149420118239619105 1725467362065088679714329)
      ·
        refine ⟨1294100521548816509785747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725467362065088679714329 1294100521548816509785747)
        ·
          refine ⟨1941150782323224764678621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294100521548816509785747 1941150782323224764678621)
          ·
            refine ⟨727931543371209286754483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1941150782323224764678621 727931543371209286754483)
            ·
              refine ⟨1091897315056813930131725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727931543371209286754483 1091897315056813930131725)
              ·
                refine ⟨409461493146305223799397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091897315056813930131725 409461493146305223799397)
                ·
                  refine ⟨76774029964932229462387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409461493146305223799397 76774029964932229462387)
                  ·
                    rfl

theorem cell21_336413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_336413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336413 prefixEnd_336413 := by exact prefixLift 336413
  have htrace : WordTrace (prefixWord ++ tailWord_336413) baseStart_336413 baseEnd_336413 := by
    simpa [prefixWord, tailWord_336413, baseEnd_336413] using wordTrace_append hprefix tailTrace_336413
  have hstable : (prefixWord ++ tailWord_336413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336413).length < 2 ^ (prefixWord ++ tailWord_336413).sum := by decide
  have hdescent : baseEnd_336413 < baseStart_336413 := by decide
  rcases family_descends (prefixWord ++ tailWord_336413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336472 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_336472 : Nat := 118140960795 + 336472 * 2 ^ 59
def prefixEnd_336472 : Nat := 4983230072969 + 3 ^ 40 * 336472 * 2
def baseEnd_336472 : Nat := 76787494568761237978933

theorem tailTrace_336472 : CollatzResearch.WordTrace tailWord_336472 prefixEnd_336472 76787494568761237978933 := by
  unfold tailWord_336472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136071018513441843849835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8181428024684589125133113 6136071018513441843849835)
  ·
    refine ⟨9204106527770162765774753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6136071018513441843849835 9204106527770162765774753)
    ·
      refine ⟨6903079895827622074331065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9204106527770162765774753 6903079895827622074331065)
      ·
        refine ⟨5177309921870716555748299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6903079895827622074331065 5177309921870716555748299)
        ·
          refine ⟨7765964882806074833622449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177309921870716555748299 7765964882806074833622449)
          ·
            refine ⟨5824473662104556125216837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7765964882806074833622449 5824473662104556125216837)
            ·
              refine ⟨1092088811644604273478157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5824473662104556125216837 1092088811644604273478157)
              ·
                refine ⟨409533304366726602554309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1092088811644604273478157 409533304366726602554309)
                ·
                  refine ⟨76787494568761237978933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409533304366726602554309 76787494568761237978933)
                  ·
                    rfl

theorem cell21_336472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_336472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336472 prefixEnd_336472 := by exact prefixLift 336472
  have htrace : WordTrace (prefixWord ++ tailWord_336472) baseStart_336472 baseEnd_336472 := by
    simpa [prefixWord, tailWord_336472, baseEnd_336472] using wordTrace_append hprefix tailTrace_336472
  have hstable : (prefixWord ++ tailWord_336472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336472).length < 2 ^ (prefixWord ++ tailWord_336472).sum := by decide
  have hdescent : baseEnd_336472 < baseStart_336472 := by decide
  rcases family_descends (prefixWord ++ tailWord_336472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336517 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_336517 : Nat := 118140960795 + 336517 * 2 ^ 59
def prefixEnd_336517 : Nat := 4983230072969 + 3 ^ 40 * 336517 * 2
def baseEnd_336517 : Nat := 76797764181851159728841

theorem tailTrace_336517 : CollatzResearch.WordTrace tailWord_336517 prefixEnd_336517 76797764181851159728841 := by
  unfold tailWord_336517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273783321863856373087805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8182522214575904248725203 12273783321863856373087805)
  ·
    refine ⟨4602668745698946139907927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12273783321863856373087805 4602668745698946139907927)
    ·
      refine ⟨6904003118548419209861891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4602668745698946139907927 6904003118548419209861891)
      ·
        refine ⟨10356004677822628814792837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6904003118548419209861891 10356004677822628814792837)
        ·
          refine ⟨1941750877091742902773657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10356004677822628814792837 1941750877091742902773657)
          ·
            refine ⟨1456313157818807177080243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941750877091742902773657 1456313157818807177080243)
            ·
              refine ⟨2184469736728210765620365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456313157818807177080243 2184469736728210765620365)
              ·
                refine ⟨819176151273079037107637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184469736728210765620365 819176151273079037107637)
                ·
                  refine ⟨76797764181851159728841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 819176151273079037107637 76797764181851159728841)
                  ·
                    rfl

theorem cell21_336517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_336517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336517 prefixEnd_336517 := by exact prefixLift 336517
  have htrace : WordTrace (prefixWord ++ tailWord_336517) baseStart_336517 baseEnd_336517 := by
    simpa [prefixWord, tailWord_336517, baseEnd_336517] using wordTrace_append hprefix tailTrace_336517
  have hstable : (prefixWord ++ tailWord_336517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336517).length < 2 ^ (prefixWord ++ tailWord_336517).sum := by decide
  have hdescent : baseEnd_336517 < baseStart_336517 := by decide
  rcases family_descends (prefixWord ++ tailWord_336517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336624 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_336624 : Nat := 118140960795 + 336624 * 2 ^ 59
def prefixEnd_336624 : Nat := 4983230072969 + 3 ^ 40 * 336624 * 2
def baseEnd_336624 : Nat := 76822183039642751445289

theorem tailTrace_336624 : CollatzResearch.WordTrace tailWord_336624 prefixEnd_336624 76822183039642751445289 := by
  unfold tailWord_336624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138842966238106823616463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8185123954984142431488617 6138842966238106823616463)
  ·
    refine ⟨9208264449357160235424695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138842966238106823616463 9208264449357160235424695)
    ·
      refine ⟨13812396674035740353137043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208264449357160235424695 13812396674035740353137043)
      ·
        refine ⟨20718595011053610529705565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13812396674035740353137043 20718595011053610529705565)
        ·
          refine ⟨7769473129145103948639587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20718595011053610529705565 7769473129145103948639587)
          ·
            refine ⟨11654209693717655922959381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7769473129145103948639587 11654209693717655922959381)
            ·
              refine ⟨546291079393015121388721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11654209693717655922959381 546291079393015121388721)
              ·
                refine ⟨409718309544761341041541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546291079393015121388721 409718309544761341041541)
                ·
                  refine ⟨76822183039642751445289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409718309544761341041541 76822183039642751445289)
                  ·
                    rfl

theorem cell21_336624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_336624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336624 prefixEnd_336624 := by exact prefixLift 336624
  have htrace : WordTrace (prefixWord ++ tailWord_336624) baseStart_336624 baseEnd_336624 := by
    simpa [prefixWord, tailWord_336624, baseEnd_336624] using wordTrace_append hprefix tailTrace_336624
  have hstable : (prefixWord ++ tailWord_336624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336624).length < 2 ^ (prefixWord ++ tailWord_336624).sum := by decide
  have hdescent : baseEnd_336624 < baseStart_336624 := by decide
  rcases family_descends (prefixWord ++ tailWord_336624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336686 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_336686 : Nat := 118140960795 + 336686 * 2 ^ 59
def prefixEnd_336686 : Nat := 4983230072969 + 3 ^ 40 * 336686 * 2
def baseEnd_336686 : Nat := 76836332284344421411829

theorem tailTrace_336686 : CollatzResearch.WordTrace tailWord_336686 prefixEnd_336686 76836332284344421411829 := by
  unfold tailWord_336686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534993407281449779498739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8186631505501065490659941 1534993407281449779498739)
  ·
    refine ⟨2302490110922174669248109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534993407281449779498739 2302490110922174669248109)
    ·
      refine ⟨863433791595815500968041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2302490110922174669248109 863433791595815500968041)
      ·
        refine ⟨647575343696861625726031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 863433791595815500968041 647575343696861625726031)
        ·
          refine ⟨971363015545292438589047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647575343696861625726031 971363015545292438589047)
          ·
            refine ⟨1457044523317938657883571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971363015545292438589047 1457044523317938657883571)
            ·
              refine ⟨2185566784976907986825357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457044523317938657883571 2185566784976907986825357)
              ·
                refine ⟨819587544366340495059509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185566784976907986825357 819587544366340495059509)
                ·
                  refine ⟨76836332284344421411829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 819587544366340495059509 76836332284344421411829)
                  ·
                    rfl

theorem cell21_336686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_336686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336686 prefixEnd_336686 := by exact prefixLift 336686
  have htrace : WordTrace (prefixWord ++ tailWord_336686) baseStart_336686 baseEnd_336686 := by
    simpa [prefixWord, tailWord_336686, baseEnd_336686] using wordTrace_append hprefix tailTrace_336686
  have hstable : (prefixWord ++ tailWord_336686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336686).length < 2 ^ (prefixWord ++ tailWord_336686).sum := by decide
  have hdescent : baseEnd_336686 < baseStart_336686 := by decide
  rcases family_descends (prefixWord ++ tailWord_336686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336728 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_336728 : Nat := 118140960795 + 336728 * 2 ^ 59
def prefixEnd_336728 : Nat := 4983230072969 + 3 ^ 40 * 336728 * 2
def baseEnd_336728 : Nat := 76845917256561681711743

theorem tailTrace_336728 : CollatzResearch.WordTrace tailWord_336728 prefixEnd_336728 76845917256561681711743 := by
  unfold tailWord_336728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140739562049719704509419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8187652749399626272679225 6140739562049719704509419)
  ·
    refine ⟨9211109343074579556764129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6140739562049719704509419 9211109343074579556764129)
    ·
      refine ⟨6908332007305934667573097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9211109343074579556764129 6908332007305934667573097)
      ·
        refine ⟨5181249005479451000679823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6908332007305934667573097 5181249005479451000679823)
        ·
          refine ⟨7771873508219176501019735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181249005479451000679823 7771873508219176501019735)
          ·
            refine ⟨11657810262328764751529603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771873508219176501019735 11657810262328764751529603)
            ·
              refine ⟨17486715393493147127294405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657810262328764751529603 17486715393493147127294405)
              ·
                refine ⟨3278759136279965086367701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17486715393493147127294405 3278759136279965086367701)
                ·
                  refine ⟨76845917256561681711743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3278759136279965086367701 76845917256561681711743)
                  ·
                    rfl

theorem cell21_336728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_336728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336728 prefixEnd_336728 := by exact prefixLift 336728
  have htrace : WordTrace (prefixWord ++ tailWord_336728) baseStart_336728 baseEnd_336728 := by
    simpa [prefixWord, tailWord_336728, baseEnd_336728] using wordTrace_append hprefix tailTrace_336728
  have hstable : (prefixWord ++ tailWord_336728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336728).length < 2 ^ (prefixWord ++ tailWord_336728).sum := by decide
  have hdescent : baseEnd_336728 < baseStart_336728 := by decide
  rcases family_descends (prefixWord ++ tailWord_336728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336821 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_336821 : Nat := 118140960795 + 336821 * 2 ^ 59
def prefixEnd_336821 : Nat := 4983230072969 + 3 ^ 40 * 336821 * 2
def baseEnd_336821 : Nat := 76867141123614186661553

theorem tailTrace_336821 : CollatzResearch.WordTrace tailWord_336821 prefixEnd_336821 76867141123614186661553 := by
  unfold tailWord_336821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12284871112762516292154317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8189914075175010861436211 12284871112762516292154317)
  ·
    refine ⟨4606826667285943609557869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12284871112762516292154317 4606826667285943609557869)
    ·
      refine ⟨1727560000232228853584201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4606826667285943609557869 1727560000232228853584201)
      ·
        refine ⟨1295670000174171640188151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727560000232228853584201 1295670000174171640188151)
        ·
          refine ⟨1943505000261257460282227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295670000174171640188151 1943505000261257460282227)
          ·
            refine ⟨2915257500391886190423341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943505000261257460282227 2915257500391886190423341)
            ·
              refine ⟨1093221562646957321408753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2915257500391886190423341 1093221562646957321408753)
              ·
                refine ⟨819916171985217991056565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093221562646957321408753 819916171985217991056565)
                ·
                  refine ⟨76867141123614186661553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 819916171985217991056565 76867141123614186661553)
                  ·
                    rfl

theorem cell21_336821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_336821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336821 prefixEnd_336821 := by exact prefixLift 336821
  have htrace : WordTrace (prefixWord ++ tailWord_336821) baseStart_336821 baseEnd_336821 := by
    simpa [prefixWord, tailWord_336821, baseEnd_336821] using wordTrace_append hprefix tailTrace_336821
  have hstable : (prefixWord ++ tailWord_336821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336821).length < 2 ^ (prefixWord ++ tailWord_336821).sum := by decide
  have hdescent : baseEnd_336821 < baseStart_336821 := by decide
  rcases family_descends (prefixWord ++ tailWord_336821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336849 : List Nat := [1, 2, 2, 1, 2, 1, 12]
def baseStart_336849 : Nat := 118140960795 + 336849 * 2 ^ 59
def prefixEnd_336849 : Nat := 4983230072969 + 3 ^ 40 * 336849 * 2
def baseEnd_336849 : Nat := 8541503456121373354981

theorem tailTrace_336849 : CollatzResearch.WordTrace tailWord_336849 prefixEnd_336849 8541503456121373354981 := by
  unfold tailWord_336849
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285892356661077074173601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8190594904440718049449067 12285892356661077074173601)
  ·
    refine ⟨9214419267495807805630201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12285892356661077074173601 9214419267495807805630201)
    ·
      refine ⟨6910814450621855854222651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9214419267495807805630201 6910814450621855854222651)
      ·
        refine ⟨10366221675932783781333977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910814450621855854222651 10366221675932783781333977)
        ·
          refine ⟨7774666256949587836000483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10366221675932783781333977 7774666256949587836000483)
          ·
            refine ⟨11661999385424381754000725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774666256949587836000483 11661999385424381754000725)
            ·
              refine ⟨8541503456121373354981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11661999385424381754000725 8541503456121373354981)
              ·
                rfl

theorem cell21_336849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 12].length) (baseStart_336849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336849 prefixEnd_336849 := by exact prefixLift 336849
  have htrace : WordTrace (prefixWord ++ tailWord_336849) baseStart_336849 baseEnd_336849 := by
    simpa [prefixWord, tailWord_336849, baseEnd_336849] using wordTrace_append hprefix tailTrace_336849
  have hstable : (prefixWord ++ tailWord_336849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336849).length < 2 ^ (prefixWord ++ tailWord_336849).sum := by decide
  have hdescent : baseEnd_336849 < baseStart_336849 := by decide
  rcases family_descends (prefixWord ++ tailWord_336849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336852 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_336852 : Nat := 118140960795 + 336852 * 2 ^ 59
def prefixEnd_336852 : Nat := 4983230072969 + 3 ^ 40 * 336852 * 2
def baseEnd_336852 : Nat := 76874215745965021644823

theorem tailTrace_336852 : CollatzResearch.WordTrace tailWord_336852 prefixEnd_336852 76874215745965021644823 := by
  unfold tailWord_336852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143000887825104293266405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8190667850433472391021873 6143000887825104293266405)
  ·
    refine ⟨1151812666467207054987451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6143000887825104293266405 1151812666467207054987451)
    ·
      refine ⟨1727718999700810582481177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151812666467207054987451 1727718999700810582481177)
      ·
        refine ⟨1295789249775607936860883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727718999700810582481177 1295789249775607936860883)
        ·
          refine ⟨1943683874663411905291325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295789249775607936860883 1943683874663411905291325)
          ·
            refine ⟨728881452998779464484247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1943683874663411905291325 728881452998779464484247)
            ·
              refine ⟨1093322179498169196726371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728881452998779464484247 1093322179498169196726371)
              ·
                refine ⟨1639983269247253795089557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093322179498169196726371 1639983269247253795089557)
                ·
                  refine ⟨76874215745965021644823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1639983269247253795089557 76874215745965021644823)
                  ·
                    rfl

theorem cell21_336852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_336852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336852 prefixEnd_336852 := by exact prefixLift 336852
  have htrace : WordTrace (prefixWord ++ tailWord_336852) baseStart_336852 baseEnd_336852 := by
    simpa [prefixWord, tailWord_336852, baseEnd_336852] using wordTrace_append hprefix tailTrace_336852
  have hstable : (prefixWord ++ tailWord_336852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336852).length < 2 ^ (prefixWord ++ tailWord_336852).sum := by decide
  have hdescent : baseEnd_336852 < baseStart_336852 := by decide
  rcases family_descends (prefixWord ++ tailWord_336852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336942 : List Nat := [4, 1, 3, 1, 1, 1, 1, 9]
def baseStart_336942 : Nat := 118140960795 + 336942 * 2 ^ 59
def prefixEnd_336942 : Nat := 4983230072969 + 3 ^ 40 * 336942 * 2
def baseEnd_336942 : Nat := 25631584990714955048213

theorem tailTrace_336942 : CollatzResearch.WordTrace tailWord_336942 prefixEnd_336942 25631584990714955048213 := by
  unfold tailWord_336942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536160543165519244663635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8192856230216102638206053 1536160543165519244663635)
  ·
    refine ⟨2304240814748278866995453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536160543165519244663635 2304240814748278866995453)
    ·
      refine ⟨864090305530604575123295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2304240814748278866995453 864090305530604575123295)
      ·
        refine ⟨1296135458295906862684943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864090305530604575123295 1296135458295906862684943)
        ·
          refine ⟨1944203187443860294027415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296135458295906862684943 1944203187443860294027415)
          ·
            refine ⟨2916304781165790441041123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944203187443860294027415 2916304781165790441041123)
            ·
              refine ⟨4374457171748685661561685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916304781165790441041123 4374457171748685661561685)
              ·
                refine ⟨25631584990714955048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4374457171748685661561685 25631584990714955048213)
                ·
                  rfl

theorem cell21_336942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_336942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_336942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_336942 prefixEnd_336942 := by exact prefixLift 336942
  have htrace : WordTrace (prefixWord ++ tailWord_336942) baseStart_336942 baseEnd_336942 := by
    simpa [prefixWord, tailWord_336942, baseEnd_336942] using wordTrace_append hprefix tailTrace_336942
  have hstable : (prefixWord ++ tailWord_336942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336942).length < 2 ^ (prefixWord ++ tailWord_336942).sum := by decide
  have hdescent : baseEnd_336942 < baseStart_336942 := by decide
  rcases family_descends (prefixWord ++ tailWord_336942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337139 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_337139 : Nat := 118140960795 + 337139 * 2 ^ 59
def prefixEnd_337139 : Nat := 4983230072969 + 3 ^ 40 * 337139 * 2
def baseEnd_337139 : Nat := 76939713056116300360903

theorem tailTrace_337139 : CollatzResearch.WordTrace tailWord_337139 prefixEnd_337139 76939713056116300360903 := by
  unfold tailWord_337139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296469525610456602230471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8197646350406971068153647 12296469525610456602230471)
  ·
    refine ⟨18444704288415684903345707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12296469525610456602230471 18444704288415684903345707)
    ·
      refine ⟨27667056432623527355018561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18444704288415684903345707 27667056432623527355018561)
      ·
        refine ⟨20750292324467645516263921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27667056432623527355018561 20750292324467645516263921)
        ·
          refine ⟨15562719243350734137197941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20750292324467645516263921 15562719243350734137197941)
          ·
            refine ⟨1459004929064131325362307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15562719243350734137197941 1459004929064131325362307)
            ·
              refine ⟨2188507393596196988043461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459004929064131325362307 2188507393596196988043461)
              ·
                refine ⟨410345136299286935258149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2188507393596196988043461 410345136299286935258149)
                ·
                  refine ⟨76939713056116300360903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410345136299286935258149 76939713056116300360903)
                  ·
                    rfl

theorem cell21_337139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_337139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337139 prefixEnd_337139 := by exact prefixLift 337139
  have htrace : WordTrace (prefixWord ++ tailWord_337139) baseStart_337139 baseEnd_337139 := by
    simpa [prefixWord, tailWord_337139, baseEnd_337139] using wordTrace_append hprefix tailTrace_337139
  have hstable : (prefixWord ++ tailWord_337139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337139).length < 2 ^ (prefixWord ++ tailWord_337139).sum := by decide
  have hdescent : baseEnd_337139 < baseStart_337139 := by decide
  rcases family_descends (prefixWord ++ tailWord_337139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337156 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_337156 : Nat := 118140960795 + 337156 * 2 ^ 59
def prefixEnd_337156 : Nat := 4983230072969 + 3 ^ 40 * 337156 * 2
def baseEnd_337156 : Nat := 76943592687728048577535

theorem tailTrace_337156 : CollatzResearch.WordTrace tailWord_337156 prefixEnd_337156 76943592687728048577535 := by
  unfold tailWord_337156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148544783274434252799661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8198059711032579003732881 6148544783274434252799661)
  ·
    refine ⟨2305704293727912844799873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6148544783274434252799661 2305704293727912844799873)
    ·
      refine ⟨1729278220295934633599905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2305704293727912844799873 1729278220295934633599905)
      ·
        refine ⟨1296958665221950975199929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729278220295934633599905 1296958665221950975199929)
        ·
          refine ⟨972718998916463231399947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296958665221950975199929 972718998916463231399947)
          ·
            refine ⟨1459078498374694847099921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972718998916463231399947 1459078498374694847099921)
            ·
              refine ⟨1094308873781021135324941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459078498374694847099921 1094308873781021135324941)
              ·
                refine ⟨410365827667882925746853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094308873781021135324941 410365827667882925746853)
                ·
                  refine ⟨76943592687728048577535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410365827667882925746853 76943592687728048577535)
                  ·
                    rfl

theorem cell21_337156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_337156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337156 prefixEnd_337156 := by exact prefixLift 337156
  have htrace : WordTrace (prefixWord ++ tailWord_337156) baseStart_337156 baseEnd_337156 := by
    simpa [prefixWord, tailWord_337156, baseEnd_337156] using wordTrace_append hprefix tailTrace_337156
  have hstable : (prefixWord ++ tailWord_337156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337156).length < 2 ^ (prefixWord ++ tailWord_337156).sum := by decide
  have hdescent : baseEnd_337156 < baseStart_337156 := by decide
  rcases family_descends (prefixWord ++ tailWord_337156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337201 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_337201 : Nat := 118140960795 + 337201 * 2 ^ 59
def prefixEnd_337201 : Nat := 4983230072969 + 3 ^ 40 * 337201 * 2
def baseEnd_337201 : Nat := 76953862300817970327443

theorem tailTrace_337201 : CollatzResearch.WordTrace tailWord_337201 prefixEnd_337201 76953862300817970327443 := by
  unfold tailWord_337201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12298730851385841190987457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8199153900923894127324971 12298730851385841190987457)
  ·
    refine ⟨9224048138539380893240593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12298730851385841190987457 9224048138539380893240593)
    ·
      refine ⟨6918036103904535669930445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9224048138539380893240593 6918036103904535669930445)
      ·
        refine ⟨2594263538964200876223917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6918036103904535669930445 2594263538964200876223917)
        ·
          refine ⟨972848827111575328583969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2594263538964200876223917 972848827111575328583969)
          ·
            refine ⟨729636620333681496437977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972848827111575328583969 729636620333681496437977)
            ·
              refine ⟨547227465250261122328483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729636620333681496437977 547227465250261122328483)
              ·
                refine ⟨820841197875391683492725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547227465250261122328483 820841197875391683492725)
                ·
                  refine ⟨76953862300817970327443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 820841197875391683492725 76953862300817970327443)
                  ·
                    rfl

theorem cell21_337201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_337201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337201 prefixEnd_337201 := by exact prefixLift 337201
  have htrace : WordTrace (prefixWord ++ tailWord_337201) baseStart_337201 baseEnd_337201 := by
    simpa [prefixWord, tailWord_337201, baseEnd_337201] using wordTrace_append hprefix tailTrace_337201
  have hstable : (prefixWord ++ tailWord_337201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337201).length < 2 ^ (prefixWord ++ tailWord_337201).sum := by decide
  have hdescent : baseEnd_337201 < baseStart_337201 := by decide
  rcases family_descends (prefixWord ++ tailWord_337201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337238 : List Nat := [5, 2, 3, 1, 2, 1, 7]
def baseStart_337238 : Nat := 118140960795 + 337238 * 2 ^ 59
def prefixEnd_337238 : Nat := 4983230072969 + 3 ^ 40 * 337238 * 2
def baseEnd_337238 : Nat := 8551367356101569801189

theorem tailTrace_337238 : CollatzResearch.WordTrace tailWord_337238 prefixEnd_337238 8551367356101569801189 := by
  unfold tailWord_337238
  simp only [CollatzResearch.WordTrace]
  refine ⟨768755022015737281880273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8200053568167864340056245 768755022015737281880273)
  ·
    refine ⟨576566266511802961410205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 768755022015737281880273 576566266511802961410205)
    ·
      refine ⟨216212349941926110528827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 576566266511802961410205 216212349941926110528827)
      ·
        refine ⟨324318524912889165793241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216212349941926110528827 324318524912889165793241)
        ·
          refine ⟨243238893684666874344931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324318524912889165793241 243238893684666874344931)
          ·
            refine ⟨364858340527000311517397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243238893684666874344931 364858340527000311517397)
            ·
              refine ⟨8551367356101569801189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 364858340527000311517397 8551367356101569801189)
              ·
                rfl

theorem cell21_337238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 7].length) (baseStart_337238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337238 prefixEnd_337238 := by exact prefixLift 337238
  have htrace : WordTrace (prefixWord ++ tailWord_337238) baseStart_337238 baseEnd_337238 := by
    simpa [prefixWord, tailWord_337238, baseEnd_337238] using wordTrace_append hprefix tailTrace_337238
  have hstable : (prefixWord ++ tailWord_337238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337238).length < 2 ^ (prefixWord ++ tailWord_337238).sum := by decide
  have hdescent : baseEnd_337238 < baseStart_337238 := by decide
  rcases family_descends (prefixWord ++ tailWord_337238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337311 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 3]
def baseStart_337311 : Nat := 118140960795 + 337311 * 2 ^ 59
def prefixEnd_337311 : Nat := 4983230072969 + 3 ^ 40 * 337311 * 2
def baseEnd_337311 : Nat := 76978965799482223493885

theorem tailTrace_337311 : CollatzResearch.WordTrace tailWord_337311 prefixEnd_337311 76978965799482223493885 := by
  unfold tailWord_337311
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302742880987329977491787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8201828587324886651661191 12302742880987329977491787)
  ·
    refine ⟨18454114321480994966237681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12302742880987329977491787 18454114321480994966237681)
    ·
      refine ⟨13840585741110746224678261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18454114321480994966237681 13840585741110746224678261)
      ·
        refine ⟨1297554913229132458563587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13840585741110746224678261 1297554913229132458563587)
        ·
          refine ⟨1946332369843698687845381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297554913229132458563587 1946332369843698687845381)
          ·
            refine ⟨364937319345693503971009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1946332369843698687845381 364937319345693503971009)
            ·
              refine ⟨273702989509270127978257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364937319345693503971009 273702989509270127978257)
              ·
                refine ⟨205277242131952595983693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273702989509270127978257 205277242131952595983693)
                ·
                  refine ⟨76978965799482223493885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205277242131952595983693 76978965799482223493885)
                  ·
                    rfl

theorem cell21_337311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 3].length) (baseStart_337311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337311 prefixEnd_337311 := by exact prefixLift 337311
  have htrace : WordTrace (prefixWord ++ tailWord_337311) baseStart_337311 baseEnd_337311 := by
    simpa [prefixWord, tailWord_337311, baseEnd_337311] using wordTrace_append hprefix tailTrace_337311
  have hstable : (prefixWord ++ tailWord_337311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337311).length < 2 ^ (prefixWord ++ tailWord_337311).sum := by decide
  have hdescent : baseEnd_337311 < baseStart_337311 := by decide
  rcases family_descends (prefixWord ++ tailWord_337311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337384 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_337384 : Nat := 118140960795 + 337384 * 2 ^ 59
def prefixEnd_337384 : Nat := 4983230072969 + 3 ^ 40 * 337384 * 2
def baseEnd_337384 : Nat := 76995625394050318777069

theorem tailTrace_337384 : CollatzResearch.WordTrace tailWord_337384 prefixEnd_337384 76995625394050318777069 := by
  unfold tailWord_337384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152702704861431722449603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8203603606481908963266137 6152702704861431722449603)
  ·
    refine ⟨9229054057292147583674405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6152702704861431722449603 9229054057292147583674405)
    ·
      refine ⟨1730447635742277671938951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9229054057292147583674405 1730447635742277671938951)
      ·
        refine ⟨2595671453613416507908427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730447635742277671938951 2595671453613416507908427)
        ·
          refine ⟨3893507180420124761862641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595671453613416507908427 3893507180420124761862641)
          ·
            refine ⟨2920130385315093571396981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3893507180420124761862641 2920130385315093571396981)
            ·
              refine ⟨273762223623290022318467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2920130385315093571396981 273762223623290022318467)
              ·
                refine ⟨410643335434935033477701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273762223623290022318467 410643335434935033477701)
                ·
                  refine ⟨76995625394050318777069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410643335434935033477701 76995625394050318777069)
                  ·
                    rfl

theorem cell21_337384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_337384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337384 prefixEnd_337384 := by exact prefixLift 337384
  have htrace : WordTrace (prefixWord ++ tailWord_337384) baseStart_337384 baseEnd_337384 := by
    simpa [prefixWord, tailWord_337384, baseEnd_337384] using wordTrace_append hprefix tailTrace_337384
  have hstable : (prefixWord ++ tailWord_337384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337384).length < 2 ^ (prefixWord ++ tailWord_337384).sum := by decide
  have hdescent : baseEnd_337384 < baseStart_337384 := by decide
  rcases family_descends (prefixWord ++ tailWord_337384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337395 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_337395 : Nat := 118140960795 + 337395 * 2 ^ 59
def prefixEnd_337395 : Nat := 4983230072969 + 3 ^ 40 * 337395 * 2
def baseEnd_337395 : Nat := 76998135743916744093713

theorem tailTrace_337395 : CollatzResearch.WordTrace tailWord_337395 prefixEnd_337395 76998135743916744093713 := by
  unfold tailWord_337395
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305806612683012323549639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8203871075122008215699759 12305806612683012323549639)
  ·
    refine ⟨18458709919024518485324459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12305806612683012323549639 18458709919024518485324459)
    ·
      refine ⟨27688064878536777727986689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458709919024518485324459 27688064878536777727986689)
      ·
        refine ⟨20766048658902583295990017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27688064878536777727986689 20766048658902583295990017)
        ·
          refine ⟨15574536494176937471992513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20766048658902583295990017 15574536494176937471992513)
          ·
            refine ⟨11680902370632703103994385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15574536494176937471992513 11680902370632703103994385)
            ·
              refine ⟨8760676777974527327995789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11680902370632703103994385 8760676777974527327995789)
              ·
                refine ⟨3285253791740447747998421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8760676777974527327995789 3285253791740447747998421)
                ·
                  refine ⟨76998135743916744093713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3285253791740447747998421 76998135743916744093713)
                  ·
                    rfl

theorem cell21_337395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_337395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337395 prefixEnd_337395 := by exact prefixLift 337395
  have htrace : WordTrace (prefixWord ++ tailWord_337395) baseStart_337395 baseEnd_337395 := by
    simpa [prefixWord, tailWord_337395, baseEnd_337395] using wordTrace_append hprefix tailTrace_337395
  have hstable : (prefixWord ++ tailWord_337395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337395).length < 2 ^ (prefixWord ++ tailWord_337395).sum := by decide
  have hdescent : baseEnd_337395 < baseStart_337395 := by decide
  rcases family_descends (prefixWord ++ tailWord_337395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337398 : List Nat := [5, 1, 1, 1, 2, 3, 1, 7]
def baseStart_337398 : Nat := 118140960795 + 337398 * 2 ^ 59
def prefixEnd_337398 : Nat := 4983230072969 + 3 ^ 40 * 337398 * 2
def baseEnd_337398 : Nat := 25666273461596468514569

theorem tailTrace_337398 : CollatzResearch.WordTrace tailWord_337398 prefixEnd_337398 25666273461596468514569 := by
  unfold tailWord_337398
  simp only [CollatzResearch.WordTrace]
  refine ⟨769119751979508989744303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8203944021114762557272565 769119751979508989744303)
  ·
    refine ⟨1153679627969263484616455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 769119751979508989744303 1153679627969263484616455)
    ·
      refine ⟨1730519441953895226924683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1153679627969263484616455 1730519441953895226924683)
      ·
        refine ⟨2595779162930842840387025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730519441953895226924683 2595779162930842840387025)
        ·
          refine ⟨1946834372198132130290269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595779162930842840387025 1946834372198132130290269)
          ·
            refine ⟨730062889574299548858851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1946834372198132130290269 730062889574299548858851)
            ·
              refine ⟨1095094334361449323288277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730062889574299548858851 1095094334361449323288277)
              ·
                refine ⟨25666273461596468514569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1095094334361449323288277 25666273461596468514569)
                ·
                  rfl

theorem cell21_337398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_337398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337398 prefixEnd_337398 := by exact prefixLift 337398
  have htrace : WordTrace (prefixWord ++ tailWord_337398) baseStart_337398 baseEnd_337398 := by
    simpa [prefixWord, tailWord_337398, baseEnd_337398] using wordTrace_append hprefix tailTrace_337398
  have hstable : (prefixWord ++ tailWord_337398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337398).length < 2 ^ (prefixWord ++ tailWord_337398).sum := by decide
  have hdescent : baseEnd_337398 < baseStart_337398 := by decide
  rcases family_descends (prefixWord ++ tailWord_337398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337421 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 3]
def baseStart_337421 : Nat := 118140960795 + 337421 * 2 ^ 59
def prefixEnd_337421 : Nat := 4983230072969 + 3 ^ 40 * 337421 * 2
def baseEnd_337421 : Nat := 77004069298146476660327

theorem tailTrace_337421 : CollatzResearch.WordTrace tailWord_337421 prefixEnd_337421 77004069298146476660327 := by
  unfold tailWord_337421
  simp only [CollatzResearch.WordTrace]
  refine ⟨12306754910588818763996117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8204503273725879175997411 12306754910588818763996117)
  ·
    refine ⟨288439568216925439781159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12306754910588818763996117 288439568216925439781159)
    ·
      refine ⟨432659352325388159671739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288439568216925439781159 432659352325388159671739)
      ·
        refine ⟨648989028488082239507609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432659352325388159671739 648989028488082239507609)
        ·
          refine ⟨486741771366061679630707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648989028488082239507609 486741771366061679630707)
          ·
            refine ⟨730112657049092519446061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486741771366061679630707 730112657049092519446061)
            ·
              refine ⟨273792246393409694792273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 730112657049092519446061 273792246393409694792273)
              ·
                refine ⟨205344184795057271094205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273792246393409694792273 205344184795057271094205)
                ·
                  refine ⟨77004069298146476660327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205344184795057271094205 77004069298146476660327)
                  ·
                    rfl

theorem cell21_337421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_337421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337421 prefixEnd_337421 := by exact prefixLift 337421
  have htrace : WordTrace (prefixWord ++ tailWord_337421) baseStart_337421 baseEnd_337421 := by
    simpa [prefixWord, tailWord_337421, baseEnd_337421] using wordTrace_append hprefix tailTrace_337421
  have hstable : (prefixWord ++ tailWord_337421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337421).length < 2 ^ (prefixWord ++ tailWord_337421).sum := by decide
  have hdescent : baseEnd_337421 < baseStart_337421 := by decide
  rcases family_descends (prefixWord ++ tailWord_337421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337429 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 5]
def baseStart_337429 : Nat := 118140960795 + 337429 * 2 ^ 59
def prefixEnd_337429 : Nat := 4983230072969 + 3 ^ 40 * 337429 * 2
def baseEnd_337429 : Nat := 77005895007140240526977

theorem tailTrace_337429 : CollatzResearch.WordTrace tailWord_337429 prefixEnd_337429 77005895007140240526977 := by
  unfold tailWord_337429
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307046694559836130287341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8204697796373224086858227 12307046694559836130287341)
  ·
    refine ⟨4615142510459938548857753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12307046694559836130287341 4615142510459938548857753)
    ·
      refine ⟨3461356882844953911643315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4615142510459938548857753 3461356882844953911643315)
      ·
        refine ⟨5192035324267430867464973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461356882844953911643315 5192035324267430867464973)
        ·
          refine ⟨1947013246600286575299365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5192035324267430867464973 1947013246600286575299365)
          ·
            refine ⟨365064983737553732868631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1947013246600286575299365 365064983737553732868631)
            ·
              refine ⟨547597475606330599302947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365064983737553732868631 547597475606330599302947)
              ·
                refine ⟨821396213409495898954421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547597475606330599302947 821396213409495898954421)
                ·
                  refine ⟨77005895007140240526977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821396213409495898954421 77005895007140240526977)
                  ·
                    rfl

theorem cell21_337429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_337429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337429 prefixEnd_337429 := by exact prefixLift 337429
  have htrace : WordTrace (prefixWord ++ tailWord_337429) baseStart_337429 baseEnd_337429 := by
    simpa [prefixWord, tailWord_337429, baseEnd_337429] using wordTrace_append hprefix tailTrace_337429
  have hstable : (prefixWord ++ tailWord_337429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337429).length < 2 ^ (prefixWord ++ tailWord_337429).sum := by decide
  have hdescent : baseEnd_337429 < baseStart_337429 := by decide
  rcases family_descends (prefixWord ++ tailWord_337429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337522 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_337522 : Nat := 118140960795 + 337522 * 2 ^ 59
def prefixEnd_337522 : Nat := 4983230072969 + 3 ^ 40 * 337522 * 2
def baseEnd_337522 : Nat := 77027118874192745476787

theorem tailTrace_337522 : CollatzResearch.WordTrace tailWord_337522 prefixEnd_337522 77027118874192745476787 := by
  unfold tailWord_337522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077609670805728253355705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8206959122148608675615213 3077609670805728253355705)
  ·
    refine ⟨2308207253104296190016779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3077609670805728253355705 2308207253104296190016779)
    ·
      refine ⟨3462310879656444285025169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308207253104296190016779 3462310879656444285025169)
      ·
        refine ⟨2596733159742333213768877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3462310879656444285025169 2596733159742333213768877)
        ·
          refine ⟨973774934903374955163329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2596733159742333213768877 973774934903374955163329)
          ·
            refine ⟨730331201177531216372497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973774934903374955163329 730331201177531216372497)
            ·
              refine ⟨547748400883148412279373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730331201177531216372497 547748400883148412279373)
              ·
                refine ⟨205405650331180654604765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 547748400883148412279373 205405650331180654604765)
                ·
                  refine ⟨77027118874192745476787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205405650331180654604765 77027118874192745476787)
                  ·
                    rfl

theorem cell21_337522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_337522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337522 prefixEnd_337522 := by exact prefixLift 337522
  have htrace : WordTrace (prefixWord ++ tailWord_337522) baseStart_337522 baseEnd_337522 := by
    simpa [prefixWord, tailWord_337522, baseEnd_337522] using wordTrace_append hprefix tailTrace_337522
  have hstable : (prefixWord ++ tailWord_337522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337522).length < 2 ^ (prefixWord ++ tailWord_337522).sum := by decide
  have hdescent : baseEnd_337522 < baseStart_337522 := by decide
  rcases family_descends (prefixWord ++ tailWord_337522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337533 : List Nat := [1, 4, 1, 1, 4, 2, 8]
def baseStart_337533 : Nat := 118140960795 + 337533 * 2 ^ 59
def prefixEnd_337533 : Nat := 4983230072969 + 3 ^ 40 * 337533 * 2
def baseEnd_337533 : Nat := 8558847691562130088159

theorem tailTrace_337533 : CollatzResearch.WordTrace tailWord_337533 prefixEnd_337533 8558847691562130088159 := by
  unfold tailWord_337533
  simp only [CollatzResearch.WordTrace]
  refine ⟨12310839886183061892073253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8207226590788707928048835 12310839886183061892073253)
  ·
    refine ⟨2308282478659324104763735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12310839886183061892073253 2308282478659324104763735)
    ·
      refine ⟨3462423717988986157145603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308282478659324104763735 3462423717988986157145603)
      ·
        refine ⟨5193635576983479235718405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462423717988986157145603 5193635576983479235718405)
        ·
          refine ⟨973806670684402356697201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5193635576983479235718405 973806670684402356697201)
          ·
            refine ⟨730355003013301767522901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973806670684402356697201 730355003013301767522901)
            ·
              refine ⟨8558847691562130088159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 730355003013301767522901 8558847691562130088159)
              ·
                rfl

theorem cell21_337533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 8].length) (baseStart_337533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337533 prefixEnd_337533 := by exact prefixLift 337533
  have htrace : WordTrace (prefixWord ++ tailWord_337533) baseStart_337533 baseEnd_337533 := by
    simpa [prefixWord, tailWord_337533, baseEnd_337533] using wordTrace_append hprefix tailTrace_337533
  have hstable : (prefixWord ++ tailWord_337533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337533).length < 2 ^ (prefixWord ++ tailWord_337533).sum := by decide
  have hdescent : baseEnd_337533 < baseStart_337533 := by decide
  rcases family_descends (prefixWord ++ tailWord_337533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337612 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_337612 : Nat := 118140960795 + 337612 * 2 ^ 59
def prefixEnd_337612 : Nat := 4983230072969 + 3 ^ 40 * 337612 * 2
def baseEnd_337612 : Nat := 77047658100372588976603

theorem tailTrace_337612 : CollatzResearch.WordTrace tailWord_337612 prefixEnd_337612 77047658100372588976603 := by
  unfold tailWord_337612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156860626448429192099545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8209147501931238922799393 6156860626448429192099545)
  ·
    refine ⟨4617645469836321894074659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6156860626448429192099545 4617645469836321894074659)
    ·
      refine ⟨6926468204754482841111989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4617645469836321894074659 6926468204754482841111989)
      ·
        refine ⟨649356394195732766354249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6926468204754482841111989 649356394195732766354249)
        ·
          refine ⟨487017295646799574765687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649356394195732766354249 487017295646799574765687)
          ·
            refine ⟨730525943470199362148531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487017295646799574765687 730525943470199362148531)
            ·
              refine ⟨1095788915205299043222797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730525943470199362148531 1095788915205299043222797)
              ·
                refine ⟨410920843201987141208549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095788915205299043222797 410920843201987141208549)
                ·
                  refine ⟨77047658100372588976603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410920843201987141208549 77047658100372588976603)
                  ·
                    rfl

theorem cell21_337612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_337612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337612 prefixEnd_337612 := by exact prefixLift 337612
  have htrace : WordTrace (prefixWord ++ tailWord_337612) baseStart_337612 baseEnd_337612 := by
    simpa [prefixWord, tailWord_337612, baseEnd_337612] using wordTrace_append hprefix tailTrace_337612
  have hstable : (prefixWord ++ tailWord_337612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337612).length < 2 ^ (prefixWord ++ tailWord_337612).sum := by decide
  have hdescent : baseEnd_337612 < baseStart_337612 := by decide
  rcases family_descends (prefixWord ++ tailWord_337612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337623 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_337623 : Nat := 118140960795 + 337623 * 2 ^ 59
def prefixEnd_337623 : Nat := 4983230072969 + 3 ^ 40 * 337623 * 2
def baseEnd_337623 : Nat := 77050168450239014293247

theorem tailTrace_337623 : CollatzResearch.WordTrace tailWord_337623 prefixEnd_337623 77050168450239014293247 := by
  unfold tailWord_337623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314122455857007262849523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8209414970571338175233015 12314122455857007262849523)
  ·
    refine ⟨18471183683785510894274285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12314122455857007262849523 18471183683785510894274285)
    ·
      refine ⟨6926693881419566585352857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18471183683785510894274285 6926693881419566585352857)
      ·
        refine ⟨5195020411064674939014643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6926693881419566585352857 5195020411064674939014643)
        ·
          refine ⟨7792530616597012408521965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195020411064674939014643 7792530616597012408521965)
          ·
            refine ⟨2922198981223879653195737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7792530616597012408521965 2922198981223879653195737)
            ·
              refine ⟨2191649235917909739896803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922198981223879653195737 2191649235917909739896803)
              ·
                refine ⟨3287473853876864609845205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191649235917909739896803 3287473853876864609845205)
                ·
                  refine ⟨77050168450239014293247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3287473853876864609845205 77050168450239014293247)
                  ·
                    rfl

theorem cell21_337623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_337623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337623 prefixEnd_337623 := by exact prefixLift 337623
  have htrace : WordTrace (prefixWord ++ tailWord_337623) baseStart_337623 baseEnd_337623 := by
    simpa [prefixWord, tailWord_337623, baseEnd_337623] using wordTrace_append hprefix tailTrace_337623
  have hstable : (prefixWord ++ tailWord_337623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337623).length < 2 ^ (prefixWord ++ tailWord_337623).sum := by decide
  have hdescent : baseEnd_337623 < baseStart_337623 := by decide
  rcases family_descends (prefixWord ++ tailWord_337623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337826 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_337826 : Nat := 118140960795 + 337826 * 2 ^ 59
def prefixEnd_337826 : Nat := 4983230072969 + 3 ^ 40 * 337826 * 2
def baseEnd_337826 : Nat := 77096495815955772409499

theorem tailTrace_337826 : CollatzResearch.WordTrace tailWord_337826 prefixEnd_337826 77096495815955772409499 := by
  unfold tailWord_337826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080381618530393233122333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8214350982747715288326221 3080381618530393233122333)
  ·
    refine ⟨1155143106948897462420875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3080381618530393233122333 1155143106948897462420875)
    ·
      refine ⟨1732714660423346193631313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155143106948897462420875 1732714660423346193631313)
      ·
        refine ⟨1299535995317509645223485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732714660423346193631313 1299535995317509645223485)
        ·
          refine ⟨487325998244066116958807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1299535995317509645223485 487325998244066116958807)
          ·
            refine ⟨730988997366099175438211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487325998244066116958807 730988997366099175438211)
            ·
              refine ⟨1096483496049148763157317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730988997366099175438211 1096483496049148763157317)
              ·
                refine ⟨205590655509215393091997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1096483496049148763157317 205590655509215393091997)
                ·
                  refine ⟨77096495815955772409499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205590655509215393091997 77096495815955772409499)
                  ·
                    rfl

theorem cell21_337826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_337826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337826 prefixEnd_337826 := by exact prefixLift 337826
  have htrace : WordTrace (prefixWord ++ tailWord_337826) baseStart_337826 baseEnd_337826 := by
    simpa [prefixWord, tailWord_337826, baseEnd_337826] using wordTrace_append hprefix tailTrace_337826
  have hstable : (prefixWord ++ tailWord_337826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337826).length < 2 ^ (prefixWord ++ tailWord_337826).sum := by decide
  have hdescent : baseEnd_337826 < baseStart_337826 := by decide
  rcases family_descends (prefixWord ++ tailWord_337826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337854 : List Nat := [4, 2, 1, 1, 1, 4, 3, 5]
def baseStart_337854 : Nat := 118140960795 + 337854 * 2 ^ 59
def prefixEnd_337854 : Nat := 4983230072969 + 3 ^ 40 * 337854 * 2
def baseEnd_337854 : Nat := 25700961932477981980925

theorem tailTrace_337854 : CollatzResearch.WordTrace tailWord_337854 prefixEnd_337854 25700961932477981980925 := by
  unfold tailWord_337854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540318464752516714313577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8215031812013422476339077 1540318464752516714313577)
  ·
    refine ⟨1155238848564387535735183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1540318464752516714313577 1155238848564387535735183)
    ·
      refine ⟨1732858272846581303602775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155238848564387535735183 1732858272846581303602775)
      ·
        refine ⟨2599287409269871955404163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732858272846581303602775 2599287409269871955404163)
        ·
          refine ⟨3898931113904807933106245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599287409269871955404163 3898931113904807933106245)
          ·
            refine ⟨731049583857151487457421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3898931113904807933106245 731049583857151487457421)
            ·
              refine ⟨274143593946431807796533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 731049583857151487457421 274143593946431807796533)
              ·
                refine ⟨25700961932477981980925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274143593946431807796533 25700961932477981980925)
                ·
                  rfl

theorem cell21_337854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_337854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337854 prefixEnd_337854 := by exact prefixLift 337854
  have htrace : WordTrace (prefixWord ++ tailWord_337854) baseStart_337854 baseEnd_337854 := by
    simpa [prefixWord, tailWord_337854, baseEnd_337854] using wordTrace_append hprefix tailTrace_337854
  have hstable : (prefixWord ++ tailWord_337854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337854).length < 2 ^ (prefixWord ++ tailWord_337854).sum := by decide
  have hdescent : baseEnd_337854 < baseStart_337854 := by decide
  rcases family_descends (prefixWord ++ tailWord_337854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337865 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_337865 : Nat := 118140960795 + 337865 * 2 ^ 59
def prefixEnd_337865 : Nat := 4983230072969 + 3 ^ 40 * 337865 * 2
def baseEnd_337865 : Nat := 77105396147300371259419

theorem tailTrace_337865 : CollatzResearch.WordTrace tailWord_337865 prefixEnd_337865 77105396147300371259419 := by
  unfold tailWord_337865
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322948920980282593159049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8215299280653521728772699 12322948920980282593159049)
  ·
    refine ⟨9242211690735211944869287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12322948920980282593159049 9242211690735211944869287)
    ·
      refine ⟨13863317536102817917303931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9242211690735211944869287 13863317536102817917303931)
      ·
        refine ⟨20794976304154226875955897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13863317536102817917303931 20794976304154226875955897)
        ·
          refine ⟨15596232228115670156966923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20794976304154226875955897 15596232228115670156966923)
          ·
            refine ⟨23394348342173505235450385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15596232228115670156966923 23394348342173505235450385)
            ·
              refine ⟨17545761256630128926587789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23394348342173505235450385 17545761256630128926587789)
              ·
                refine ⟨6579660471236298347470421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17545761256630128926587789 6579660471236298347470421)
                ·
                  refine ⟨77105396147300371259419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6579660471236298347470421 77105396147300371259419)
                  ·
                    rfl

theorem cell21_337865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_337865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337865 prefixEnd_337865 := by exact prefixLift 337865
  have htrace : WordTrace (prefixWord ++ tailWord_337865) baseStart_337865 baseEnd_337865 := by
    simpa [prefixWord, tailWord_337865, baseEnd_337865] using wordTrace_append hprefix tailTrace_337865
  have hstable : (prefixWord ++ tailWord_337865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337865).length < 2 ^ (prefixWord ++ tailWord_337865).sum := by decide
  have hdescent : baseEnd_337865 < baseStart_337865 := by decide
  rcases family_descends (prefixWord ++ tailWord_337865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337885 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_337885 : Nat := 118140960795 + 337885 * 2 ^ 59
def prefixEnd_337885 : Nat := 4983230072969 + 3 ^ 40 * 337885 * 2
def baseEnd_337885 : Nat := 77109960419784780926045

theorem tailTrace_337885 : CollatzResearch.WordTrace tailWord_337885 prefixEnd_337885 77109960419784780926045 := by
  unfold tailWord_337885
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323678380907826008887109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8215785587271884005924739 12323678380907826008887109)
  ·
    refine ⟨2310689696420217376666333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12323678380907826008887109 2310689696420217376666333)
    ·
      refine ⟨866508636157581516249875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2310689696420217376666333 866508636157581516249875)
      ·
        refine ⟨1299762954236372274374813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866508636157581516249875 1299762954236372274374813)
        ·
          refine ⟨487411107838639602890555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1299762954236372274374813 487411107838639602890555)
          ·
            refine ⟨731116661757959404335833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487411107838639602890555 731116661757959404335833)
            ·
              refine ⟨548337496318469553251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731116661757959404335833 548337496318469553251875)
              ·
                refine ⟨822506244477704329877813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548337496318469553251875 822506244477704329877813)
                ·
                  refine ⟨77109960419784780926045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 822506244477704329877813 77109960419784780926045)
                  ·
                    rfl

theorem cell21_337885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_337885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337885 prefixEnd_337885 := by exact prefixLift 337885
  have htrace : WordTrace (prefixWord ++ tailWord_337885) baseStart_337885 baseEnd_337885 := by
    simpa [prefixWord, tailWord_337885, baseEnd_337885] using wordTrace_append hprefix tailTrace_337885
  have hstable : (prefixWord ++ tailWord_337885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337885).length < 2 ^ (prefixWord ++ tailWord_337885).sum := by decide
  have hdescent : baseEnd_337885 < baseStart_337885 := by decide
  rcases family_descends (prefixWord ++ tailWord_337885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337896 : List Nat := [2, 1, 4, 1, 1, 1, 1, 10]
def baseStart_337896 : Nat := 118140960795 + 337896 * 2 ^ 59
def prefixEnd_337896 : Nat := 4983230072969 + 3 ^ 40 * 337896 * 2
def baseEnd_337896 : Nat := 25704156923217068747563

theorem tailTrace_337896 : CollatzResearch.WordTrace tailWord_337896 prefixEnd_337896 25704156923217068747563 := by
  unfold tailWord_337896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162039791933987443768771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8216053055911983258358361 6162039791933987443768771)
  ·
    refine ⟨9243059687900981165653157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6162039791933987443768771 9243059687900981165653157)
    ·
      refine ⟨1733073691481433968559967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9243059687900981165653157 1733073691481433968559967)
      ·
        refine ⟨2599610537222150952839951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733073691481433968559967 2599610537222150952839951)
        ·
          refine ⟨3899415805833226429259927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599610537222150952839951 3899415805833226429259927)
          ·
            refine ⟨5849123708749839643889891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899415805833226429259927 5849123708749839643889891)
            ·
              refine ⟨8773685563124759465834837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849123708749839643889891 8773685563124759465834837)
              ·
                refine ⟨25704156923217068747563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8773685563124759465834837 25704156923217068747563)
                ·
                  rfl

theorem cell21_337896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_337896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337896 prefixEnd_337896 := by exact prefixLift 337896
  have htrace : WordTrace (prefixWord ++ tailWord_337896) baseStart_337896 baseEnd_337896 := by
    simpa [prefixWord, tailWord_337896, baseEnd_337896] using wordTrace_append hprefix tailTrace_337896
  have hstable : (prefixWord ++ tailWord_337896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337896).length < 2 ^ (prefixWord ++ tailWord_337896).sum := by decide
  have hdescent : baseEnd_337896 < baseStart_337896 := by decide
  rcases family_descends (prefixWord ++ tailWord_337896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337913 : List Nat := [1, 2, 1, 3, 1, 4, 4, 5]
def baseStart_337913 : Nat := 118140960795 + 337913 * 2 ^ 59
def prefixEnd_337913 : Nat := 4983230072969 + 3 ^ 40 * 337913 * 2
def baseEnd_337913 : Nat := 25705450133754318153107

theorem tailTrace_337913 : CollatzResearch.WordTrace tailWord_337913 prefixEnd_337913 25705450133754318153107 := by
  unfold tailWord_337913
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324699624806386790906393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8216466416537591193937595 12324699624806386790906393)
  ·
    refine ⟨9243524718604790093179795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12324699624806386790906393 9243524718604790093179795)
    ·
      refine ⟨13865287077907185139769693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9243524718604790093179795 13865287077907185139769693)
      ·
        refine ⟨5199482654215194427413635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13865287077907185139769693 5199482654215194427413635)
        ·
          refine ⟨7799223981322791641120453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199482654215194427413635 7799223981322791641120453)
          ·
            refine ⟨1462354496498023432710085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7799223981322791641120453 1462354496498023432710085)
            ·
              refine ⟨274191468093379393633141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1462354496498023432710085 274191468093379393633141)
              ·
                refine ⟨25705450133754318153107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274191468093379393633141 25705450133754318153107)
                ·
                  rfl

theorem cell21_337913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 5].length) (baseStart_337913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337913 prefixEnd_337913 := by exact prefixLift 337913
  have htrace : WordTrace (prefixWord ++ tailWord_337913) baseStart_337913 baseEnd_337913 := by
    simpa [prefixWord, tailWord_337913, baseEnd_337913] using wordTrace_append hprefix tailTrace_337913
  have hstable : (prefixWord ++ tailWord_337913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337913).length < 2 ^ (prefixWord ++ tailWord_337913).sum := by decide
  have hdescent : baseEnd_337913 < baseStart_337913 := by decide
  rcases family_descends (prefixWord ++ tailWord_337913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337930 : List Nat := [3, 1, 2, 2, 5, 1, 7]
def baseStart_337930 : Nat := 118140960795 + 337930 * 2 ^ 59
def prefixEnd_337930 : Nat := 4983230072969 + 3 ^ 40 * 337930 * 2
def baseEnd_337930 : Nat := 8568914448097189186217

theorem tailTrace_337930 : CollatzResearch.WordTrace tailWord_337930 prefixEnd_337930 8568914448097189186217 := by
  unfold tailWord_337930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081329916436199673568811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8216879777163199129516829 3081329916436199673568811)
  ·
    refine ⟨4621994874654299510353217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3081329916436199673568811 4621994874654299510353217)
    ·
      refine ⟨3466496155990724632764913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4621994874654299510353217 3466496155990724632764913)
      ·
        refine ⟨2599872116993043474573685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3466496155990724632764913 2599872116993043474573685)
        ·
          refine ⟨243738010968097825741283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2599872116993043474573685 243738010968097825741283)
          ·
            refine ⟨365607016452146738611925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243738010968097825741283 365607016452146738611925)
            ·
              refine ⟨8568914448097189186217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 365607016452146738611925 8568914448097189186217)
              ·
                rfl

theorem cell21_337930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 7].length) (baseStart_337930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_337930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_337930 prefixEnd_337930 := by exact prefixLift 337930
  have htrace : WordTrace (prefixWord ++ tailWord_337930) baseStart_337930 baseEnd_337930 := by
    simpa [prefixWord, tailWord_337930, baseEnd_337930] using wordTrace_append hprefix tailTrace_337930
  have hstable : (prefixWord ++ tailWord_337930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337930).length < 2 ^ (prefixWord ++ tailWord_337930).sum := by decide
  have hdescent : baseEnd_337930 < baseStart_337930 := by decide
  rcases family_descends (prefixWord ++ tailWord_337930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338017 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_338017 : Nat := 118140960795 + 338017 * 2 ^ 59
def prefixEnd_338017 : Nat := 4983230072969 + 3 ^ 40 * 338017 * 2
def baseEnd_338017 : Nat := 77140084618181884725775

theorem tailTrace_338017 : CollatzResearch.WordTrace tailWord_338017 prefixEnd_338017 77140084618181884725775 := by
  unfold tailWord_338017
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328492816429612552692305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8218995210953075035128203 12328492816429612552692305)
  ·
    refine ⟨9246369612322209414519229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12328492816429612552692305 9246369612322209414519229)
    ·
      refine ⟨3467388604620828530444711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9246369612322209414519229 3467388604620828530444711)
      ·
        refine ⟨5201082906931242795667067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467388604620828530444711 5201082906931242795667067)
        ·
          refine ⟨7801624360396864193500601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201082906931242795667067 7801624360396864193500601)
          ·
            refine ⟨5851218270297648145125451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801624360396864193500601 5851218270297648145125451)
            ·
              refine ⟨8776827405446472217688177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851218270297648145125451 8776827405446472217688177)
              ·
                refine ⟨6582620554084854163266133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8776827405446472217688177 6582620554084854163266133)
                ·
                  refine ⟨77140084618181884725775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6582620554084854163266133 77140084618181884725775)
                  ·
                    rfl

theorem cell21_338017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_338017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338017 prefixEnd_338017 := by exact prefixLift 338017
  have htrace : WordTrace (prefixWord ++ tailWord_338017) baseStart_338017 baseEnd_338017 := by
    simpa [prefixWord, tailWord_338017, baseEnd_338017] using wordTrace_append hprefix tailTrace_338017
  have hstable : (prefixWord ++ tailWord_338017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338017).length < 2 ^ (prefixWord ++ tailWord_338017).sum := by decide
  have hdescent : baseEnd_338017 < baseStart_338017 := by decide
  rcases family_descends (prefixWord ++ tailWord_338017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338051 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 4]
def baseStart_338051 : Nat := 118140960795 + 338051 * 2 ^ 59
def prefixEnd_338051 : Nat := 4983230072969 + 3 ^ 40 * 338051 * 2
def baseEnd_338051 : Nat := 77147843881405381159039

theorem tailTrace_338051 : CollatzResearch.WordTrace tailWord_338051 prefixEnd_338051 77147843881405381159039 := by
  unfold tailWord_338051
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329732898306436359430007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8219821932204290906286671 12329732898306436359430007)
  ·
    refine ⟨18494599347459654539145011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12329732898306436359430007 18494599347459654539145011)
    ·
      refine ⟨27741899021189481808717517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18494599347459654539145011 27741899021189481808717517)
      ·
        refine ⟨10403212132946055678269069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27741899021189481808717517 10403212132946055678269069)
        ·
          refine ⟨3901204549854770879350901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10403212132946055678269069 3901204549854770879350901)
          ·
            refine ⟨365737926548884769939147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3901204549854770879350901 365737926548884769939147)
            ·
              refine ⟨548606889823327154908721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365737926548884769939147 548606889823327154908721)
              ·
                refine ⟨411455167367495366181541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548606889823327154908721 411455167367495366181541)
                ·
                  refine ⟨77147843881405381159039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411455167367495366181541 77147843881405381159039)
                  ·
                    rfl

theorem cell21_338051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_338051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338051 prefixEnd_338051 := by exact prefixLift 338051
  have htrace : WordTrace (prefixWord ++ tailWord_338051) baseStart_338051 baseEnd_338051 := by
    simpa [prefixWord, tailWord_338051, baseEnd_338051] using wordTrace_append hprefix tailTrace_338051
  have hstable : (prefixWord ++ tailWord_338051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338051).length < 2 ^ (prefixWord ++ tailWord_338051).sum := by decide
  have hdescent : baseEnd_338051 < baseStart_338051 := by decide
  rcases family_descends (prefixWord ++ tailWord_338051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338082 : List Nat := [3, 3, 1, 3, 1, 1, 4, 5]
def baseStart_338082 : Nat := 118140960795 + 338082 * 2 ^ 59
def prefixEnd_338082 : Nat := 4983230072969 + 3 ^ 40 * 338082 * 2
def baseEnd_338082 : Nat := 25718306167918738714103

theorem tailTrace_338082 : CollatzResearch.WordTrace tailWord_338082 prefixEnd_338082 25718306167918738714103 := by
  unfold tailWord_338082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082715890298532163452125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8220575707462752435872333 3082715890298532163452125)
  ·
    refine ⟨1156018458861949561294547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3082715890298532163452125 1156018458861949561294547)
    ·
      refine ⟨1734027688292924341941821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156018458861949561294547 1734027688292924341941821)
      ·
        refine ⟨650260383109846628228183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1734027688292924341941821 650260383109846628228183)
        ·
          refine ⟨975390574664769942342275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650260383109846628228183 975390574664769942342275)
          ·
            refine ⟨1463085861997154913513413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975390574664769942342275 1463085861997154913513413)
            ·
              refine ⟨274328599124466546283765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1463085861997154913513413 274328599124466546283765)
              ·
                refine ⟨25718306167918738714103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274328599124466546283765 25718306167918738714103)
                ·
                  rfl

theorem cell21_338082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_338082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338082 prefixEnd_338082 := by exact prefixLift 338082
  have htrace : WordTrace (prefixWord ++ tailWord_338082) baseStart_338082 baseEnd_338082 := by
    simpa [prefixWord, tailWord_338082, baseEnd_338082] using wordTrace_append hprefix tailTrace_338082
  have hstable : (prefixWord ++ tailWord_338082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338082).length < 2 ^ (prefixWord ++ tailWord_338082).sum := by decide
  have hdescent : baseEnd_338082 < baseStart_338082 := by decide
  rcases family_descends (prefixWord ++ tailWord_338082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338141 : List Nat := [1, 4, 3, 2, 1, 1, 2, 7]
def baseStart_338141 : Nat := 118140960795 + 338141 * 2 ^ 59
def prefixEnd_338141 : Nat := 4983230072969 + 3 ^ 40 * 338141 * 2
def baseEnd_338141 : Nat := 25722794369195074886285

theorem tailTrace_338141 : CollatzResearch.WordTrace tailWord_338141 prefixEnd_338141 25722794369195074886285 := by
  unfold tailWord_338141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12333015467980381730206277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8222010311986921153470851 12333015467980381730206277)
  ·
    refine ⟨2312440400246321574413677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12333015467980381730206277 2312440400246321574413677)
    ·
      refine ⟨867165150092370590405129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2312440400246321574413677 867165150092370590405129)
      ·
        refine ⟨650373862569277942803847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867165150092370590405129 650373862569277942803847)
        ·
          refine ⟨975560793853916914205771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650373862569277942803847 975560793853916914205771)
          ·
            refine ⟨1463341190780875371308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975560793853916914205771 1463341190780875371308657)
            ·
              refine ⟨1097505893085656528481493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463341190780875371308657 1097505893085656528481493)
              ·
                refine ⟨25722794369195074886285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1097505893085656528481493 25722794369195074886285)
                ·
                  rfl

theorem cell21_338141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_338141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338141 prefixEnd_338141 := by exact prefixLift 338141
  have htrace : WordTrace (prefixWord ++ tailWord_338141) baseStart_338141 baseEnd_338141 := by
    simpa [prefixWord, tailWord_338141, baseEnd_338141] using wordTrace_append hprefix tailTrace_338141
  have hstable : (prefixWord ++ tailWord_338141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338141).length < 2 ^ (prefixWord ++ tailWord_338141).sum := by decide
  have hdescent : baseEnd_338141 < baseStart_338141 := by decide
  rcases family_descends (prefixWord ++ tailWord_338141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338186 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_338186 : Nat := 118140960795 + 338186 * 2 ^ 59
def prefixEnd_338186 : Nat := 4983230072969 + 3 ^ 40 * 338186 * 2
def baseEnd_338186 : Nat := 77178652720675146408763

theorem tailTrace_338186 : CollatzResearch.WordTrace tailWord_338186 prefixEnd_338186 77178652720675146408763 := by
  unfold tailWord_338186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083664188204338603898603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8223104501878236277062941 3083664188204338603898603)
  ·
    refine ⟨4625496282306507905847905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3083664188204338603898603 4625496282306507905847905)
    ·
      refine ⟨3469122211729880929385929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4625496282306507905847905 3469122211729880929385929)
      ·
        refine ⟨2601841658797410697039447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3469122211729880929385929 2601841658797410697039447)
        ·
          refine ⟨3902762488196116045559171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601841658797410697039447 3902762488196116045559171)
          ·
            refine ⟨5854143732294174068338757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902762488196116045559171 5854143732294174068338757)
            ·
              refine ⟨1097651949805157637813517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5854143732294174068338757 1097651949805157637813517)
              ·
                refine ⟨411619481176934114180069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1097651949805157637813517 411619481176934114180069)
                ·
                  refine ⟨77178652720675146408763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411619481176934114180069 77178652720675146408763)
                  ·
                    rfl

theorem cell21_338186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_338186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338186 prefixEnd_338186 := by exact prefixLift 338186
  have htrace : WordTrace (prefixWord ++ tailWord_338186) baseStart_338186 baseEnd_338186 := by
    simpa [prefixWord, tailWord_338186, baseEnd_338186] using wordTrace_append hprefix tailTrace_338186
  have hstable : (prefixWord ++ tailWord_338186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338186).length < 2 ^ (prefixWord ++ tailWord_338186).sum := by decide
  have hdescent : baseEnd_338186 < baseStart_338186 := by decide
  rcases family_descends (prefixWord ++ tailWord_338186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
