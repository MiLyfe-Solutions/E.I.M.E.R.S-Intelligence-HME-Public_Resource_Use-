import V185TrunkScan22Chunk131

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1179631 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1179631 : Nat := 118140960795 + 1179631 * 2 ^ 59
def prefixEnd_1179631 : Nat := 4983230072969 + 3 ^ 40 * 1179631 * 2
def baseEnd_1179631 : Nat := 403811798629319614658321

theorem tailTrace_1179631 : CollatzResearch.WordTrace tailWord_1179631 prefixEnd_1179631 403811798629319614658321 := by
  unfold tailWord_1179631
  simp only [CollatzResearch.WordTrace]
  refine ⟨43024677189405826780466747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28683118126270551186977831 43024677189405826780466747)
  ·
    refine ⟨64537015784108740170700121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43024677189405826780466747 64537015784108740170700121)
    ·
      refine ⟨48402761838081555128025091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64537015784108740170700121 48402761838081555128025091)
      ·
        refine ⟨72604142757122332692037637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48402761838081555128025091 72604142757122332692037637)
        ·
          refine ⟨13613276766960437379757057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72604142757122332692037637 13613276766960437379757057)
          ·
            refine ⟨10209957575220328034817793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13613276766960437379757057 10209957575220328034817793)
            ·
              refine ⟨7657468181415246026113345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10209957575220328034817793 7657468181415246026113345)
              ·
                refine ⟨5743101136061434519585009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7657468181415246026113345 5743101136061434519585009)
                ·
                  refine ⟨4307325852046075889688757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743101136061434519585009 4307325852046075889688757)
                  ·
                    refine ⟨403811798629319614658321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4307325852046075889688757 403811798629319614658321)
                    ·
                      rfl

theorem cell22_1179631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1179631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179631 prefixEnd_1179631 := by exact prefixLift 1179631
  have htrace : WordTrace (prefixWord ++ tailWord_1179631) baseStart_1179631 baseEnd_1179631 := by
    simpa [prefixWord, tailWord_1179631, baseEnd_1179631] using wordTrace_append hprefix tailTrace_1179631
  have hstable : (prefixWord ++ tailWord_1179631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179631).length < 2 ^ (prefixWord ++ tailWord_1179631).sum := by decide
  have hdescent : baseEnd_1179631 < baseStart_1179631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179706 : List Nat := [3, 1, 1, 1, 3, 1, 1, 11]
def baseStart_1179706 : Nat := 118140960795 + 1179706 * 2 ^ 59
def prefixEnd_1179706 : Nat := 4983230072969 + 3 ^ 40 * 1179706 * 2
def baseEnd_1179706 : Nat := 44870830295782713225899

theorem tailTrace_1179706 : CollatzResearch.WordTrace tailWord_1179706 prefixEnd_1179706 44870830295782713225899 := by
  unfold tailWord_1179706
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756853166033528647361743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28684941776089409726297981 10756853166033528647361743)
  ·
    refine ⟨16135279749050292971042615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10756853166033528647361743 16135279749050292971042615)
    ·
      refine ⟨24202919623575439456563923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16135279749050292971042615 24202919623575439456563923)
      ·
        refine ⟨36304379435363159184845885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24202919623575439456563923 36304379435363159184845885)
        ·
          refine ⟨13614142288261184694317207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36304379435363159184845885 13614142288261184694317207)
          ·
            refine ⟨20421213432391777041475811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13614142288261184694317207 20421213432391777041475811)
            ·
              refine ⟨30631820148587665562213717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20421213432391777041475811 30631820148587665562213717)
              ·
                refine ⟨44870830295782713225899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 30631820148587665562213717 44870830295782713225899)
                ·
                  rfl

theorem cell22_1179706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_1179706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179706 prefixEnd_1179706 := by exact prefixLift 1179706
  have htrace : WordTrace (prefixWord ++ tailWord_1179706) baseStart_1179706 baseEnd_1179706 := by
    simpa [prefixWord, tailWord_1179706, baseEnd_1179706] using wordTrace_append hprefix tailTrace_1179706
  have hstable : (prefixWord ++ tailWord_1179706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179706).length < 2 ^ (prefixWord ++ tailWord_1179706).sum := by decide
  have hdescent : baseEnd_1179706 < baseStart_1179706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179721 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1179721 : Nat := 118140960795 + 1179721 * 2 ^ 59
def prefixEnd_1179721 : Nat := 4983230072969 + 3 ^ 40 * 1179721 * 2
def baseEnd_1179721 : Nat := 403842607468589379908045

theorem tailTrace_1179721 : CollatzResearch.WordTrace tailWord_1179721 prefixEnd_1179721 403842607468589379908045 := by
  unfold tailWord_1179721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43027959759079772151243017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28685306506053181434162011 43027959759079772151243017)
  ·
    refine ⟨32270969819309829113432263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43027959759079772151243017 32270969819309829113432263)
    ·
      refine ⟨48406454728964743670148395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32270969819309829113432263 48406454728964743670148395)
      ·
        refine ⟨72609682093447115505222593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48406454728964743670148395 72609682093447115505222593)
        ·
          refine ⟨54457261570085336628916945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72609682093447115505222593 54457261570085336628916945)
          ·
            refine ⟨40842946177564002471687709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54457261570085336628916945 40842946177564002471687709)
            ·
              refine ⟨15316104816586500926882891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40842946177564002471687709 15316104816586500926882891)
              ·
                refine ⟨22974157224879751390324337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15316104816586500926882891 22974157224879751390324337)
                ·
                  refine ⟨17230617918659813542743253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22974157224879751390324337 17230617918659813542743253)
                  ·
                    refine ⟨403842607468589379908045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17230617918659813542743253 403842607468589379908045)
                    ·
                      rfl

theorem cell22_1179721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1179721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179721 prefixEnd_1179721 := by exact prefixLift 1179721
  have htrace : WordTrace (prefixWord ++ tailWord_1179721) baseStart_1179721 baseEnd_1179721 := by
    simpa [prefixWord, tailWord_1179721, baseEnd_1179721] using wordTrace_append hprefix tailTrace_1179721
  have hstable : (prefixWord ++ tailWord_1179721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179721).length < 2 ^ (prefixWord ++ tailWord_1179721).sum := by decide
  have hdescent : baseEnd_1179721 < baseStart_1179721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179725 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1179725 : Nat := 118140960795 + 1179725 * 2 ^ 59
def prefixEnd_1179725 : Nat := 4983230072969 + 3 ^ 40 * 1179725 * 2
def baseEnd_1179725 : Nat := 403843976750334702808033

theorem tailTrace_1179725 : CollatzResearch.WordTrace tailWord_1179725 prefixEnd_1179725 403843976750334702808033 := by
  unfold tailWord_1179725
  simp only [CollatzResearch.WordTrace]
  refine ⟨43028105651065280834388629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28685403767376853889592419 43028105651065280834388629)
  ·
    refine ⟨2016942452393685039111967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43028105651065280834388629 2016942452393685039111967)
    ·
      refine ⟨3025413678590527558667951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016942452393685039111967 3025413678590527558667951)
      ·
        refine ⟨4538120517885791338001927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025413678590527558667951 4538120517885791338001927)
        ·
          refine ⟨6807180776828687007002891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538120517885791338001927 6807180776828687007002891)
          ·
            refine ⟨10210771165243030510504337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807180776828687007002891 10210771165243030510504337)
            ·
              refine ⟨7658078373932272882878253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10210771165243030510504337 7658078373932272882878253)
              ·
                refine ⟨2871779390224602331079345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7658078373932272882878253 2871779390224602331079345)
                ·
                  refine ⟨2153834542668451748309509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871779390224602331079345 2153834542668451748309509)
                  ·
                    refine ⟨403843976750334702808033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153834542668451748309509 403843976750334702808033)
                    ·
                      rfl

theorem cell22_1179725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1179725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179725 prefixEnd_1179725 := by exact prefixLift 1179725
  have htrace : WordTrace (prefixWord ++ tailWord_1179725) baseStart_1179725 baseEnd_1179725 := by
    simpa [prefixWord, tailWord_1179725, baseEnd_1179725] using wordTrace_append hprefix tailTrace_1179725
  have hstable : (prefixWord ++ tailWord_1179725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179725).length < 2 ^ (prefixWord ++ tailWord_1179725).sum := by decide
  have hdescent : baseEnd_1179725 < baseStart_1179725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179802 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_1179802 : Nat := 118140960795 + 1179802 * 2 ^ 59
def prefixEnd_1179802 : Nat := 4983230072969 + 3 ^ 40 * 1179802 * 2
def baseEnd_1179802 : Nat := 134623445141310722877599

theorem tailTrace_1179802 : CollatzResearch.WordTrace tailWord_1179802 prefixEnd_1179802 134623445141310722877599 := by
  unfold tailWord_1179802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757728517946580746235415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28687276047857548656627773 10757728517946580746235415)
  ·
    refine ⟨16136592776919871119353123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10757728517946580746235415 16136592776919871119353123)
    ·
      refine ⟨24204889165379806679029685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16136592776919871119353123 24204889165379806679029685)
      ·
        refine ⟨2269208359254356876159033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24204889165379806679029685 2269208359254356876159033)
        ·
          refine ⟨1701906269440767657119275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2269208359254356876159033 1701906269440767657119275)
          ·
            refine ⟨2552859404161151485678913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701906269440767657119275 2552859404161151485678913)
            ·
              refine ⟨1914644553120863614259185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552859404161151485678913 1914644553120863614259185)
              ·
                refine ⟨1435983414840647710694389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914644553120863614259185 1435983414840647710694389)
                ·
                  refine ⟨134623445141310722877599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1435983414840647710694389 134623445141310722877599)
                  ·
                    rfl

theorem cell22_1179802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_1179802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179802 prefixEnd_1179802 := by exact prefixLift 1179802
  have htrace : WordTrace (prefixWord ++ tailWord_1179802) baseStart_1179802 baseEnd_1179802 := by
    simpa [prefixWord, tailWord_1179802, baseEnd_1179802] using wordTrace_append hprefix tailTrace_1179802
  have hstable : (prefixWord ++ tailWord_1179802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179802).length < 2 ^ (prefixWord ++ tailWord_1179802).sum := by decide
  have hdescent : baseEnd_1179802 < baseStart_1179802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179806 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1179806 : Nat := 118140960795 + 1179806 * 2 ^ 59
def prefixEnd_1179806 : Nat := 4983230072969 + 3 ^ 40 * 1179806 * 2
def baseEnd_1179806 : Nat := 403871704705677491532785

theorem tailTrace_1179806 : CollatzResearch.WordTrace tailWord_1179806 prefixEnd_1179806 403871704705677491532785 := by
  unfold tailWord_1179806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378882495471478958510909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28687373309181221112058181 5378882495471478958510909)
  ·
    refine ⟨2017080935801804609441591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5378882495471478958510909 2017080935801804609441591)
    ·
      refine ⟨3025621403702706914162387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2017080935801804609441591 3025621403702706914162387)
      ·
        refine ⟨4538432105554060371243581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025621403702706914162387 4538432105554060371243581)
        ·
          refine ⟨1701912039582772639216343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4538432105554060371243581 1701912039582772639216343)
          ·
            refine ⟨2552868059374158958824515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701912039582772639216343 2552868059374158958824515)
            ·
              refine ⟨3829302089061238438236773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552868059374158958824515 3829302089061238438236773)
              ·
                refine ⟨717994141698982207169395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3829302089061238438236773 717994141698982207169395)
                ·
                  refine ⟨1076991212548473310754093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717994141698982207169395 1076991212548473310754093)
                  ·
                    refine ⟨403871704705677491532785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1076991212548473310754093 403871704705677491532785)
                    ·
                      rfl

theorem cell22_1179806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1179806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179806 prefixEnd_1179806 := by exact prefixLift 1179806
  have htrace : WordTrace (prefixWord ++ tailWord_1179806) baseStart_1179806 baseEnd_1179806 := by
    simpa [prefixWord, tailWord_1179806, baseEnd_1179806] using wordTrace_append hprefix tailTrace_1179806
  have hstable : (prefixWord ++ tailWord_1179806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179806).length < 2 ^ (prefixWord ++ tailWord_1179806).sum := by decide
  have hdescent : baseEnd_1179806 < baseStart_1179806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179813 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 6]
def baseStart_1179813 : Nat := 118140960795 + 1179813 * 2 ^ 59
def prefixEnd_1179813 : Nat := 4983230072969 + 3 ^ 40 * 1179813 * 2
def baseEnd_1179813 : Nat := 134624700316243935535921

theorem tailTrace_1179813 : CollatzResearch.WordTrace tailWord_1179813 prefixEnd_1179813 134624700316243935535921 := by
  unfold tailWord_1179813
  simp only [CollatzResearch.WordTrace]
  refine ⟨43031315274746471863592093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28687543516497647909061395 43031315274746471863592093)
  ·
    refine ⟨16136743228029926948847035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43031315274746471863592093 16136743228029926948847035)
    ·
      refine ⟨24205114842044890423270553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16136743228029926948847035 24205114842044890423270553)
      ·
        refine ⟨18153836131533667817452915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24205114842044890423270553 18153836131533667817452915)
        ·
          refine ⟨27230754197300501726179373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18153836131533667817452915 27230754197300501726179373)
          ·
            refine ⟨10211532823987688147317265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27230754197300501726179373 10211532823987688147317265)
            ·
              refine ⟨7658649617990766110487949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10211532823987688147317265 7658649617990766110487949)
              ·
                refine ⟨2871993606746537291432981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7658649617990766110487949 2871993606746537291432981)
                ·
                  refine ⟨134624700316243935535921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2871993606746537291432981 134624700316243935535921)
                  ·
                    rfl

theorem cell22_1179813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_1179813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179813 prefixEnd_1179813 := by exact prefixLift 1179813
  have htrace : WordTrace (prefixWord ++ tailWord_1179813) baseStart_1179813 baseEnd_1179813 := by
    simpa [prefixWord, tailWord_1179813, baseEnd_1179813] using wordTrace_append hprefix tailTrace_1179813
  have hstable : (prefixWord ++ tailWord_1179813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179813).length < 2 ^ (prefixWord ++ tailWord_1179813).sum := by decide
  have hdescent : baseEnd_1179813 < baseStart_1179813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179888 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1179888 : Nat := 118140960795 + 1179888 * 2 ^ 59
def prefixEnd_1179888 : Nat := 4983230072969 + 3 ^ 40 * 1179888 * 2
def baseEnd_1179888 : Nat := 403899774981456610982533

theorem tailTrace_1179888 : CollatzResearch.WordTrace tailWord_1179888 prefixEnd_1179888 403899774981456610982533 := by
  unfold tailWord_1179888
  simp only [CollatzResearch.WordTrace]
  refine ⟨21517025374737379836286159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28689367166316506448381545 21517025374737379836286159)
  ·
    refine ⟨32275538062106069754429239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21517025374737379836286159 32275538062106069754429239)
    ·
      refine ⟨48413307093159104631643859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32275538062106069754429239 48413307093159104631643859)
      ·
        refine ⟨72619960639738656947465789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48413307093159104631643859 72619960639738656947465789)
        ·
          refine ⟨27232485239901996355299671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72619960639738656947465789 27232485239901996355299671)
          ·
            refine ⟨40848727859852994532949507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27232485239901996355299671 40848727859852994532949507)
            ·
              refine ⟨61273091789779491799424261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40848727859852994532949507 61273091789779491799424261)
              ·
                refine ⟨11488704710583654712392049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61273091789779491799424261 11488704710583654712392049)
                ·
                  refine ⟨8616528532937741034294037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11488704710583654712392049 8616528532937741034294037)
                  ·
                    refine ⟨403899774981456610982533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8616528532937741034294037 403899774981456610982533)
                    ·
                      rfl

theorem cell22_1179888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1179888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179888 prefixEnd_1179888 := by exact prefixLift 1179888
  have htrace : WordTrace (prefixWord ++ tailWord_1179888) baseStart_1179888 baseEnd_1179888 := by
    simpa [prefixWord, tailWord_1179888, baseEnd_1179888] using wordTrace_append hprefix tailTrace_1179888
  have hstable : (prefixWord ++ tailWord_1179888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179888).length < 2 ^ (prefixWord ++ tailWord_1179888).sum := by decide
  have hdescent : baseEnd_1179888 < baseStart_1179888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179903 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 9]
def baseStart_1179903 : Nat := 118140960795 + 1179903 * 2 ^ 59
def prefixEnd_1179903 : Nat := 4983230072969 + 3 ^ 40 * 1179903 * 2
def baseEnd_1179903 : Nat := 134634969929333857285829

theorem tailTrace_1179903 : CollatzResearch.WordTrace tailWord_1179903 prefixEnd_1179903 134634969929333857285829 := by
  unfold tailWord_1179903
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034597844420417234368363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28689731896280278156245575 43034597844420417234368363)
  ·
    refine ⟨64551896766630625851552545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43034597844420417234368363 64551896766630625851552545)
    ·
      refine ⟨48413922574972969388664409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64551896766630625851552545 48413922574972969388664409)
      ·
        refine ⟨36310441931229727041498307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48413922574972969388664409 36310441931229727041498307)
        ·
          refine ⟨54465662896844590562247461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36310441931229727041498307 54465662896844590562247461)
          ·
            refine ⟨10212311793158360730421399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54465662896844590562247461 10212311793158360730421399)
            ·
              refine ⟨15318467689737541095632099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10212311793158360730421399 15318467689737541095632099)
              ·
                refine ⟨22977701534606311643448149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15318467689737541095632099 22977701534606311643448149)
                ·
                  refine ⟨134634969929333857285829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22977701534606311643448149 134634969929333857285829)
                  ·
                    rfl

theorem cell22_1179903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_1179903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179903 prefixEnd_1179903 := by exact prefixLift 1179903
  have htrace : WordTrace (prefixWord ++ tailWord_1179903) baseStart_1179903 baseEnd_1179903 := by
    simpa [prefixWord, tailWord_1179903, baseEnd_1179903] using wordTrace_append hprefix tailTrace_1179903
  have hstable : (prefixWord ++ tailWord_1179903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179903).length < 2 ^ (prefixWord ++ tailWord_1179903).sum := by decide
  have hdescent : baseEnd_1179903 < baseStart_1179903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179937 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 5]
def baseStart_1179937 : Nat := 118140960795 + 1179937 * 2 ^ 59
def prefixEnd_1179937 : Nat := 4983230072969 + 3 ^ 40 * 1179937 * 2
def baseEnd_1179937 : Nat := 134638849560945605502461

theorem tailTrace_1179937 : CollatzResearch.WordTrace tailWord_1179937 prefixEnd_1179937 134638849560945605502461 := by
  unfold tailWord_1179937
  simp only [CollatzResearch.WordTrace]
  refine ⟨43035837926297241041106065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28690558617531494027404043 43035837926297241041106065)
  ·
    refine ⟨32276878444722930780829549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43035837926297241041106065 32276878444722930780829549)
    ·
      refine ⟨12103829416771099042811081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32276878444722930780829549 12103829416771099042811081)
      ·
        refine ⟨9077872062578324282108311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12103829416771099042811081 9077872062578324282108311)
        ·
          refine ⟨13616808093867486423162467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9077872062578324282108311 13616808093867486423162467)
          ·
            refine ⟨20425212140801229634743701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13616808093867486423162467 20425212140801229634743701)
            ·
              refine ⟨957431819100057639128611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20425212140801229634743701 957431819100057639128611)
              ·
                refine ⟨1436147728650086458692917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957431819100057639128611 1436147728650086458692917)
                ·
                  refine ⟨134638849560945605502461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436147728650086458692917 134638849560945605502461)
                  ·
                    rfl

theorem cell22_1179937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_1179937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179937 prefixEnd_1179937 := by exact prefixLift 1179937
  have htrace : WordTrace (prefixWord ++ tailWord_1179937) baseStart_1179937 baseEnd_1179937 := by
    simpa [prefixWord, tailWord_1179937, baseEnd_1179937] using wordTrace_append hprefix tailTrace_1179937
  have hstable : (prefixWord ++ tailWord_1179937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179937).length < 2 ^ (prefixWord ++ tailWord_1179937).sum := by decide
  have hdescent : baseEnd_1179937 < baseStart_1179937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179980 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1179980 : Nat := 118140960795 + 1179980 * 2 ^ 59
def prefixEnd_1179980 : Nat := 4983230072969 + 3 ^ 40 * 1179980 * 2
def baseEnd_1179980 : Nat := 403931268461599037682251

theorem tailTrace_1179980 : CollatzResearch.WordTrace tailWord_1179980 prefixEnd_1179980 403931268461599037682251 := by
  unfold tailWord_1179980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518703132570729692460697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28691604176760972923280929 21518703132570729692460697)
  ·
    refine ⟨16139027349428047269345523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21518703132570729692460697 16139027349428047269345523)
    ·
      refine ⟨24208541024142070904018285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16139027349428047269345523 24208541024142070904018285)
      ·
        refine ⟨9078202884053276589006857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24208541024142070904018285 9078202884053276589006857)
        ·
          refine ⟨6808652163039957441755143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9078202884053276589006857 6808652163039957441755143)
          ·
            refine ⟨10212978244559936162632715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808652163039957441755143 10212978244559936162632715)
            ·
              refine ⟨15319467366839904243949073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10212978244559936162632715 15319467366839904243949073)
              ·
                refine ⟨11489600525129928182961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15319467366839904243949073 11489600525129928182961805)
                ·
                  refine ⟨4308600196923723068610677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11489600525129928182961805 4308600196923723068610677)
                  ·
                    refine ⟨403931268461599037682251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4308600196923723068610677 403931268461599037682251)
                    ·
                      rfl

theorem cell22_1179980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1179980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1179980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1179980 prefixEnd_1179980 := by exact prefixLift 1179980
  have htrace : WordTrace (prefixWord ++ tailWord_1179980) baseStart_1179980 baseEnd_1179980 := by
    simpa [prefixWord, tailWord_1179980, baseEnd_1179980] using wordTrace_append hprefix tailTrace_1179980
  have hstable : (prefixWord ++ tailWord_1179980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179980).length < 2 ^ (prefixWord ++ tailWord_1179980).sum := by decide
  have hdescent : baseEnd_1179980 < baseStart_1179980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180012 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1180012 : Nat := 118140960795 + 1180012 * 2 ^ 59
def prefixEnd_1180012 : Nat := 4983230072969 + 3 ^ 40 * 1180012 * 2
def baseEnd_1180012 : Nat := 403942222715561620882153

theorem tailTrace_1180012 : CollatzResearch.WordTrace tailWord_1180012 prefixEnd_1180012 403942222715561620882153 := by
  unfold tailWord_1180012
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519286700512764425043145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28692382267350352566724193 21519286700512764425043145)
  ·
    refine ⟨16139465025384573318782359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21519286700512764425043145 16139465025384573318782359)
    ·
      refine ⟨24209197538076859978173539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16139465025384573318782359 24209197538076859978173539)
      ·
        refine ⟨36313796307115289967260309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24209197538076859978173539 36313796307115289967260309)
        ·
          refine ⟨1702209201896029217215327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36313796307115289967260309 1702209201896029217215327)
          ·
            refine ⟨2553313802844043825822991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702209201896029217215327 2553313802844043825822991)
            ·
              refine ⟨3829970704266065738734487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553313802844043825822991 3829970704266065738734487)
              ·
                refine ⟨5744956056399098608101731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829970704266065738734487 5744956056399098608101731)
                ·
                  refine ⟨8617434084598647912152597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744956056399098608101731 8617434084598647912152597)
                  ·
                    refine ⟨403942222715561620882153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8617434084598647912152597 403942222715561620882153)
                    ·
                      rfl

theorem cell22_1180012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1180012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180012 prefixEnd_1180012 := by exact prefixLift 1180012
  have htrace : WordTrace (prefixWord ++ tailWord_1180012) baseStart_1180012 baseEnd_1180012 := by
    simpa [prefixWord, tailWord_1180012, baseEnd_1180012] using wordTrace_append hprefix tailTrace_1180012
  have hstable : (prefixWord ++ tailWord_1180012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180012).length < 2 ^ (prefixWord ++ tailWord_1180012).sum := by decide
  have hdescent : baseEnd_1180012 < baseStart_1180012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180061 : List Nat := [1, 4, 2, 1, 5, 1, 2, 6]
def baseStart_1180061 : Nat := 118140960795 + 1180061 * 2 ^ 59
def prefixEnd_1180061 : Nat := 4983230072969 + 3 ^ 40 * 1180061 * 2
def baseEnd_1180061 : Nat := 44884332935215758489667

theorem tailTrace_1180061 : CollatzResearch.WordTrace tailWord_1180061 prefixEnd_1180061 44884332935215758489667 := by
  unfold tailWord_1180061
  simp only [CollatzResearch.WordTrace]
  refine ⟨43040360577848010218620037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28693573718565340145746691 43040360577848010218620037)
  ·
    refine ⟨8070067608346501915991257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43040360577848010218620037 8070067608346501915991257)
    ·
      refine ⟨6052550706259876436993443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8070067608346501915991257 6052550706259876436993443)
      ·
        refine ⟨9078826059389814655490165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052550706259876436993443 9078826059389814655490165)
        ·
          refine ⟨851139943067795123952203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9078826059389814655490165 851139943067795123952203)
          ·
            refine ⟨1276709914601692685928305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851139943067795123952203 1276709914601692685928305)
            ·
              refine ⟨957532435951269514446229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276709914601692685928305 957532435951269514446229)
              ·
                refine ⟨44884332935215758489667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 957532435951269514446229 44884332935215758489667)
                ·
                  rfl

theorem cell22_1180061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 6].length) (baseStart_1180061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180061 prefixEnd_1180061 := by exact prefixLift 1180061
  have htrace : WordTrace (prefixWord ++ tailWord_1180061) baseStart_1180061 baseEnd_1180061 := by
    simpa [prefixWord, tailWord_1180061, baseEnd_1180061] using wordTrace_append hprefix tailTrace_1180061
  have hstable : (prefixWord ++ tailWord_1180061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180061).length < 2 ^ (prefixWord ++ tailWord_1180061).sum := by decide
  have hdescent : baseEnd_1180061 < baseStart_1180061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180093 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_1180093 : Nat := 118140960795 + 1180093 * 2 ^ 59
def prefixEnd_1180093 : Nat := 4983230072969 + 3 ^ 40 * 1180093 * 2
def baseEnd_1180093 : Nat := 403969950670904409606905

theorem tailTrace_1180093 : CollatzResearch.WordTrace tailWord_1180093 prefixEnd_1180093 403969950670904409606905 := by
  unfold tailWord_1180093
  simp only [CollatzResearch.WordTrace]
  refine ⟨43041527713732079683784933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28694351809154719789189955 43041527713732079683784933)
  ·
    refine ⟨8070286446324764940709675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43041527713732079683784933 8070286446324764940709675)
    ·
      refine ⟨12105429669487147411064513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070286446324764940709675 12105429669487147411064513)
      ·
        refine ⟨9079072252115360558298385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12105429669487147411064513 9079072252115360558298385)
        ·
          refine ⟨6809304189086520418723789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9079072252115360558298385 6809304189086520418723789)
          ·
            refine ⟨2553489070907445157021421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6809304189086520418723789 2553489070907445157021421)
            ·
              refine ⟨957558401590291933883033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2553489070907445157021421 957558401590291933883033)
              ·
                refine ⟨718168801192718950412275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957558401590291933883033 718168801192718950412275)
                ·
                  refine ⟨1077253201789078425618413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718168801192718950412275 1077253201789078425618413)
                  ·
                    refine ⟨403969950670904409606905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077253201789078425618413 403969950670904409606905)
                    ·
                      rfl

theorem cell22_1180093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_1180093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180093 prefixEnd_1180093 := by exact prefixLift 1180093
  have htrace : WordTrace (prefixWord ++ tailWord_1180093) baseStart_1180093 baseEnd_1180093 := by
    simpa [prefixWord, tailWord_1180093, baseEnd_1180093] using wordTrace_append hprefix tailTrace_1180093
  have hstable : (prefixWord ++ tailWord_1180093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180093).length < 2 ^ (prefixWord ++ tailWord_1180093).sum := by decide
  have hdescent : baseEnd_1180093 < baseStart_1180093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180136 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1180136 : Nat := 118140960795 + 1180136 * 2 ^ 59
def prefixEnd_1180136 : Nat := 4983230072969 + 3 ^ 40 * 1180136 * 2
def baseEnd_1180136 : Nat := 403984670449666630781773

theorem tailTrace_1180136 : CollatzResearch.WordTrace tailWord_1180136 prefixEnd_1180136 403984670449666630781773 := by
  unfold tailWord_1180136
  simp only [CollatzResearch.WordTrace]
  refine ⟨21521548026288149013800131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28695397368384198685066841 21521548026288149013800131)
  ·
    refine ⟨32282322039432223520700197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21521548026288149013800131 32282322039432223520700197)
    ·
      refine ⟨6052935382393541910131287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32282322039432223520700197 6052935382393541910131287)
      ·
        refine ⟨9079403073590312865196931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052935382393541910131287 9079403073590312865196931)
        ·
          refine ⟨13619104610385469297795397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079403073590312865196931 13619104610385469297795397)
          ·
            refine ⟨2553582114447275493336637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13619104610385469297795397 2553582114447275493336637)
            ·
              refine ⟨957593292917728310001239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2553582114447275493336637 957593292917728310001239)
              ·
                refine ⟨1436389939376592465001859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957593292917728310001239 1436389939376592465001859)
                ·
                  refine ⟨2154584909064888697502789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436389939376592465001859 2154584909064888697502789)
                  ·
                    refine ⟨403984670449666630781773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154584909064888697502789 403984670449666630781773)
                    ·
                      rfl

theorem cell22_1180136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1180136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180136 prefixEnd_1180136 := by exact prefixLift 1180136
  have htrace : WordTrace (prefixWord ++ tailWord_1180136) baseStart_1180136 baseEnd_1180136 := by
    simpa [prefixWord, tailWord_1180136, baseEnd_1180136] using wordTrace_append hprefix tailTrace_1180136
  have hstable : (prefixWord ++ tailWord_1180136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180136).length < 2 ^ (prefixWord ++ tailWord_1180136).sum := by decide
  have hdescent : baseEnd_1180136 < baseStart_1180136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180147 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_1180147 : Nat := 118140960795 + 1180147 * 2 ^ 59
def prefixEnd_1180147 : Nat := 4983230072969 + 3 ^ 40 * 1180147 * 2
def baseEnd_1180147 : Nat := 403988435974466268756739

theorem tailTrace_1180147 : CollatzResearch.WordTrace tailWord_1180147 prefixEnd_1180147 403988435974466268756739 := by
  unfold tailWord_1180147
  simp only [CollatzResearch.WordTrace]
  refine ⟨43043497255536446906250695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28695664837024297937500463 43043497255536446906250695)
  ·
    refine ⟨64565245883304670359376043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43043497255536446906250695 64565245883304670359376043)
    ·
      refine ⟨96847868824957005539064065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64565245883304670359376043 96847868824957005539064065)
      ·
        refine ⟨72635901618717754154298049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96847868824957005539064065 72635901618717754154298049)
        ·
          refine ⟨54476926214038315615723537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72635901618717754154298049 54476926214038315615723537)
          ·
            refine ⟨40857694660528736711792653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54476926214038315615723537 40857694660528736711792653)
            ·
              refine ⟨15321635497698276266922245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40857694660528736711792653 15321635497698276266922245)
              ·
                refine ⟨2872806655818426800047921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15321635497698276266922245 2872806655818426800047921)
                ·
                  refine ⟨2154604991863820100035941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872806655818426800047921 2154604991863820100035941)
                  ·
                    refine ⟨403988435974466268756739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154604991863820100035941 403988435974466268756739)
                    ·
                      rfl

theorem cell22_1180147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_1180147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180147 prefixEnd_1180147 := by exact prefixLift 1180147
  have htrace : WordTrace (prefixWord ++ tailWord_1180147) baseStart_1180147 baseEnd_1180147 := by
    simpa [prefixWord, tailWord_1180147, baseEnd_1180147] using wordTrace_append hprefix tailTrace_1180147
  have hstable : (prefixWord ++ tailWord_1180147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180147).length < 2 ^ (prefixWord ++ tailWord_1180147).sum := by decide
  have hdescent : baseEnd_1180147 < baseStart_1180147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180194 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1180194 : Nat := 118140960795 + 1180194 * 2 ^ 59
def prefixEnd_1180194 : Nat := 4983230072969 + 3 ^ 40 * 1180194 * 2
def baseEnd_1180194 : Nat := 404004525034973812831595

theorem tailTrace_1180194 : CollatzResearch.WordTrace tailWord_1180194 prefixEnd_1180194 404004525034973812831595 := by
  unfold tailWord_1180194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761302871591543483302909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28696807657577449288807757 10761302871591543483302909)
  ·
    refine ⟨4035488576846828806238591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10761302871591543483302909 4035488576846828806238591)
    ·
      refine ⟨6053232865270243209357887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035488576846828806238591 6053232865270243209357887)
      ·
        refine ⟨9079849297905364814036831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6053232865270243209357887 9079849297905364814036831)
        ·
          refine ⟨13619773946858047221055247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079849297905364814036831 13619773946858047221055247)
          ·
            refine ⟨20429660920287070831582871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13619773946858047221055247 20429660920287070831582871)
            ·
              refine ⟨30644491380430606247374307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20429660920287070831582871 30644491380430606247374307)
              ·
                refine ⟨45966737070645909371061461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30644491380430606247374307 45966737070645909371061461)
                ·
                  refine ⟨1077345400093263500884253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 45966737070645909371061461 1077345400093263500884253)
                  ·
                    refine ⟨404004525034973812831595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077345400093263500884253 404004525034973812831595)
                    ·
                      rfl

theorem cell22_1180194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1180194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180194 prefixEnd_1180194 := by exact prefixLift 1180194
  have htrace : WordTrace (prefixWord ++ tailWord_1180194) baseStart_1180194 baseEnd_1180194 := by
    simpa [prefixWord, tailWord_1180194, baseEnd_1180194] using wordTrace_append hprefix tailTrace_1180194
  have hstable : (prefixWord ++ tailWord_1180194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180194).length < 2 ^ (prefixWord ++ tailWord_1180194).sum := by decide
  have hdescent : baseEnd_1180194 < baseStart_1180194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180211 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 1, 3]
def baseStart_1180211 : Nat := 118140960795 + 1180211 * 2 ^ 59
def prefixEnd_1180211 : Nat := 4983230072969 + 3 ^ 40 * 1180211 * 2
def baseEnd_1180211 : Nat := 404010344482391435156543

theorem tailTrace_1180211 : CollatzResearch.WordTrace tailWord_1180211 prefixEnd_1180211 404010344482391435156543 := by
  unfold tailWord_1180211
  simp only [CollatzResearch.WordTrace]
  refine ⟨43045831527304585836580487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28697221018203057224386991 43045831527304585836580487)
  ·
    refine ⟨64568747290956878754870731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43045831527304585836580487 64568747290956878754870731)
    ·
      refine ⟨96853120936435318132306097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64568747290956878754870731 96853120936435318132306097)
      ·
        refine ⟨72639840702326488599229573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96853120936435318132306097 72639840702326488599229573)
        ·
          refine ⟨13619970131686216612355545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72639840702326488599229573 13619970131686216612355545)
          ·
            refine ⟨10214977598764662459266659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13619970131686216612355545 10214977598764662459266659)
            ·
              refine ⟨15322466398146993688899989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10214977598764662459266659 15322466398146993688899989)
              ·
                refine ⟨718240612413140329167187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15322466398146993688899989 718240612413140329167187)
                ·
                  refine ⟨1077360918619710493750781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718240612413140329167187 1077360918619710493750781)
                  ·
                    refine ⟨404010344482391435156543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077360918619710493750781 404010344482391435156543)
                    ·
                      rfl

theorem cell22_1180211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 3].length) (baseStart_1180211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180211 prefixEnd_1180211 := by exact prefixLift 1180211
  have htrace : WordTrace (prefixWord ++ tailWord_1180211) baseStart_1180211 baseEnd_1180211 := by
    simpa [prefixWord, tailWord_1180211, baseEnd_1180211] using wordTrace_append hprefix tailTrace_1180211
  have hstable : (prefixWord ++ tailWord_1180211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180211).length < 2 ^ (prefixWord ++ tailWord_1180211).sum := by decide
  have hdescent : baseEnd_1180211 < baseStart_1180211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180267 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_1180267 : Nat := 118140960795 + 1180267 * 2 ^ 59
def prefixEnd_1180267 : Nat := 4983230072969 + 3 ^ 40 * 1180267 * 2
def baseEnd_1180267 : Nat := 404029514426825955756371

theorem tailTrace_1180267 : CollatzResearch.WordTrace tailWord_1180267 prefixEnd_1180267 404029514426825955756371 := by
  unfold tailWord_1180267
  simp only [CollatzResearch.WordTrace]
  refine ⟨43047874015101707400619055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28698582676734471600412703 43047874015101707400619055)
  ·
    refine ⟨64571811022652561100928583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43047874015101707400619055 64571811022652561100928583)
    ·
      refine ⟨96857716533978841651392875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64571811022652561100928583 96857716533978841651392875)
      ·
        refine ⟨145286574800968262477089313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96857716533978841651392875 145286574800968262477089313)
        ·
          refine ⟨108964931100726196857816985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145286574800968262477089313 108964931100726196857816985)
          ·
            refine ⟨81723698325544647643362739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108964931100726196857816985 81723698325544647643362739)
            ·
              refine ⟨122585547488316971465044109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81723698325544647643362739 122585547488316971465044109)
              ·
                refine ⟨45969580308118864299391541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122585547488316971465044109 45969580308118864299391541)
                ·
                  refine ⟨4309648153886143528067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45969580308118864299391541 4309648153886143528067957)
                  ·
                    refine ⟨404029514426825955756371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4309648153886143528067957 404029514426825955756371)
                    ·
                      rfl

theorem cell22_1180267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_1180267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180267 prefixEnd_1180267 := by exact prefixLift 1180267
  have htrace : WordTrace (prefixWord ++ tailWord_1180267) baseStart_1180267 baseEnd_1180267 := by
    simpa [prefixWord, tailWord_1180267, baseEnd_1180267] using wordTrace_append hprefix tailTrace_1180267
  have hstable : (prefixWord ++ tailWord_1180267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180267).length < 2 ^ (prefixWord ++ tailWord_1180267).sum := by decide
  have hdescent : baseEnd_1180267 < baseStart_1180267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180314 : List Nat := [3, 1, 1, 6, 11]
def baseStart_1180314 : Nat := 118140960795 + 1180314 * 2 ^ 59
def prefixEnd_1180314 : Nat := 4983230072969 + 3 ^ 40 * 1180314 * 2
def baseEnd_1180314 : Nat := 1662739109001372427289

theorem tailTrace_1180314 : CollatzResearch.WordTrace tailWord_1180314 prefixEnd_1180314 1662739109001372427289 := by
  unfold tailWord_1180314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762397061482858606894999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28699725497287622951719997 10762397061482858606894999)
  ·
    refine ⟨16143595592224287910342499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10762397061482858606894999 16143595592224287910342499)
    ·
      refine ⟨24215393388336431865513749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16143595592224287910342499 24215393388336431865513749)
      ·
        refine ⟨1135096565078270243695957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24215393388336431865513749 1135096565078270243695957)
        ·
          refine ⟨1662739109001372427289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1135096565078270243695957 1662739109001372427289)
          ·
            rfl

theorem cell22_1180314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 11].length) (baseStart_1180314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180314 prefixEnd_1180314 := by exact prefixLift 1180314
  have htrace : WordTrace (prefixWord ++ tailWord_1180314) baseStart_1180314 baseEnd_1180314 := by
    simpa [prefixWord, tailWord_1180314, baseEnd_1180314] using wordTrace_append hprefix tailTrace_1180314
  have hstable : (prefixWord ++ tailWord_1180314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180314).length < 2 ^ (prefixWord ++ tailWord_1180314).sum := by decide
  have hdescent : baseEnd_1180314 < baseStart_1180314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180316 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1180316 : Nat := 118140960795 + 1180316 * 2 ^ 59
def prefixEnd_1180316 : Nat := 4983230072969 + 3 ^ 40 * 1180316 * 2
def baseEnd_1180316 : Nat := 404046288128206161281221

theorem tailTrace_1180316 : CollatzResearch.WordTrace tailWord_1180316 prefixEnd_1180316 404046288128206161281221 := by
  unfold tailWord_1180316
  simp only [CollatzResearch.WordTrace]
  refine ⟨21524830595962094384576401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28699774127949459179435201 21524830595962094384576401)
  ·
    refine ⟨16143622946971570788432301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21524830595962094384576401 16143622946971570788432301)
    ·
      refine ⟨6053858605114339045662113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16143622946971570788432301 6053858605114339045662113)
      ·
        refine ⟨4540393953835754284246585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053858605114339045662113 4540393953835754284246585)
        ·
          refine ⟨3405295465376815713184939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540393953835754284246585 3405295465376815713184939)
          ·
            refine ⟨5107943198065223569777409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405295465376815713184939 5107943198065223569777409)
            ·
              refine ⟨3830957398548917677333057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5107943198065223569777409 3830957398548917677333057)
              ·
                refine ⟨2873218048911688257999793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830957398548917677333057 2873218048911688257999793)
                ·
                  refine ⟨2154913536683766193499845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873218048911688257999793 2154913536683766193499845)
                  ·
                    refine ⟨404046288128206161281221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154913536683766193499845 404046288128206161281221)
                    ·
                      rfl

theorem cell22_1180316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1180316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180316 prefixEnd_1180316 := by exact prefixLift 1180316
  have htrace : WordTrace (prefixWord ++ tailWord_1180316) baseStart_1180316 baseEnd_1180316 := by
    simpa [prefixWord, tailWord_1180316, baseEnd_1180316] using wordTrace_append hprefix tailTrace_1180316
  have hstable : (prefixWord ++ tailWord_1180316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180316).length < 2 ^ (prefixWord ++ tailWord_1180316).sum := by decide
  have hdescent : baseEnd_1180316 < baseStart_1180316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180320 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_1180320 : Nat := 118140960795 + 1180320 * 2 ^ 59
def prefixEnd_1180320 : Nat := 4983230072969 + 3 ^ 40 * 1180320 * 2
def baseEnd_1180320 : Nat := 134682552469983828060403

theorem tailTrace_1180320 : CollatzResearch.WordTrace tailWord_1180320 prefixEnd_1180320 134682552469983828060403 := by
  unfold tailWord_1180320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21524903541954848726149207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28699871389273131634865609 21524903541954848726149207)
  ·
    refine ⟨32287355312932273089223811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21524903541954848726149207 32287355312932273089223811)
    ·
      refine ⟨48431032969398409633835717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32287355312932273089223811 48431032969398409633835717)
      ·
        refine ⟨9080818681762201806344197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48431032969398409633835717 9080818681762201806344197)
        ·
          refine ⟨1702653502830412838689537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9080818681762201806344197 1702653502830412838689537)
          ·
            refine ⟨1276990127122809629017153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702653502830412838689537 1276990127122809629017153)
            ·
              refine ⟨957742595342107221762865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276990127122809629017153 957742595342107221762865)
              ·
                refine ⟨718306946506580416322149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957742595342107221762865 718306946506580416322149)
                ·
                  refine ⟨134682552469983828060403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718306946506580416322149 134682552469983828060403)
                  ·
                    rfl

theorem cell22_1180320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_1180320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180320 prefixEnd_1180320 := by exact prefixLift 1180320
  have htrace : WordTrace (prefixWord ++ tailWord_1180320) baseStart_1180320 baseEnd_1180320 := by
    simpa [prefixWord, tailWord_1180320, baseEnd_1180320] using wordTrace_append hprefix tailTrace_1180320
  have hstable : (prefixWord ++ tailWord_1180320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180320).length < 2 ^ (prefixWord ++ tailWord_1180320).sum := by decide
  have hdescent : baseEnd_1180320 < baseStart_1180320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180346 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_1180346 : Nat := 118140960795 + 1180346 * 2 ^ 59
def prefixEnd_1180346 : Nat := 4983230072969 + 3 ^ 40 * 1180346 * 2
def baseEnd_1180346 : Nat := 404056557741296083031129

theorem tailTrace_1180346 : CollatzResearch.WordTrace tailWord_1180346 prefixEnd_1180346 404056557741296083031129 := by
  unfold tailWord_1180346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762688845453875973186223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28700503587877002595163261 10762688845453875973186223)
  ·
    refine ⟨16144033268180813959779335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10762688845453875973186223 16144033268180813959779335)
    ·
      refine ⟨24216049902271220939669003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16144033268180813959779335 24216049902271220939669003)
      ·
        refine ⟨36324074853406831409503505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24216049902271220939669003 36324074853406831409503505)
        ·
          refine ⟨27243056140055123557127629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36324074853406831409503505 27243056140055123557127629)
          ·
            refine ⟨10216146052520671333922861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27243056140055123557127629 10216146052520671333922861)
            ·
              refine ⟨3831054769695251750221073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10216146052520671333922861 3831054769695251750221073)
              ·
                refine ⟨2873291077271438812665805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831054769695251750221073 2873291077271438812665805)
                ·
                  refine ⟨1077484153976789554749677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2873291077271438812665805 1077484153976789554749677)
                  ·
                    refine ⟨404056557741296083031129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077484153976789554749677 404056557741296083031129)
                    ·
                      rfl

theorem cell22_1180346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_1180346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180346 prefixEnd_1180346 := by exact prefixLift 1180346
  have htrace : WordTrace (prefixWord ++ tailWord_1180346) baseStart_1180346 baseEnd_1180346 := by
    simpa [prefixWord, tailWord_1180346, baseEnd_1180346] using wordTrace_append hprefix tailTrace_1180346
  have hstable : (prefixWord ++ tailWord_1180346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180346).length < 2 ^ (prefixWord ++ tailWord_1180346).sum := by decide
  have hdescent : baseEnd_1180346 < baseStart_1180346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180376 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_1180376 : Nat := 118140960795 + 1180376 * 2 ^ 59
def prefixEnd_1180376 : Nat := 4983230072969 + 3 ^ 40 * 1180376 * 2
def baseEnd_1180376 : Nat := 134688942451462001593679

theorem tailTrace_1180376 : CollatzResearch.WordTrace tailWord_1180376 prefixEnd_1180376 134688942451462001593679 := by
  unfold tailWord_1180376
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525924785853409508168491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28701233047804546010891321 21525924785853409508168491)
  ·
    refine ⟨32288887178780114262252737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21525924785853409508168491 32288887178780114262252737)
    ·
      refine ⟨24216665384085085696689553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32288887178780114262252737 24216665384085085696689553)
      ·
        refine ⟨18162499038063814272517165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24216665384085085696689553 18162499038063814272517165)
        ·
          refine ⟨6810937139273930352193937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18162499038063814272517165 6810937139273930352193937)
          ·
            refine ⟨5108202854455447764145453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6810937139273930352193937 5108202854455447764145453)
            ·
              refine ⟨1915576070420792911554545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5108202854455447764145453 1915576070420792911554545)
              ·
                refine ⟨1436682052815594683665909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915576070420792911554545 1436682052815594683665909)
                ·
                  refine ⟨134688942451462001593679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436682052815594683665909 134688942451462001593679)
                  ·
                    rfl

theorem cell22_1180376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_1180376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180376 prefixEnd_1180376 := by exact prefixLift 1180376
  have htrace : WordTrace (prefixWord ++ tailWord_1180376) baseStart_1180376 baseEnd_1180376 := by
    simpa [prefixWord, tailWord_1180376, baseEnd_1180376] using wordTrace_append hprefix tailTrace_1180376
  have hstable : (prefixWord ++ tailWord_1180376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180376).length < 2 ^ (prefixWord ++ tailWord_1180376).sum := by decide
  have hdescent : baseEnd_1180376 < baseStart_1180376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180380 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1180380 : Nat := 118140960795 + 1180380 * 2 ^ 59
def prefixEnd_1180380 : Nat := 4983230072969 + 3 ^ 40 * 1180380 * 2
def baseEnd_1180380 : Nat := 404068196636131327681025

theorem tailTrace_1180380 : CollatzResearch.WordTrace tailWord_1180380 prefixEnd_1180380 404068196636131327681025 := by
  unfold tailWord_1180380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525997731846163849741297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28701330309128218466321729 21525997731846163849741297)
  ·
    refine ⟨16144498298884622887305973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21525997731846163849741297 16144498298884622887305973)
    ·
      refine ⟨1513546715520433395684935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16144498298884622887305973 1513546715520433395684935)
      ·
        refine ⟨2270320073280650093527403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513546715520433395684935 2270320073280650093527403)
        ·
          refine ⟨3405480109920975140291105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270320073280650093527403 3405480109920975140291105)
          ·
            refine ⟨2554110082440731355218329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3405480109920975140291105 2554110082440731355218329)
            ·
              refine ⟨1915582561830548516413747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2554110082440731355218329 1915582561830548516413747)
              ·
                refine ⟨2873373842745822774620621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915582561830548516413747 2873373842745822774620621)
                ·
                  refine ⟨1077515191029683540482733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2873373842745822774620621 1077515191029683540482733)
                  ·
                    refine ⟨404068196636131327681025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077515191029683540482733 404068196636131327681025)
                    ·
                      rfl

theorem cell22_1180380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1180380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180380 prefixEnd_1180380 := by exact prefixLift 1180380
  have htrace : WordTrace (prefixWord ++ tailWord_1180380) baseStart_1180380 baseEnd_1180380 := by
    simpa [prefixWord, tailWord_1180380, baseEnd_1180380] using wordTrace_append hprefix tailTrace_1180380
  have hstable : (prefixWord ++ tailWord_1180380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180380).length < 2 ^ (prefixWord ++ tailWord_1180380).sum := by decide
  have hdescent : baseEnd_1180380 < baseStart_1180380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180419 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_1180419 : Nat := 118140960795 + 1180419 * 2 ^ 59
def prefixEnd_1180419 : Nat := 4983230072969 + 3 ^ 40 * 1180419 * 2
def baseEnd_1180419 : Nat := 404081547133148225955905

theorem tailTrace_1180419 : CollatzResearch.WordTrace tailWord_1180419 prefixEnd_1180419 404081547133148225955905 := by
  unfold tailWord_1180419
  simp only [CollatzResearch.WordTrace]
  refine ⟨43053417910551037360152311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28702278607034024906768207 43053417910551037360152311)
  ·
    refine ⟨64580126865826556040228467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43053417910551037360152311 64580126865826556040228467)
    ·
      refine ⟨96870190298739834060342701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64580126865826556040228467 96870190298739834060342701)
      ·
        refine ⟨36326321362027437772628513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96870190298739834060342701 36326321362027437772628513)
        ·
          refine ⟨27244741021520578329471385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36326321362027437772628513 27244741021520578329471385)
          ·
            refine ⟨20433555766140433747103539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27244741021520578329471385 20433555766140433747103539)
            ·
              refine ⟨30650333649210650620655309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20433555766140433747103539 30650333649210650620655309)
              ·
                refine ⟨11493875118453993982745741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30650333649210650620655309 11493875118453993982745741)
                ·
                  refine ⟨4310203169420247743529653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11493875118453993982745741 4310203169420247743529653)
                  ·
                    refine ⟨404081547133148225955905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4310203169420247743529653 404081547133148225955905)
                    ·
                      rfl

theorem cell22_1180419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_1180419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180419 prefixEnd_1180419 := by exact prefixLift 1180419
  have htrace : WordTrace (prefixWord ++ tailWord_1180419) baseStart_1180419 baseEnd_1180419 := by
    simpa [prefixWord, tailWord_1180419, baseEnd_1180419] using wordTrace_append hprefix tailTrace_1180419
  have hstable : (prefixWord ++ tailWord_1180419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180419).length < 2 ^ (prefixWord ++ tailWord_1180419).sum := by decide
  have hdescent : baseEnd_1180419 < baseStart_1180419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180423 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1180423 : Nat := 118140960795 + 1180423 * 2 ^ 59
def prefixEnd_1180423 : Nat := 4983230072969 + 3 ^ 40 * 1180423 * 2
def baseEnd_1180423 : Nat := 404082916414893548855893

theorem tailTrace_1180423 : CollatzResearch.WordTrace tailWord_1180423 prefixEnd_1180423 404082916414893548855893 := by
  unfold tailWord_1180423
  simp only [CollatzResearch.WordTrace]
  refine ⟨43053563802536546043297923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28702375868357697362198615 43053563802536546043297923)
  ·
    refine ⟨64580345703804819064946885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43053563802536546043297923 64580345703804819064946885)
    ·
      refine ⟨12108814819463403574677541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64580345703804819064946885 12108814819463403574677541)
      ·
        refine ⟨2270402778649388170252039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12108814819463403574677541 2270402778649388170252039)
        ·
          refine ⟨3405604167974082255378059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270402778649388170252039 3405604167974082255378059)
          ·
            refine ⟨5108406251961123383067089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405604167974082255378059 5108406251961123383067089)
            ·
              refine ⟨3831304688970842537300317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108406251961123383067089 3831304688970842537300317)
              ·
                refine ⟨1436739258364065951487619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831304688970842537300317 1436739258364065951487619)
                ·
                  refine ⟨2155108887546098927231429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436739258364065951487619 2155108887546098927231429)
                  ·
                    refine ⟨404082916414893548855893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155108887546098927231429 404082916414893548855893)
                    ·
                      rfl

theorem cell22_1180423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1180423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180423 prefixEnd_1180423 := by exact prefixLift 1180423
  have htrace : WordTrace (prefixWord ++ tailWord_1180423) baseStart_1180423 baseEnd_1180423 := by
    simpa [prefixWord, tailWord_1180423, baseEnd_1180423] using wordTrace_append hprefix tailTrace_1180423
  have hstable : (prefixWord ++ tailWord_1180423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180423).length < 2 ^ (prefixWord ++ tailWord_1180423).sum := by decide
  have hdescent : baseEnd_1180423 < baseStart_1180423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180453 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_1180453 : Nat := 118140960795 + 1180453 * 2 ^ 59
def prefixEnd_1180453 : Nat := 4983230072969 + 3 ^ 40 * 1180453 * 2
def baseEnd_1180453 : Nat := 404093186027983470605801

theorem tailTrace_1180453 : CollatzResearch.WordTrace tailWord_1180453 prefixEnd_1180453 404093186027983470605801 := by
  unfold tailWord_1180453
  simp only [CollatzResearch.WordTrace]
  refine ⟨43054657992427861166890013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28703105328285240777926675 43054657992427861166890013)
  ·
    refine ⟨16145496747160447937583755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43054657992427861166890013 16145496747160447937583755)
    ·
      refine ⟨24218245120740671906375633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16145496747160447937583755 24218245120740671906375633)
      ·
        refine ⟨18163683840555503929781725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24218245120740671906375633 18163683840555503929781725)
        ·
          refine ⟨6811381440208313973668147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18163683840555503929781725 6811381440208313973668147)
          ·
            refine ⟨10217072160312470960502221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811381440208313973668147 10217072160312470960502221)
            ·
              refine ⟨3831402060117176610188333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10217072160312470960502221 3831402060117176610188333)
              ·
                refine ⟨1436775772543941228820625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831402060117176610188333 1436775772543941228820625)
                ·
                  refine ⟨1077581829407955921615469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436775772543941228820625 1077581829407955921615469)
                  ·
                    refine ⟨404093186027983470605801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077581829407955921615469 404093186027983470605801)
                    ·
                      rfl

theorem cell22_1180453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_1180453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180453 prefixEnd_1180453 := by exact prefixLift 1180453
  have htrace : WordTrace (prefixWord ++ tailWord_1180453) baseStart_1180453 baseEnd_1180453 := by
    simpa [prefixWord, tailWord_1180453, baseEnd_1180453] using wordTrace_append hprefix tailTrace_1180453
  have hstable : (prefixWord ++ tailWord_1180453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180453).length < 2 ^ (prefixWord ++ tailWord_1180453).sum := by decide
  have hdescent : baseEnd_1180453 < baseStart_1180453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180464 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1180464 : Nat := 118140960795 + 1180464 * 2 ^ 59
def prefixEnd_1180464 : Nat := 4983230072969 + 3 ^ 40 * 1180464 * 2
def baseEnd_1180464 : Nat := 404096951552783108580767

theorem tailTrace_1180464 : CollatzResearch.WordTrace tailWord_1180464 prefixEnd_1180464 404096951552783108580767 := by
  unfold tailWord_1180464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527529597694005022770223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28703372796925340030360297 21527529597694005022770223)
  ·
    refine ⟨32291294396541007534155335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21527529597694005022770223 32291294396541007534155335)
    ·
      refine ⟨48436941594811511301233003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32291294396541007534155335 48436941594811511301233003)
      ·
        refine ⟨72655412392217266951849505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48436941594811511301233003 72655412392217266951849505)
        ·
          refine ⟨54491559294162950213887129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72655412392217266951849505 54491559294162950213887129)
          ·
            refine ⟨40868669470622212660415347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54491559294162950213887129 40868669470622212660415347)
            ·
              refine ⟨61303004205933318990623021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40868669470622212660415347 61303004205933318990623021)
              ·
                refine ⟨22988626577224994621483633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61303004205933318990623021 22988626577224994621483633)
                ·
                  refine ⟨17241469932918745966112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22988626577224994621483633 17241469932918745966112725)
                  ·
                    refine ⟨404096951552783108580767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17241469932918745966112725 404096951552783108580767)
                    ·
                      rfl

theorem cell22_1180464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1180464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180464 prefixEnd_1180464 := by exact prefixLift 1180464
  have htrace : WordTrace (prefixWord ++ tailWord_1180464) baseStart_1180464 baseEnd_1180464 := by
    simpa [prefixWord, tailWord_1180464, baseEnd_1180464] using wordTrace_append hprefix tailTrace_1180464
  have hstable : (prefixWord ++ tailWord_1180464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180464).length < 2 ^ (prefixWord ++ tailWord_1180464).sum := by decide
  have hdescent : baseEnd_1180464 < baseStart_1180464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180470 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1180470 : Nat := 118140960795 + 1180470 * 2 ^ 59
def prefixEnd_1180470 : Nat := 4983230072969 + 3 ^ 40 * 1180470 * 2
def baseEnd_1180470 : Nat := 404099005475401092930749

theorem tailTrace_1180470 : CollatzResearch.WordTrace tailWord_1180470 prefixEnd_1180470 404099005475401092930749 := by
  unfold tailWord_1180470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690954877085392066891179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28703518688910848713505909 2690954877085392066891179)
  ·
    refine ⟨4036432315628088100336769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2690954877085392066891179 4036432315628088100336769)
    ·
      refine ⟨3027324236721066075252577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4036432315628088100336769 3027324236721066075252577)
      ·
        refine ⟨2270493177540799556439433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027324236721066075252577 2270493177540799556439433)
        ·
          refine ⟨1702869883155599667329575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270493177540799556439433 1702869883155599667329575)
          ·
            refine ⟨2554304824733399500994363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702869883155599667329575 2554304824733399500994363)
            ·
              refine ⟨3831457237100099251491545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554304824733399500994363 3831457237100099251491545)
              ·
                refine ⟨2873592927825074438618659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831457237100099251491545 2873592927825074438618659)
                ·
                  refine ⟨4310389391737611657927989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873592927825074438618659 4310389391737611657927989)
                  ·
                    refine ⟨404099005475401092930749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4310389391737611657927989 404099005475401092930749)
                    ·
                      rfl

theorem cell22_1180470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1180470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180470 prefixEnd_1180470 := by exact prefixLift 1180470
  have htrace : WordTrace (prefixWord ++ tailWord_1180470) baseStart_1180470 baseEnd_1180470 := by
    simpa [prefixWord, tailWord_1180470, baseEnd_1180470] using wordTrace_append hprefix tailTrace_1180470
  have hstable : (prefixWord ++ tailWord_1180470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180470).length < 2 ^ (prefixWord ++ tailWord_1180470).sum := by decide
  have hdescent : baseEnd_1180470 < baseStart_1180470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180498 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1180498 : Nat := 118140960795 + 1180498 * 2 ^ 59
def prefixEnd_1180498 : Nat := 4983230072969 + 3 ^ 40 * 1180498 * 2
def baseEnd_1180498 : Nat := 404108590447618353230663

theorem tailTrace_1180498 : CollatzResearch.WordTrace tailWord_1180498 prefixEnd_1180498 404108590447618353230663 := by
  unfold tailWord_1180498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764074819316208463069537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28704199518176555901518765 10764074819316208463069537)
  ·
    refine ⟨8073056114487156347302153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10764074819316208463069537 8073056114487156347302153)
    ·
      refine ⟨6054792085865367260476615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8073056114487156347302153 6054792085865367260476615)
      ·
        refine ⟨9082188128798050890714923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054792085865367260476615 9082188128798050890714923)
        ·
          refine ⟨13623282193197076336072385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9082188128798050890714923 13623282193197076336072385)
          ·
            refine ⟨10217461644897807252054289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13623282193197076336072385 10217461644897807252054289)
            ·
              refine ⟨7663096233673355439040717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10217461644897807252054289 7663096233673355439040717)
              ·
                refine ⟨2873661087627508289640269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7663096233673355439040717 2873661087627508289640269)
                ·
                  refine ⟨1077622907860315608615101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2873661087627508289640269 1077622907860315608615101)
                  ·
                    refine ⟨404108590447618353230663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077622907860315608615101 404108590447618353230663)
                    ·
                      rfl

theorem cell22_1180498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1180498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180498 prefixEnd_1180498 := by exact prefixLift 1180498
  have htrace : WordTrace (prefixWord ++ tailWord_1180498) baseStart_1180498 baseEnd_1180498 := by
    simpa [prefixWord, tailWord_1180498, baseEnd_1180498] using wordTrace_append hprefix tailTrace_1180498
  have hstable : (prefixWord ++ tailWord_1180498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180498).length < 2 ^ (prefixWord ++ tailWord_1180498).sum := by decide
  have hdescent : baseEnd_1180498 < baseStart_1180498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180500 : List Nat := [2, 4, 1, 1, 5, 1, 1, 7]
def baseStart_1180500 : Nat := 118140960795 + 1180500 * 2 ^ 59
def prefixEnd_1180500 : Nat := 4983230072969 + 3 ^ 40 * 1180500 * 2
def baseEnd_1180500 : Nat := 44901030565387890520073

theorem tailTrace_1180500 : CollatzResearch.WordTrace tailWord_1180500 prefixEnd_1180500 44901030565387890520073 := by
  unfold tailWord_1180500
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528186111628794096925477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28704248148838392129233969 21528186111628794096925477)
  ·
    refine ⟨4036534895930398893173527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21528186111628794096925477 4036534895930398893173527)
    ·
      refine ⟨6054802343895598339760291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4036534895930398893173527 6054802343895598339760291)
      ·
        refine ⟨9082203515843397509640437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054802343895598339760291 9082203515843397509640437)
        ·
          refine ⟨851456579610318516528791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9082203515843397509640437 851456579610318516528791)
          ·
            refine ⟨1277184869415477774793187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851456579610318516528791 1277184869415477774793187)
            ·
              refine ⟨1915777304123216662189781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277184869415477774793187 1915777304123216662189781)
              ·
                refine ⟨44901030565387890520073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1915777304123216662189781 44901030565387890520073)
                ·
                  rfl

theorem cell22_1180500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_1180500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180500 prefixEnd_1180500 := by exact prefixLift 1180500
  have htrace : WordTrace (prefixWord ++ tailWord_1180500) baseStart_1180500 baseEnd_1180500 := by
    simpa [prefixWord, tailWord_1180500, baseEnd_1180500] using wordTrace_append hprefix tailTrace_1180500
  have hstable : (prefixWord ++ tailWord_1180500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180500).length < 2 ^ (prefixWord ++ tailWord_1180500).sum := by decide
  have hdescent : baseEnd_1180500 < baseStart_1180500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180511 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 5]
def baseStart_1180511 : Nat := 118140960795 + 1180511 * 2 ^ 59
def prefixEnd_1180511 : Nat := 4983230072969 + 3 ^ 40 * 1180511 * 2
def baseEnd_1180511 : Nat := 134704346871096884218541

theorem tailTrace_1180511 : CollatzResearch.WordTrace tailWord_1180511 prefixEnd_1180511 134704346871096884218541 := by
  unfold tailWord_1180511
  simp only [CollatzResearch.WordTrace]
  refine ⟨43056773426217737072501387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28704515617478491381667591 43056773426217737072501387)
  ·
    refine ⟨64585160139326605608752081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43056773426217737072501387 64585160139326605608752081)
    ·
      refine ⟨48438870104494954206564061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64585160139326605608752081 48438870104494954206564061)
      ·
        refine ⟨18164576289185607827461523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48438870104494954206564061 18164576289185607827461523)
        ·
          refine ⟨27246864433778411741192285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18164576289185607827461523 27246864433778411741192285)
          ·
            refine ⟨10217574162666904402947107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27246864433778411741192285 10217574162666904402947107)
            ·
              refine ⟨15326361244000356604420661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10217574162666904402947107 15326361244000356604420661)
              ·
                refine ⟨1436846366625033431664437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15326361244000356604420661 1436846366625033431664437)
                ·
                  refine ⟨134704346871096884218541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436846366625033431664437 134704346871096884218541)
                  ·
                    rfl

theorem cell22_1180511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 5].length) (baseStart_1180511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180511 prefixEnd_1180511 := by exact prefixLift 1180511
  have htrace : WordTrace (prefixWord ++ tailWord_1180511) baseStart_1180511 baseEnd_1180511 := by
    simpa [prefixWord, tailWord_1180511, baseEnd_1180511] using wordTrace_append hprefix tailTrace_1180511
  have hstable : (prefixWord ++ tailWord_1180511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180511).length < 2 ^ (prefixWord ++ tailWord_1180511).sum := by decide
  have hdescent : baseEnd_1180511 < baseStart_1180511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180556 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1180556 : Nat := 118140960795 + 1180556 * 2 ^ 59
def prefixEnd_1180556 : Nat := 4983230072969 + 3 ^ 40 * 1180556 * 2
def baseEnd_1180556 : Nat := 134709481677641845093495

theorem tailTrace_1180556 : CollatzResearch.WordTrace tailWord_1180556 prefixEnd_1180556 134709481677641845093495 := by
  unfold tailWord_1180556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21529207355527354878944761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28705609807369806505259681 21529207355527354878944761)
  ·
    refine ⟨16146905516645516159208571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21529207355527354878944761 16146905516645516159208571)
    ·
      refine ⟨24220358274968274238812857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16146905516645516159208571 24220358274968274238812857)
      ·
        refine ⟨18165268706226205679109643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24220358274968274238812857 18165268706226205679109643)
        ·
          refine ⟨27247903059339308518664465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18165268706226205679109643 27247903059339308518664465)
          ·
            refine ⟨20435927294504481388998349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27247903059339308518664465 20435927294504481388998349)
            ·
              refine ⟨7663472735439180520874381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20435927294504481388998349 7663472735439180520874381)
              ·
                refine ⟨2873802275789692695327893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7663472735439180520874381 2873802275789692695327893)
                ·
                  refine ⟨134709481677641845093495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2873802275789692695327893 134709481677641845093495)
                  ·
                    rfl

theorem cell22_1180556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1180556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180556 prefixEnd_1180556 := by exact prefixLift 1180556
  have htrace : WordTrace (prefixWord ++ tailWord_1180556) baseStart_1180556 baseEnd_1180556 := by
    simpa [prefixWord, tailWord_1180556, baseEnd_1180556] using wordTrace_append hprefix tailTrace_1180556
  have hstable : (prefixWord ++ tailWord_1180556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180556).length < 2 ^ (prefixWord ++ tailWord_1180556).sum := by decide
  have hdescent : baseEnd_1180556 < baseStart_1180556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180562 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_1180562 : Nat := 118140960795 + 1180562 * 2 ^ 59
def prefixEnd_1180562 : Nat := 4983230072969 + 3 ^ 40 * 1180562 * 2
def baseEnd_1180562 : Nat := 134710166318514506543489

theorem tailTrace_1180562 : CollatzResearch.WordTrace tailWord_1180562 prefixEnd_1180562 134710166318514506543489 := by
  unfold tailWord_1180562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764658387258243195651985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28705755699355315188405293 10764658387258243195651985)
  ·
    refine ⟨8073493790443682396738989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10764658387258243195651985 8073493790443682396738989)
    ·
      refine ⟨3027560171416380898777121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8073493790443682396738989 3027560171416380898777121)
      ·
        refine ⟨2270670128562285674082841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027560171416380898777121 2270670128562285674082841)
        ·
          refine ⟨1703002596421714255562131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270670128562285674082841 1703002596421714255562131)
          ·
            refine ⟨2554503894632571383343197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703002596421714255562131 2554503894632571383343197)
            ·
              refine ⟨957938960487214268753699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2554503894632571383343197 957938960487214268753699)
              ·
                refine ⟨1436908440730821403130549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957938960487214268753699 1436908440730821403130549)
                ·
                  refine ⟨134710166318514506543489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436908440730821403130549 134710166318514506543489)
                  ·
                    rfl

theorem cell22_1180562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_1180562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180562 prefixEnd_1180562 := by exact prefixLift 1180562
  have htrace : WordTrace (prefixWord ++ tailWord_1180562) baseStart_1180562 baseEnd_1180562 := by
    simpa [prefixWord, tailWord_1180562, baseEnd_1180562] using wordTrace_append hprefix tailTrace_1180562
  have hstable : (prefixWord ++ tailWord_1180562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180562).length < 2 ^ (prefixWord ++ tailWord_1180562).sum := by decide
  have hdescent : baseEnd_1180562 < baseStart_1180562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180575 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 1, 4]
def baseStart_1180575 : Nat := 118140960795 + 1180575 * 2 ^ 59
def prefixEnd_1180575 : Nat := 4983230072969 + 3 ^ 40 * 1180575 * 2
def baseEnd_1180575 : Nat := 404134949121215819055427

theorem tailTrace_1180575 : CollatzResearch.WordTrace tailWord_1180575 prefixEnd_1180575 404134949121215819055427 := by
  unfold tailWord_1180575
  simp only [CollatzResearch.WordTrace]
  refine ⟨43059107697985876002831179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28706071798657250668554119 43059107697985876002831179)
  ·
    refine ⟨64588661546978814004246769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43059107697985876002831179 64588661546978814004246769)
    ·
      refine ⟨48441496160234110503185077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64588661546978814004246769 48441496160234110503185077)
      ·
        refine ⟨4541390265021947859673601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48441496160234110503185077 4541390265021947859673601)
        ·
          refine ⟨3406042698766460894755201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4541390265021947859673601 3406042698766460894755201)
          ·
            refine ⟨2554532024074845671066401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406042698766460894755201 2554532024074845671066401)
            ·
              refine ⟨1915899018056134253299801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2554532024074845671066401 1915899018056134253299801)
              ·
                refine ⟨1436924263542100689974851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915899018056134253299801 1436924263542100689974851)
                ·
                  refine ⟨2155386395313151034962277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436924263542100689974851 2155386395313151034962277)
                  ·
                    refine ⟨404134949121215819055427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155386395313151034962277 404134949121215819055427)
                    ·
                      rfl

theorem cell22_1180575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_1180575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180575 prefixEnd_1180575 := by exact prefixLift 1180575
  have htrace : WordTrace (prefixWord ++ tailWord_1180575) baseStart_1180575 baseEnd_1180575 := by
    simpa [prefixWord, tailWord_1180575, baseEnd_1180575] using wordTrace_append hprefix tailTrace_1180575
  have hstable : (prefixWord ++ tailWord_1180575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180575).length < 2 ^ (prefixWord ++ tailWord_1180575).sum := by decide
  have hdescent : baseEnd_1180575 < baseStart_1180575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180601 : List Nat := [1, 2, 1, 4, 2, 2, 10]
def baseStart_1180601 : Nat := 118140960795 + 1180601 * 2 ^ 59
def prefixEnd_1180601 : Nat := 4983230072969 + 3 ^ 40 * 1180601 * 2
def baseEnd_1180601 : Nat := 14968290720465200663161

theorem tailTrace_1180601 : CollatzResearch.WordTrace tailWord_1180601 prefixEnd_1180601 14968290720465200663161 := by
  unfold tailWord_1180601
  simp only [CollatzResearch.WordTrace]
  refine ⟨43060055995891682443277657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28706703997261121628851771 43060055995891682443277657)
  ·
    refine ⟨32295041996918761832458243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43060055995891682443277657 32295041996918761832458243)
    ·
      refine ⟨48442562995378142748687365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32295041996918761832458243 48442562995378142748687365)
      ·
        refine ⟨9082980561633401765378881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48442562995378142748687365 9082980561633401765378881)
        ·
          refine ⟨6812235421225051324034161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9082980561633401765378881 6812235421225051324034161)
          ·
            refine ⟨5109176565918788493025621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6812235421225051324034161 5109176565918788493025621)
            ·
              refine ⟨14968290720465200663161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5109176565918788493025621 14968290720465200663161)
              ·
                rfl

theorem cell22_1180601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 10].length) (baseStart_1180601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180601 prefixEnd_1180601 := by exact prefixLift 1180601
  have htrace : WordTrace (prefixWord ++ tailWord_1180601) baseStart_1180601 baseEnd_1180601 := by
    simpa [prefixWord, tailWord_1180601, baseEnd_1180601] using wordTrace_append hprefix tailTrace_1180601
  have hstable : (prefixWord ++ tailWord_1180601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180601).length < 2 ^ (prefixWord ++ tailWord_1180601).sum := by decide
  have hdescent : baseEnd_1180601 < baseStart_1180601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180622 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1180622 : Nat := 118140960795 + 1180622 * 2 ^ 59
def prefixEnd_1180622 : Nat := 4983230072969 + 3 ^ 40 * 1180622 * 2
def baseEnd_1180622 : Nat := 404151038181723363130283

theorem tailTrace_1180622 : CollatzResearch.WordTrace tailWord_1180622 prefixEnd_1180622 404151038181723363130283 := by
  unfold tailWord_1180622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382602741101950378724015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28707214619210402019861413 5382602741101950378724015)
  ·
    refine ⟨8073904111652925568086023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5382602741101950378724015 8073904111652925568086023)
    ·
      refine ⟨12110856167479388352129035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8073904111652925568086023 12110856167479388352129035)
      ·
        refine ⟨18166284251219082528193553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12110856167479388352129035 18166284251219082528193553)
        ·
          refine ⟨13624713188414311896145165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18166284251219082528193553 13624713188414311896145165)
          ·
            refine ⟨5109267445655366961054437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13624713188414311896145165 5109267445655366961054437)
            ·
              refine ⟨957987646060381305197707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5109267445655366961054437 957987646060381305197707)
              ·
                refine ⟨1436981469090571957796561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957987646060381305197707 1436981469090571957796561)
                ·
                  refine ⟨1077736101817928968347421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436981469090571957796561 1077736101817928968347421)
                  ·
                    refine ⟨404151038181723363130283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077736101817928968347421 404151038181723363130283)
                    ·
                      rfl

theorem cell22_1180622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1180622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180622 prefixEnd_1180622 := by exact prefixLift 1180622
  have htrace : WordTrace (prefixWord ++ tailWord_1180622) baseStart_1180622 baseEnd_1180622 := by
    simpa [prefixWord, tailWord_1180622, baseEnd_1180622] using wordTrace_append hprefix tailTrace_1180622
  have hstable : (prefixWord ++ tailWord_1180622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180622).length < 2 ^ (prefixWord ++ tailWord_1180622).sum := by decide
  have hdescent : baseEnd_1180622 < baseStart_1180622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180631 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1180631 : Nat := 118140960795 + 1180631 * 2 ^ 59
def prefixEnd_1180631 : Nat := 4983230072969 + 3 ^ 40 * 1180631 * 2
def baseEnd_1180631 : Nat := 404154119065650339655255

theorem tailTrace_1180631 : CollatzResearch.WordTrace tailWord_1180631 prefixEnd_1180631 404154119065650339655255 := by
  unfold tailWord_1180631
  simp only [CollatzResearch.WordTrace]
  refine ⟨43061150185782997566869747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28707433457188665044579831 43061150185782997566869747)
  ·
    refine ⟨64591725278674496350304621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43061150185782997566869747 64591725278674496350304621)
    ·
      refine ⟨24221896979502936131364233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64591725278674496350304621 24221896979502936131364233)
      ·
        refine ⟨18166422734627202098523175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24221896979502936131364233 18166422734627202098523175)
        ·
          refine ⟨27249634101940803147784763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18166422734627202098523175 27249634101940803147784763)
          ·
            refine ⟨40874451152911204721677145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27249634101940803147784763 40874451152911204721677145)
            ·
              refine ⟨30655838364683403541257859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40874451152911204721677145 30655838364683403541257859)
              ·
                refine ⟨45983757547025105311886789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30655838364683403541257859 45983757547025105311886789)
                ·
                  refine ⟨8621954540067207245978773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45983757547025105311886789 8621954540067207245978773)
                  ·
                    refine ⟨404154119065650339655255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8621954540067207245978773 404154119065650339655255)
                    ·
                      rfl

theorem cell22_1180631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1180631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180631 prefixEnd_1180631 := by exact prefixLift 1180631
  have htrace : WordTrace (prefixWord ++ tailWord_1180631) baseStart_1180631 baseEnd_1180631 := by
    simpa [prefixWord, tailWord_1180631, baseEnd_1180631] using wordTrace_append hprefix tailTrace_1180631
  have hstable : (prefixWord ++ tailWord_1180631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180631).length < 2 ^ (prefixWord ++ tailWord_1180631).sum := by decide
  have hdescent : baseEnd_1180631 < baseStart_1180631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180714 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_1180714 : Nat := 118140960795 + 1180714 * 2 ^ 59
def prefixEnd_1180714 : Nat := 4983230072969 + 3 ^ 40 * 1180714 * 2
def baseEnd_1180714 : Nat := 134727510553955263276667

theorem tailTrace_1180714 : CollatzResearch.WordTrace tailWord_1180714 prefixEnd_1180714 134727510553955263276667 := by
  unfold tailWord_1180714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766044361120575685535299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28709451629654868494760797 10766044361120575685535299)
  ·
    refine ⟨16149066541680863528302949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10766044361120575685535299 16149066541680863528302949)
    ·
      refine ⟨3027949976565161911556803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16149066541680863528302949 3027949976565161911556803)
      ·
        refine ⟨4541924964847742867335205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027949976565161911556803 4541924964847742867335205)
        ·
          refine ⟨851610930908951787625351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4541924964847742867335205 851610930908951787625351)
          ·
            refine ⟨1277416396363427681438027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851610930908951787625351 1277416396363427681438027)
            ·
              refine ⟨1916124594545141522157041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277416396363427681438027 1916124594545141522157041)
              ·
                refine ⟨1437093445908856141617781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916124594545141522157041 1437093445908856141617781)
                ·
                  refine ⟨134727510553955263276667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437093445908856141617781 134727510553955263276667)
                  ·
                    rfl

theorem cell22_1180714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_1180714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180714 prefixEnd_1180714 := by exact prefixLift 1180714
  have htrace : WordTrace (prefixWord ++ tailWord_1180714) baseStart_1180714 baseEnd_1180714 := by
    simpa [prefixWord, tailWord_1180714, baseEnd_1180714] using wordTrace_append hprefix tailTrace_1180714
  have hstable : (prefixWord ++ tailWord_1180714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180714).length < 2 ^ (prefixWord ++ tailWord_1180714).sum := by decide
  have hdescent : baseEnd_1180714 < baseStart_1180714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180742 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1180742 : Nat := 118140960795 + 1180742 * 2 ^ 59
def prefixEnd_1180742 : Nat := 4983230072969 + 3 ^ 40 * 1180742 * 2
def baseEnd_1180742 : Nat := 134730705544694350043305

theorem tailTrace_1180742 : CollatzResearch.WordTrace tailWord_1180742 prefixEnd_1180742 134730705544694350043305 := by
  unfold tailWord_1180742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345787459011901985130015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28710132458920575682773653 1345787459011901985130015)
  ·
    refine ⟨2018681188517852977695023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345787459011901985130015 2018681188517852977695023)
    ·
      refine ⟨3028021782776779466542535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018681188517852977695023 3028021782776779466542535)
      ·
        refine ⟨4542032674165169199813803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028021782776779466542535 4542032674165169199813803)
        ·
          refine ⟨6813049011247753799720705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542032674165169199813803 6813049011247753799720705)
          ·
            refine ⟨5109786758435815349790529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813049011247753799720705 5109786758435815349790529)
            ·
              refine ⟨3832340068826861512342897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109786758435815349790529 3832340068826861512342897)
              ·
                refine ⟨2874255051620146134257173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3832340068826861512342897 2874255051620146134257173)
                ·
                  refine ⟨134730705544694350043305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2874255051620146134257173 134730705544694350043305)
                  ·
                    rfl

theorem cell22_1180742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1180742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180742 prefixEnd_1180742 := by exact prefixLift 1180742
  have htrace : WordTrace (prefixWord ++ tailWord_1180742) baseStart_1180742 baseEnd_1180742 := by
    simpa [prefixWord, tailWord_1180742, baseEnd_1180742] using wordTrace_append hprefix tailTrace_1180742
  have hstable : (prefixWord ++ tailWord_1180742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180742).length < 2 ^ (prefixWord ++ tailWord_1180742).sum := by decide
  have hdescent : baseEnd_1180742 < baseStart_1180742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180770 : List Nat := [3, 3, 2, 2, 1, 1, 10]
def baseStart_1180770 : Nat := 118140960795 + 1180770 * 2 ^ 59
def prefixEnd_1180770 : Nat := 4983230072969 + 3 ^ 40 * 1180770 * 2
def baseEnd_1180770 : Nat := 14970433392825937423327

theorem tailTrace_1180770 : CollatzResearch.WordTrace tailWord_1180770 prefixEnd_1180770 14970433392825937423327 := by
  unfold tailWord_1180770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766554983069856076544941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28710813288186282870786509 10766554983069856076544941)
  ·
    refine ⟨4037458118651196028704353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10766554983069856076544941 4037458118651196028704353)
    ·
      refine ⟨3028093588988397021528265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4037458118651196028704353 3028093588988397021528265)
      ·
        refine ⟨2271070191741297766146199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3028093588988397021528265 2271070191741297766146199)
        ·
          refine ⟨3406605287611946649219299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271070191741297766146199 3406605287611946649219299)
          ·
            refine ⟨5109907931417919973828949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406605287611946649219299 5109907931417919973828949)
            ·
              refine ⟨14970433392825937423327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5109907931417919973828949 14970433392825937423327)
              ·
                rfl

theorem cell22_1180770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 10].length) (baseStart_1180770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180770 prefixEnd_1180770 := by exact prefixLift 1180770
  have htrace : WordTrace (prefixWord ++ tailWord_1180770) baseStart_1180770 baseEnd_1180770 := by
    simpa [prefixWord, tailWord_1180770, baseEnd_1180770] using wordTrace_append hprefix tailTrace_1180770
  have hstable : (prefixWord ++ tailWord_1180770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180770).length < 2 ^ (prefixWord ++ tailWord_1180770).sum := by decide
  have hdescent : baseEnd_1180770 < baseStart_1180770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180776 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_1180776 : Nat := 118140960795 + 1180776 * 2 ^ 59
def prefixEnd_1180776 : Nat := 4983230072969 + 3 ^ 40 * 1180776 * 2
def baseEnd_1180776 : Nat := 134734585176306098259937

theorem tailTrace_1180776 : CollatzResearch.WordTrace tailWord_1180776 prefixEnd_1180776 134734585176306098259937 := by
  unfold tailWord_1180776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533219385128843665449091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28710959180171791553932121 21533219385128843665449091)
  ·
    refine ⟨32299829077693265498173637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21533219385128843665449091 32299829077693265498173637)
    ·
      refine ⟨6056217952067487280907557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32299829077693265498173637 6056217952067487280907557)
      ·
        refine ⟨1135540866012653865170167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6056217952067487280907557 1135540866012653865170167)
        ·
          refine ⟨1703311299018980797755251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135540866012653865170167 1703311299018980797755251)
          ·
            refine ⟨2554966948528471196632877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703311299018980797755251 2554966948528471196632877)
            ·
              refine ⟨958112605698176698737329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2554966948528471196632877 958112605698176698737329)
              ·
                refine ⟨718584454273632524052997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958112605698176698737329 718584454273632524052997)
                ·
                  refine ⟨134734585176306098259937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718584454273632524052997 134734585176306098259937)
                  ·
                    rfl

theorem cell22_1180776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_1180776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180776 prefixEnd_1180776 := by exact prefixLift 1180776
  have htrace : WordTrace (prefixWord ++ tailWord_1180776) baseStart_1180776 baseEnd_1180776 := by
    simpa [prefixWord, tailWord_1180776, baseEnd_1180776] using wordTrace_append hprefix tailTrace_1180776
  have hstable : (prefixWord ++ tailWord_1180776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180776).length < 2 ^ (prefixWord ++ tailWord_1180776).sum := by decide
  have hdescent : baseEnd_1180776 < baseStart_1180776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180783 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_1180783 : Nat := 118140960795 + 1180783 * 2 ^ 59
def prefixEnd_1180783 : Nat := 4983230072969 + 3 ^ 40 * 1180783 * 2
def baseEnd_1180783 : Nat := 404206151771972609854789

theorem tailTrace_1180783 : CollatzResearch.WordTrace tailWord_1180783 prefixEnd_1180783 404206151771972609854789 := by
  unfold tailWord_1180783
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066694081232327526403003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28711129387488218350935335 43066694081232327526403003)
  ·
    refine ⟨64600041121848491289604505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43066694081232327526403003 64600041121848491289604505)
    ·
      refine ⟨48450030841386368467203379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64600041121848491289604505 48450030841386368467203379)
      ·
        refine ⟨72675046262079552700805069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48450030841386368467203379 72675046262079552700805069)
        ·
          refine ⟨27253142348279832262801901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72675046262079552700805069 27253142348279832262801901)
          ·
            refine ⟨10219928380604937098550713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27253142348279832262801901 10219928380604937098550713)
            ·
              refine ⟨7664946285453702823913035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10219928380604937098550713 7664946285453702823913035)
              ·
                refine ⟨11497419428180554235869553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664946285453702823913035 11497419428180554235869553)
                ·
                  refine ⟨8623064571135415676902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11497419428180554235869553 8623064571135415676902165)
                  ·
                    refine ⟨404206151771972609854789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8623064571135415676902165 404206151771972609854789)
                    ·
                      rfl

theorem cell22_1180783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_1180783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180783 prefixEnd_1180783 := by exact prefixLift 1180783
  have htrace : WordTrace (prefixWord ++ tailWord_1180783) baseStart_1180783 baseEnd_1180783 := by
    simpa [prefixWord, tailWord_1180783, baseEnd_1180783] using wordTrace_append hprefix tailTrace_1180783
  have hstable : (prefixWord ++ tailWord_1180783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180783).length < 2 ^ (prefixWord ++ tailWord_1180783).sum := by decide
  have hdescent : baseEnd_1180783 < baseStart_1180783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180785 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_1180785 : Nat := 118140960795 + 1180785 * 2 ^ 59
def prefixEnd_1180785 : Nat := 4983230072969 + 3 ^ 40 * 1180785 * 2
def baseEnd_1180785 : Nat := 404206836412845271304783

theorem tailTrace_1180785 : CollatzResearch.WordTrace tailWord_1180785 prefixEnd_1180785 404206836412845271304783 := by
  unfold tailWord_1180785
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066767027225081867975809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28711178018150054578650539 43066767027225081867975809)
  ·
    refine ⟨32300075270418811400981857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43066767027225081867975809 32300075270418811400981857)
    ·
      refine ⟨24225056452814108550736393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32300075270418811400981857 24225056452814108550736393)
      ·
        refine ⟨18168792339610581413052295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24225056452814108550736393 18168792339610581413052295)
        ·
          refine ⟨27253188509415872119578443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18168792339610581413052295 27253188509415872119578443)
          ·
            refine ⟨40879782764123808179367665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27253188509415872119578443 40879782764123808179367665)
            ·
              refine ⟨30659837073092856134525749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40879782764123808179367665 30659837073092856134525749)
              ·
                refine ⟨2874359725602455262611789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30659837073092856134525749 2874359725602455262611789)
                ·
                  refine ⟨1077884897100920723479421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2874359725602455262611789 1077884897100920723479421)
                  ·
                    refine ⟨404206836412845271304783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077884897100920723479421 404206836412845271304783)
                    ·
                      rfl

theorem cell22_1180785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_1180785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180785 prefixEnd_1180785 := by exact prefixLift 1180785
  have htrace : WordTrace (prefixWord ++ tailWord_1180785) baseStart_1180785 baseEnd_1180785 := by
    simpa [prefixWord, tailWord_1180785, baseEnd_1180785] using wordTrace_append hprefix tailTrace_1180785
  have hstable : (prefixWord ++ tailWord_1180785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180785).length < 2 ^ (prefixWord ++ tailWord_1180785).sum := by decide
  have hdescent : baseEnd_1180785 < baseStart_1180785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180836 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_1180836 : Nat := 118140960795 + 1180836 * 2 ^ 59
def prefixEnd_1180836 : Nat := 4983230072969 + 3 ^ 40 * 1180836 * 2
def baseEnd_1180836 : Nat := 404224294755098138279627

theorem tailTrace_1180836 : CollatzResearch.WordTrace tailWord_1180836 prefixEnd_1180836 404224294755098138279627 := by
  unfold tailWord_1180836
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534313575020158789041181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28712418100026878385388241 21534313575020158789041181)
  ·
    refine ⟨8075367590632559545890443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21534313575020158789041181 8075367590632559545890443)
    ·
      refine ⟨12113051385948839318835665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8075367590632559545890443 12113051385948839318835665)
      ·
        refine ⟨9084788539461629489126749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12113051385948839318835665 9084788539461629489126749)
        ·
          refine ⟨3406795702298111058422531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9084788539461629489126749 3406795702298111058422531)
          ·
            refine ⟨5110193553447166587633797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406795702298111058422531 5110193553447166587633797)
            ·
              refine ⟨958161291271343735181337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5110193553447166587633797 958161291271343735181337)
              ·
                refine ⟨718620968453507801386003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958161291271343735181337 718620968453507801386003)
                ·
                  refine ⟨1077931452680261702079005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718620968453507801386003 1077931452680261702079005)
                  ·
                    refine ⟨404224294755098138279627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1077931452680261702079005 404224294755098138279627)
                    ·
                      rfl

theorem cell22_1180836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_1180836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180836 prefixEnd_1180836 := by exact prefixLift 1180836
  have htrace : WordTrace (prefixWord ++ tailWord_1180836) baseStart_1180836 baseEnd_1180836 := by
    simpa [prefixWord, tailWord_1180836, baseEnd_1180836] using wordTrace_append hprefix tailTrace_1180836
  have hstable : (prefixWord ++ tailWord_1180836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180836).length < 2 ^ (prefixWord ++ tailWord_1180836).sum := by decide
  have hdescent : baseEnd_1180836 < baseStart_1180836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180860 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_1180860 : Nat := 118140960795 + 1180860 * 2 ^ 59
def prefixEnd_1180860 : Nat := 4983230072969 + 3 ^ 40 * 1180860 * 2
def baseEnd_1180860 : Nat := 134744170148523358559851

theorem tailTrace_1180860 : CollatzResearch.WordTrace tailWord_1180860 prefixEnd_1180860 134744170148523358559851 := by
  unfold tailWord_1180860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534751250976684838478017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28713001667968913117970689 21534751250976684838478017)
  ·
    refine ⟨16151063438232513628858513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21534751250976684838478017 16151063438232513628858513)
    ·
      refine ⟨12113297578674385221643885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16151063438232513628858513 12113297578674385221643885)
      ·
        refine ⟨4542486592002894458116457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12113297578674385221643885 4542486592002894458116457)
        ·
          refine ⟨3406864944002170843587343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4542486592002894458116457 3406864944002170843587343)
          ·
            refine ⟨5110297416003256265381015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406864944002170843587343 5110297416003256265381015)
            ·
              refine ⟨7665446124004884398071523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5110297416003256265381015 7665446124004884398071523)
              ·
                refine ⟨11498169186007326597107285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665446124004884398071523 11498169186007326597107285)
                ·
                  refine ⟨134744170148523358559851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11498169186007326597107285 134744170148523358559851)
                  ·
                    rfl

theorem cell22_1180860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_1180860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180860 prefixEnd_1180860 := by exact prefixLift 1180860
  have htrace : WordTrace (prefixWord ++ tailWord_1180860) baseStart_1180860 baseEnd_1180860 := by
    simpa [prefixWord, tailWord_1180860, baseEnd_1180860] using wordTrace_append hprefix tailTrace_1180860
  have hstable : (prefixWord ++ tailWord_1180860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180860).length < 2 ^ (prefixWord ++ tailWord_1180860).sum := by decide
  have hdescent : baseEnd_1180860 < baseStart_1180860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180862 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1180862 : Nat := 118140960795 + 1180862 * 2 ^ 59
def prefixEnd_1180862 : Nat := 4983230072969 + 3 ^ 40 * 1180862 * 2
def baseEnd_1180862 : Nat := 404233195086442737129547

theorem tailTrace_1180862 : CollatzResearch.WordTrace tailWord_1180862 prefixEnd_1180862 404233195086442737129547 := by
  unfold tailWord_1180862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383696930993265502316105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28713050298630749345685893 5383696930993265502316105)
  ·
    refine ⟨4037772698244949126737079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5383696930993265502316105 4037772698244949126737079)
    ·
      refine ⟨6056659047367423690105619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4037772698244949126737079 6056659047367423690105619)
      ·
        refine ⟨9084988571051135535158429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056659047367423690105619 9084988571051135535158429)
        ·
          refine ⟨3406870714144175825684411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9084988571051135535158429 3406870714144175825684411)
          ·
            refine ⟨5110306071216263738526617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406870714144175825684411 5110306071216263738526617)
            ·
              refine ⟨3832729553412197803894963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110306071216263738526617 3832729553412197803894963)
              ·
                refine ⟨5749094330118296705842445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832729553412197803894963 5749094330118296705842445)
                ·
                  refine ⟨2155910373794361264690917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5749094330118296705842445 2155910373794361264690917)
                  ·
                    refine ⟨404233195086442737129547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155910373794361264690917 404233195086442737129547)
                    ·
                      rfl

theorem cell22_1180862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1180862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180862 prefixEnd_1180862 := by exact prefixLift 1180862
  have htrace : WordTrace (prefixWord ++ tailWord_1180862) baseStart_1180862 baseEnd_1180862 := by
    simpa [prefixWord, tailWord_1180862, baseEnd_1180862] using wordTrace_append hprefix tailTrace_1180862
  have hstable : (prefixWord ++ tailWord_1180862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180862).length < 2 ^ (prefixWord ++ tailWord_1180862).sum := by decide
  have hdescent : baseEnd_1180862 < baseStart_1180862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180890 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_1180890 : Nat := 118140960795 + 1180890 * 2 ^ 59
def prefixEnd_1180890 : Nat := 4983230072969 + 3 ^ 40 * 1180890 * 2
def baseEnd_1180890 : Nat := 404242780058659997429461

theorem tailTrace_1180890 : CollatzResearch.WordTrace tailWord_1180890 prefixEnd_1180890 404242780058659997429461 := by
  unfold tailWord_1180890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767649172961171200137031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28713731127896456533698749 10767649172961171200137031)
  ·
    refine ⟨16151473759441756800205547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10767649172961171200137031 16151473759441756800205547)
    ·
      refine ⟨24227210639162635200308321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16151473759441756800205547 24227210639162635200308321)
      ·
        refine ⟨18170407979371976400231241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24227210639162635200308321 18170407979371976400231241)
        ·
          refine ⟨13627805984528982300173431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18170407979371976400231241 13627805984528982300173431)
          ·
            refine ⟨20441708976793473450260147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627805984528982300173431 20441708976793473450260147)
            ·
              refine ⟨30662563465190210175390221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20441708976793473450260147 30662563465190210175390221)
              ·
                refine ⟨11498461299446328815771333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30662563465190210175390221 11498461299446328815771333)
                ·
                  refine ⟨2155961493646186652957125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11498461299446328815771333 2155961493646186652957125)
                  ·
                    refine ⟨404242780058659997429461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155961493646186652957125 404242780058659997429461)
                    ·
                      rfl

theorem cell22_1180890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1180890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180890 prefixEnd_1180890 := by exact prefixLift 1180890
  have htrace : WordTrace (prefixWord ++ tailWord_1180890) baseStart_1180890 baseEnd_1180890 := by
    simpa [prefixWord, tailWord_1180890, baseEnd_1180890] using wordTrace_append hprefix tailTrace_1180890
  have hstable : (prefixWord ++ tailWord_1180890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180890).length < 2 ^ (prefixWord ++ tailWord_1180890).sum := by decide
  have hdescent : baseEnd_1180890 < baseStart_1180890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180909 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1180909 : Nat := 118140960795 + 1180909 * 2 ^ 59
def prefixEnd_1180909 : Nat := 4983230072969 + 3 ^ 40 * 1180909 * 2
def baseEnd_1180909 : Nat := 404249284146950281204403

theorem tailTrace_1180909 : CollatzResearch.WordTrace tailWord_1180909 prefixEnd_1180909 404249284146950281204403 := by
  unfold tailWord_1180909
  simp only [CollatzResearch.WordTrace]
  refine ⟨43071289678775851045489781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28714193119183900696993187 43071289678775851045489781)
  ·
    refine ⟨4037933407385236035514667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43071289678775851045489781 4037933407385236035514667)
    ·
      refine ⟨6056900111077854053272001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4037933407385236035514667 6056900111077854053272001)
      ·
        refine ⟨4542675083308390539954001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6056900111077854053272001 4542675083308390539954001)
        ·
          refine ⟨3407006312481292904965501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4542675083308390539954001 3407006312481292904965501)
          ·
            refine ⟨1277627367180484839362063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3407006312481292904965501 1277627367180484839362063)
            ·
              refine ⟨1916441050770727259043095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277627367180484839362063 1916441050770727259043095)
              ·
                refine ⟨2874661576156090888564643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916441050770727259043095 2874661576156090888564643)
                ·
                  refine ⟨4311992364234136332846965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874661576156090888564643 4311992364234136332846965)
                  ·
                    refine ⟨404249284146950281204403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4311992364234136332846965 404249284146950281204403)
                    ·
                      rfl

theorem cell22_1180909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1180909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180909 prefixEnd_1180909 := by exact prefixLift 1180909
  have htrace : WordTrace (prefixWord ++ tailWord_1180909) baseStart_1180909 baseEnd_1180909 := by
    simpa [prefixWord, tailWord_1180909, baseEnd_1180909] using wordTrace_append hprefix tailTrace_1180909
  have hstable : (prefixWord ++ tailWord_1180909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180909).length < 2 ^ (prefixWord ++ tailWord_1180909).sum := by decide
  have hdescent : baseEnd_1180909 < baseStart_1180909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180954 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_1180954 : Nat := 118140960795 + 1180954 * 2 ^ 59
def prefixEnd_1180954 : Nat := 4983230072969 + 3 ^ 40 * 1180954 * 2
def baseEnd_1180954 : Nat := 404264688566585163829265

theorem tailTrace_1180954 : CollatzResearch.WordTrace tailWord_1180954 prefixEnd_1180954 404264688566585163829265 := by
  unfold tailWord_1180954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10768232740903205932719479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28715287309075215820585277 10768232740903205932719479)
  ·
    refine ⟨16152349111354808899079219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10768232740903205932719479 16152349111354808899079219)
    ·
      refine ⟨24228523667032213348618829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16152349111354808899079219 24228523667032213348618829)
      ·
        refine ⟨9085696375137080005732061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24228523667032213348618829 9085696375137080005732061)
        ·
          refine ⟨3407136140676405002149523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9085696375137080005732061 3407136140676405002149523)
          ·
            refine ⟨5110704211014607503224285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407136140676405002149523 5110704211014607503224285)
            ·
              refine ⟨1916514079130477813709107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5110704211014607503224285 1916514079130477813709107)
              ·
                refine ⟨2874771118695716720563661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916514079130477813709107 2874771118695716720563661)
                ·
                  refine ⟨1078039169510893770211373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2874771118695716720563661 1078039169510893770211373)
                  ·
                    refine ⟨404264688566585163829265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078039169510893770211373 404264688566585163829265)
                    ·
                      rfl

theorem cell22_1180954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_1180954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180954 prefixEnd_1180954 := by exact prefixLift 1180954
  have htrace : WordTrace (prefixWord ++ tailWord_1180954) baseStart_1180954 baseEnd_1180954 := by
    simpa [prefixWord, tailWord_1180954, baseEnd_1180954] using wordTrace_append hprefix tailTrace_1180954
  have hstable : (prefixWord ++ tailWord_1180954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180954).length < 2 ^ (prefixWord ++ tailWord_1180954).sum := by decide
  have hdescent : baseEnd_1180954 < baseStart_1180954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180997 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_1180997 : Nat := 118140960795 + 1180997 * 2 ^ 59
def prefixEnd_1180997 : Nat := 4983230072969 + 3 ^ 40 * 1180997 * 2
def baseEnd_1180997 : Nat := 404279408345347385004133

theorem tailTrace_1180997 : CollatzResearch.WordTrace tailWord_1180997 prefixEnd_1180997 404279408345347385004133 := by
  unfold tailWord_1180997
  simp only [CollatzResearch.WordTrace]
  refine ⟨43074499302457042074693245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28716332868304694716462163 43074499302457042074693245)
  ·
    refine ⟨16152937238421390778009967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43074499302457042074693245 16152937238421390778009967)
    ·
      refine ⟨24229405857632086167014951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16152937238421390778009967 24229405857632086167014951)
      ·
        refine ⟨36344108786448129250522427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24229405857632086167014951 36344108786448129250522427)
        ·
          refine ⟨54516163179672193875783641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36344108786448129250522427 54516163179672193875783641)
          ·
            refine ⟨40887122384754145406837731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54516163179672193875783641 40887122384754145406837731)
            ·
              refine ⟨61330683577131218110256597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40887122384754145406837731 61330683577131218110256597)
              ·
                refine ⟨1437437896339012924459139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61330683577131218110256597 1437437896339012924459139)
                ·
                  refine ⟨2156156844508519386688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437437896339012924459139 2156156844508519386688709)
                  ·
                    refine ⟨404279408345347385004133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156156844508519386688709 404279408345347385004133)
                    ·
                      rfl

theorem cell22_1180997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_1180997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1180997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1180997 prefixEnd_1180997 := by exact prefixLift 1180997
  have htrace : WordTrace (prefixWord ++ tailWord_1180997) baseStart_1180997 baseEnd_1180997 := by
    simpa [prefixWord, tailWord_1180997, baseEnd_1180997] using wordTrace_append hprefix tailTrace_1180997
  have hstable : (prefixWord ++ tailWord_1180997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180997).length < 2 ^ (prefixWord ++ tailWord_1180997).sum := by decide
  have hdescent : baseEnd_1180997 < baseStart_1180997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181005 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1181005 : Nat := 118140960795 + 1181005 * 2 ^ 59
def prefixEnd_1181005 : Nat := 4983230072969 + 3 ^ 40 * 1181005 * 2
def baseEnd_1181005 : Nat := 404282146908838030804109

theorem tailTrace_1181005 : CollatzResearch.WordTrace tailWord_1181005 prefixEnd_1181005 404282146908838030804109 := by
  unfold tailWord_1181005
  simp only [CollatzResearch.WordTrace]
  refine ⟨43074791086428059440984469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28716527390952039627322979 43074791086428059440984469)
  ·
    refine ⟨2019130832176315286296147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43074791086428059440984469 2019130832176315286296147)
    ·
      refine ⟨3028696248264472929444221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019130832176315286296147 3028696248264472929444221)
      ·
        refine ⟨1135761093099177348541583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3028696248264472929444221 1135761093099177348541583)
        ·
          refine ⟨1703641639648766022812375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135761093099177348541583 1703641639648766022812375)
          ·
            refine ⟨2555462459473149034218563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703641639648766022812375 2555462459473149034218563)
            ·
              refine ⟨3833193689209723551327845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555462459473149034218563 3833193689209723551327845)
              ·
                refine ⟨718723816726823165873971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3833193689209723551327845 718723816726823165873971)
                ·
                  refine ⟨1078085725090234748810957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718723816726823165873971 1078085725090234748810957)
                  ·
                    refine ⟨404282146908838030804109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078085725090234748810957 404282146908838030804109)
                    ·
                      rfl

theorem cell22_1181005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1181005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181005 prefixEnd_1181005 := by exact prefixLift 1181005
  have htrace : WordTrace (prefixWord ++ tailWord_1181005) baseStart_1181005 baseEnd_1181005 := by
    simpa [prefixWord, tailWord_1181005, baseEnd_1181005] using wordTrace_append hprefix tailTrace_1181005
  have hstable : (prefixWord ++ tailWord_1181005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181005).length < 2 ^ (prefixWord ++ tailWord_1181005).sum := by decide
  have hdescent : baseEnd_1181005 < baseStart_1181005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181012 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1181012 : Nat := 118140960795 + 1181012 * 2 ^ 59
def prefixEnd_1181012 : Nat := 4983230072969 + 3 ^ 40 * 1181012 * 2
def baseEnd_1181012 : Nat := 134761514383964115293029

theorem tailTrace_1181012 : CollatzResearch.WordTrace tailWord_1181012 prefixEnd_1181012 134761514383964115293029 := by
  unfold tailWord_1181012
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537523198701349818244645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28716697598268466424326193 21537523198701349818244645)
  ·
    refine ⟨4038285599756503090920871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21537523198701349818244645 4038285599756503090920871)
    ·
      refine ⟨6057428399634754636381307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4038285599756503090920871 6057428399634754636381307)
      ·
        refine ⟨9086142599452131954571961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057428399634754636381307 9086142599452131954571961)
        ·
          refine ⟨6814606949589098965928971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086142599452131954571961 6814606949589098965928971)
          ·
            refine ⟨10221910424383648448893457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6814606949589098965928971 10221910424383648448893457)
            ·
              refine ⟨7666432818287736336670093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10221910424383648448893457 7666432818287736336670093)
              ·
                refine ⟨2874912306857901126251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7666432818287736336670093 2874912306857901126251285)
                ·
                  refine ⟨134761514383964115293029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2874912306857901126251285 134761514383964115293029)
                  ·
                    rfl

theorem cell22_1181012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1181012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181012 prefixEnd_1181012 := by exact prefixLift 1181012
  have htrace : WordTrace (prefixWord ++ tailWord_1181012) baseStart_1181012 baseEnd_1181012 := by
    simpa [prefixWord, tailWord_1181012, baseEnd_1181012] using wordTrace_append hprefix tailTrace_1181012
  have hstable : (prefixWord ++ tailWord_1181012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181012).length < 2 ^ (prefixWord ++ tailWord_1181012).sum := by decide
  have hdescent : baseEnd_1181012 < baseStart_1181012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181027 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_1181027 : Nat := 118140960795 + 1181027 * 2 ^ 59
def prefixEnd_1181027 : Nat := 4983230072969 + 3 ^ 40 * 1181027 * 2
def baseEnd_1181027 : Nat := 404289677958437306754041

theorem tailTrace_1181027 : CollatzResearch.WordTrace tailWord_1181027 prefixEnd_1181027 404289677958437306754041 := by
  unfold tailWord_1181027
  simp only [CollatzResearch.WordTrace]
  refine ⟨43075593492348357198285335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28717062328232238132190223 43075593492348357198285335)
  ·
    refine ⟨64613390238522535797428003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43075593492348357198285335 64613390238522535797428003)
    ·
      refine ⟨96920085357783803696142005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64613390238522535797428003 96920085357783803696142005)
      ·
        refine ⟨9086258002292231596513313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96920085357783803696142005 9086258002292231596513313)
        ·
          refine ⟨6814693501719173697384985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086258002292231596513313 6814693501719173697384985)
          ·
            refine ⟨5111020126289380273038739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6814693501719173697384985 5111020126289380273038739)
            ·
              refine ⟨7666530189434070409558109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111020126289380273038739 7666530189434070409558109)
              ·
                refine ⟨2874948821037776403584291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7666530189434070409558109 2874948821037776403584291)
                ·
                  refine ⟨4312423231556664605376437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874948821037776403584291 4312423231556664605376437)
                  ·
                    refine ⟨404289677958437306754041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4312423231556664605376437 404289677958437306754041)
                    ·
                      rfl

theorem cell22_1181027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_1181027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181027 prefixEnd_1181027 := by exact prefixLift 1181027
  have htrace : WordTrace (prefixWord ++ tailWord_1181027) baseStart_1181027 baseEnd_1181027 := by
    simpa [prefixWord, tailWord_1181027, baseEnd_1181027] using wordTrace_append hprefix tailTrace_1181027
  have hstable : (prefixWord ++ tailWord_1181027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181027).length < 2 ^ (prefixWord ++ tailWord_1181027).sum := by decide
  have hdescent : baseEnd_1181027 < baseStart_1181027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181042 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1181042 : Nat := 118140960795 + 1181042 * 2 ^ 59
def prefixEnd_1181042 : Nat := 4983230072969 + 3 ^ 40 * 1181042 * 2
def baseEnd_1181042 : Nat := 404294812764982267628995

theorem tailTrace_1181042 : CollatzResearch.WordTrace tailWord_1181042 prefixEnd_1181042 404294812764982267628995 := by
  unfold tailWord_1181042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769035146823503690020345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28717427058196009840054253 10769035146823503690020345)
  ·
    refine ⟨8076776360117627767515259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10769035146823503690020345 8076776360117627767515259)
    ·
      refine ⟨12115164540176441651272889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8076776360117627767515259 12115164540176441651272889)
      ·
        refine ⟨9086373405132331238454667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12115164540176441651272889 9086373405132331238454667)
        ·
          refine ⟨13629560107698496857682001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9086373405132331238454667 13629560107698496857682001)
          ·
            refine ⟨10222170080773872643261501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13629560107698496857682001 10222170080773872643261501)
            ·
              refine ⟨3833313780290202241223063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10222170080773872643261501 3833313780290202241223063)
              ·
                refine ⟨5749970670435303361834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833313780290202241223063 5749970670435303361834595)
                ·
                  refine ⟨8624956005652955042751893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749970670435303361834595 8624956005652955042751893)
                  ·
                    refine ⟨404294812764982267628995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8624956005652955042751893 404294812764982267628995)
                    ·
                      rfl

theorem cell22_1181042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1181042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181042 prefixEnd_1181042 := by exact prefixLift 1181042
  have htrace : WordTrace (prefixWord ++ tailWord_1181042) baseStart_1181042 baseEnd_1181042 := by
    simpa [prefixWord, tailWord_1181042, baseEnd_1181042] using wordTrace_append hprefix tailTrace_1181042
  have hstable : (prefixWord ++ tailWord_1181042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181042).length < 2 ^ (prefixWord ++ tailWord_1181042).sum := by decide
  have hdescent : baseEnd_1181042 < baseStart_1181042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181106 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_1181106 : Nat := 118140960795 + 1181106 * 2 ^ 59
def prefixEnd_1181106 : Nat := 4983230072969 + 3 ^ 40 * 1181106 * 2
def baseEnd_1181106 : Nat := 404316721272907434028799

theorem tailTrace_1181106 : CollatzResearch.WordTrace tailWord_1181106 prefixEnd_1181106 404316721272907434028799 := by
  unfold tailWord_1181106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769618714765538422602793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28718983239374769126940781 10769618714765538422602793)
  ·
    refine ⟨8077214036074153816952095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10769618714765538422602793 8077214036074153816952095)
    ·
      refine ⟨12115821054111230725428143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8077214036074153816952095 12115821054111230725428143)
      ·
        refine ⟨18173731581166846088142215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12115821054111230725428143 18173731581166846088142215)
        ·
          refine ⟨27260597371750269132213323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18173731581166846088142215 27260597371750269132213323)
          ·
            refine ⟨40890896057625403698319985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27260597371750269132213323 40890896057625403698319985)
            ·
              refine ⟨30668172043219052773739989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40890896057625403698319985 30668172043219052773739989)
              ·
                refine ⟨718785282262946549384531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30668172043219052773739989 718785282262946549384531)
                ·
                  refine ⟨1078177923394419824076797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718785282262946549384531 1078177923394419824076797)
                  ·
                    refine ⟨404316721272907434028799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078177923394419824076797 404316721272907434028799)
                    ·
                      rfl

theorem cell22_1181106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_1181106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181106 prefixEnd_1181106 := by exact prefixLift 1181106
  have htrace : WordTrace (prefixWord ++ tailWord_1181106) baseStart_1181106 baseEnd_1181106 := by
    simpa [prefixWord, tailWord_1181106, baseEnd_1181106] using wordTrace_append hprefix tailTrace_1181106
  have hstable : (prefixWord ++ tailWord_1181106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181106).length < 2 ^ (prefixWord ++ tailWord_1181106).sum := by decide
  have hdescent : baseEnd_1181106 < baseStart_1181106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181177 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_1181177 : Nat := 118140960795 + 1181177 * 2 ^ 59
def prefixEnd_1181177 : Nat := 4983230072969 + 3 ^ 40 * 1181177 * 2
def baseEnd_1181177 : Nat := 404341026023886915503581

theorem tailTrace_1181177 : CollatzResearch.WordTrace tailWord_1181177 prefixEnd_1181177 404341026023886915503581 := by
  unfold tailWord_1181177
  simp only [CollatzResearch.WordTrace]
  refine ⟨43081064441804932816245785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28720709627869955210830523 43081064441804932816245785)
  ·
    refine ⟨32310798331353699612184339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43081064441804932816245785 32310798331353699612184339)
    ·
      refine ⟨48466197497030549418276509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32310798331353699612184339 48466197497030549418276509)
      ·
        refine ⟨18174824061386456031853691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48466197497030549418276509 18174824061386456031853691)
        ·
          refine ⟨27262236092079684047780537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18174824061386456031853691 27262236092079684047780537)
          ·
            refine ⟨20446677069059763035835403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27262236092079684047780537 20446677069059763035835403)
            ·
              refine ⟨30670015603589644553753105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20446677069059763035835403 30670015603589644553753105)
              ·
                refine ⟨23002511702692233415314829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30670015603589644553753105 23002511702692233415314829)
                ·
                  refine ⟨8625941888509587530743061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23002511702692233415314829 8625941888509587530743061)
                  ·
                    refine ⟨404341026023886915503581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8625941888509587530743061 404341026023886915503581)
                    ·
                      rfl

theorem cell22_1181177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_1181177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181177 prefixEnd_1181177 := by exact prefixLift 1181177
  have htrace : WordTrace (prefixWord ++ tailWord_1181177) baseStart_1181177 baseEnd_1181177 := by
    simpa [prefixWord, tailWord_1181177, baseEnd_1181177] using wordTrace_append hprefix tailTrace_1181177
  have hstable : (prefixWord ++ tailWord_1181177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181177).length < 2 ^ (prefixWord ++ tailWord_1181177).sum := by decide
  have hdescent : baseEnd_1181177 < baseStart_1181177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181181 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 4]
def baseStart_1181181 : Nat := 118140960795 + 1181181 * 2 ^ 59
def prefixEnd_1181181 : Nat := 4983230072969 + 3 ^ 40 * 1181181 * 2
def baseEnd_1181181 : Nat := 134780798435210746134523

theorem tailTrace_1181181 : CollatzResearch.WordTrace tailWord_1181181 prefixEnd_1181181 134780798435210746134523 := by
  unfold tailWord_1181181
  simp only [CollatzResearch.WordTrace]
  refine ⟨43081210333790441499391397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28720806889193627666260931 43081210333790441499391397)
  ·
    refine ⟨8077726937585707781135887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43081210333790441499391397 8077726937585707781135887)
    ·
      refine ⟨12116590406378561671703831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8077726937585707781135887 12116590406378561671703831)
      ·
        refine ⟨18174885609567842507555747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12116590406378561671703831 18174885609567842507555747)
        ·
          refine ⟨27262328414351763761333621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18174885609567842507555747 27262328414351763761333621)
          ·
            refine ⟨2555843288845477852625027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27262328414351763761333621 2555843288845477852625027)
            ·
              refine ⟨3833764933268216778937541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555843288845477852625027 3833764933268216778937541)
              ·
                refine ⟨718830924987790646050789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3833764933268216778937541 718830924987790646050789)
                ·
                  refine ⟨134780798435210746134523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718830924987790646050789 134780798435210746134523)
                  ·
                    rfl

theorem cell22_1181181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_1181181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181181 prefixEnd_1181181 := by exact prefixLift 1181181
  have htrace : WordTrace (prefixWord ++ tailWord_1181181) baseStart_1181181 baseEnd_1181181 := by
    simpa [prefixWord, tailWord_1181181, baseEnd_1181181] using wordTrace_append hprefix tailTrace_1181181
  have hstable : (prefixWord ++ tailWord_1181181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181181).length < 2 ^ (prefixWord ++ tailWord_1181181).sum := by decide
  have hdescent : baseEnd_1181181 < baseStart_1181181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181196 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1181196 : Nat := 118140960795 + 1181196 * 2 ^ 59
def prefixEnd_1181196 : Nat := 4983230072969 + 3 ^ 40 * 1181196 * 2
def baseEnd_1181196 : Nat := 404347530112177199278523

theorem tailTrace_1181196 : CollatzResearch.WordTrace tailWord_1181196 prefixEnd_1181196 404347530112177199278523 := by
  unfold tailWord_1181196
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540878714368049530593721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28721171619157399374124961 21540878714368049530593721)
  ·
    refine ⟨16155659035776037147945291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21540878714368049530593721 16155659035776037147945291)
    ·
      refine ⟨24233488553664055721917937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16155659035776037147945291 24233488553664055721917937)
      ·
        refine ⟨18175116415248041791438453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24233488553664055721917937 18175116415248041791438453)
        ·
          refine ⟨1703917163929503917947355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18175116415248041791438453 1703917163929503917947355)
          ·
            refine ⟨2555875745894255876921033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703917163929503917947355 2555875745894255876921033)
            ·
              refine ⟨1916906809420691907690775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555875745894255876921033 1916906809420691907690775)
              ·
                refine ⟨2875360214131037861536163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916906809420691907690775 2875360214131037861536163)
                ·
                  refine ⟨4313040321196556792304245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875360214131037861536163 4313040321196556792304245)
                  ·
                    refine ⟨404347530112177199278523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4313040321196556792304245 404347530112177199278523)
                    ·
                      rfl

theorem cell22_1181196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1181196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181196 prefixEnd_1181196 := by exact prefixLift 1181196
  have htrace : WordTrace (prefixWord ++ tailWord_1181196) baseStart_1181196 baseEnd_1181196 := by
    simpa [prefixWord, tailWord_1181196, baseEnd_1181196] using wordTrace_append hprefix tailTrace_1181196
  have hstable : (prefixWord ++ tailWord_1181196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181196).length < 2 ^ (prefixWord ++ tailWord_1181196).sum := by decide
  have hdescent : baseEnd_1181196 < baseStart_1181196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181230 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1181230 : Nat := 118140960795 + 1181230 * 2 ^ 59
def prefixEnd_1181230 : Nat := 4983230072969 + 3 ^ 40 * 1181230 * 2
def baseEnd_1181230 : Nat := 404359169007012443928419

theorem tailTrace_1181230 : CollatzResearch.WordTrace tailWord_1181230 prefixEnd_1181230 404359169007012443928419 := by
  unfold tailWord_1181230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385374688826615358490643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28721998340408615245283429 5385374688826615358490643)
  ·
    refine ⟨8078062033239923037735965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5385374688826615358490643 8078062033239923037735965)
    ·
      refine ⟨3029273262464971139150987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8078062033239923037735965 3029273262464971139150987)
      ·
        refine ⟨4543909893697456708726481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029273262464971139150987 4543909893697456708726481)
        ·
          refine ⟨3407932420273092531544861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4543909893697456708726481 3407932420273092531544861)
          ·
            refine ⟨1277974657602409699329323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3407932420273092531544861 1277974657602409699329323)
            ·
              refine ⟨1916961986403614548993985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277974657602409699329323 1916961986403614548993985)
              ·
                refine ⟨1437721489802710911745489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916961986403614548993985 1437721489802710911745489)
                ·
                  refine ⟨1078291117352033183809117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1437721489802710911745489 1078291117352033183809117)
                  ·
                    refine ⟨404359169007012443928419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078291117352033183809117 404359169007012443928419)
                    ·
                      rfl

theorem cell22_1181230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1181230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181230 prefixEnd_1181230 := by exact prefixLift 1181230
  have htrace : WordTrace (prefixWord ++ tailWord_1181230) baseStart_1181230 baseEnd_1181230 := by
    simpa [prefixWord, tailWord_1181230, baseEnd_1181230] using wordTrace_append hprefix tailTrace_1181230
  have hstable : (prefixWord ++ tailWord_1181230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181230).length < 2 ^ (prefixWord ++ tailWord_1181230).sum := by decide
  have hdescent : baseEnd_1181230 < baseStart_1181230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181241 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_1181241 : Nat := 118140960795 + 1181241 * 2 ^ 59
def prefixEnd_1181241 : Nat := 4983230072969 + 3 ^ 40 * 1181241 * 2
def baseEnd_1181241 : Nat := 404362934531812081903385

theorem tailTrace_1181241 : CollatzResearch.WordTrace tailWord_1181241 prefixEnd_1181241 404362934531812081903385 := by
  unfold tailWord_1181241
  simp only [CollatzResearch.WordTrace]
  refine ⟨43083398713573071746575577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28722265809048714497717051 43083398713573071746575577)
  ·
    refine ⟨32312549035179803809931683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43083398713573071746575577 32312549035179803809931683)
    ·
      refine ⟨48468823552769705714897525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32312549035179803809931683 48468823552769705714897525)
      ·
        refine ⟨4543952208072159910771643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48468823552769705714897525 4543952208072159910771643)
        ·
          refine ⟨6815928312108239866157465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543952208072159910771643 6815928312108239866157465)
          ·
            refine ⟨5111946234081179899618099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6815928312108239866157465 5111946234081179899618099)
            ·
              refine ⟨7667919351121769849427149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111946234081179899618099 7667919351121769849427149)
              ·
                refine ⟨2875469756670663693535181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7667919351121769849427149 2875469756670663693535181)
                ·
                  refine ⟨1078301158751498885075693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2875469756670663693535181 1078301158751498885075693)
                  ·
                    refine ⟨404362934531812081903385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078301158751498885075693 404362934531812081903385)
                    ·
                      rfl

theorem cell22_1181241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_1181241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181241 prefixEnd_1181241 := by exact prefixLift 1181241
  have htrace : WordTrace (prefixWord ++ tailWord_1181241) baseStart_1181241 baseEnd_1181241 := by
    simpa [prefixWord, tailWord_1181241, baseEnd_1181241] using wordTrace_append hprefix tailTrace_1181241
  have hstable : (prefixWord ++ tailWord_1181241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181241).length < 2 ^ (prefixWord ++ tailWord_1181241).sum := by decide
  have hdescent : baseEnd_1181241 < baseStart_1181241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181344 : List Nat := [2, 1, 1, 4, 3, 11]
def baseStart_1181344 : Nat := 118140960795 + 1181344 * 2 ^ 59
def prefixEnd_1181344 : Nat := 4983230072969 + 3 ^ 40 * 1181344 * 2
def baseEnd_1181344 : Nat := 4992570290577211686149

theorem tailTrace_1181344 : CollatzResearch.WordTrace tailWord_1181344 prefixEnd_1181344 4992570290577211686149 := by
  unfold tailWord_1181344
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543577716099960168787543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28724770288133280225050057 21543577716099960168787543)
  ·
    refine ⟨32315366574149940253181315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21543577716099960168787543 32315366574149940253181315)
    ·
      refine ⟨48473049861224910379771973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32315366574149940253181315 48473049861224910379771973)
      ·
        refine ⟨9088696848979670696207245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48473049861224910379771973 9088696848979670696207245)
        ·
          refine ⟨3408261318367376511077717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9088696848979670696207245 3408261318367376511077717)
          ·
            refine ⟨4992570290577211686149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3408261318367376511077717 4992570290577211686149)
            ·
              rfl

theorem cell22_1181344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 11].length) (baseStart_1181344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181344 prefixEnd_1181344 := by exact prefixLift 1181344
  have htrace : WordTrace (prefixWord ++ tailWord_1181344) baseStart_1181344 baseEnd_1181344 := by
    simpa [prefixWord, tailWord_1181344, baseEnd_1181344] using wordTrace_append hprefix tailTrace_1181344
  have hstable : (prefixWord ++ tailWord_1181344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181344).length < 2 ^ (prefixWord ++ tailWord_1181344).sum := by decide
  have hdescent : baseEnd_1181344 < baseStart_1181344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181348 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1181348 : Nat := 118140960795 + 1181348 * 2 ^ 59
def prefixEnd_1181348 : Nat := 4983230072969 + 3 ^ 40 * 1181348 * 2
def baseEnd_1181348 : Nat := 404399562818499469478057

theorem tailTrace_1181348 : CollatzResearch.WordTrace tailWord_1181348 prefixEnd_1181348 404399562818499469478057 := by
  unfold tailWord_1181348
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543650662092714510360349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28724867549456952680480465 21543650662092714510360349)
  ·
    refine ⟨8078868998284767941385131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21543650662092714510360349 8078868998284767941385131)
    ·
      refine ⟨12118303497427151912077697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078868998284767941385131 12118303497427151912077697)
      ·
        refine ⟨9088727623070363934058273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12118303497427151912077697 9088727623070363934058273)
        ·
          refine ⟨6816545717302772950543705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9088727623070363934058273 6816545717302772950543705)
          ·
            refine ⟨5112409287977079712907779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816545717302772950543705 5112409287977079712907779)
            ·
              refine ⟨7668613931965619569361669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112409287977079712907779 7668613931965619569361669)
              ·
                refine ⟨1437865112243553669255313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7668613931965619569361669 1437865112243553669255313)
                ·
                  refine ⟨1078398834182665251941485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1437865112243553669255313 1078398834182665251941485)
                  ·
                    refine ⟨404399562818499469478057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078398834182665251941485 404399562818499469478057)
                    ·
                      rfl

theorem cell22_1181348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1181348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181348 prefixEnd_1181348 := by exact prefixLift 1181348
  have htrace : WordTrace (prefixWord ++ tailWord_1181348) baseStart_1181348 baseEnd_1181348 := by
    simpa [prefixWord, tailWord_1181348, baseEnd_1181348] using wordTrace_append hprefix tailTrace_1181348
  have hstable : (prefixWord ++ tailWord_1181348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181348).length < 2 ^ (prefixWord ++ tailWord_1181348).sum := by decide
  have hdescent : baseEnd_1181348 < baseStart_1181348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181423 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 5]
def baseStart_1181423 : Nat := 118140960795 + 1181423 * 2 ^ 59
def prefixEnd_1181423 : Nat := 4983230072969 + 3 ^ 40 * 1181423 * 2
def baseEnd_1181423 : Nat := 134808412283741424617609

theorem tailTrace_1181423 : CollatzResearch.WordTrace tailWord_1181423 prefixEnd_1181423 134808412283741424617609 := by
  unfold tailWord_1181423
  simp only [CollatzResearch.WordTrace]
  refine ⟨43090036798913716829700923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28726691199275811219800615 43090036798913716829700923)
  ·
    refine ⟨64635055198370575244551385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43090036798913716829700923 64635055198370575244551385)
    ·
      refine ⟨48476291398777931433413539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64635055198370575244551385 48476291398777931433413539)
      ·
        refine ⟨72714437098166897150120309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48476291398777931433413539 72714437098166897150120309)
        ·
          refine ⟨6816978477953146607823779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72714437098166897150120309 6816978477953146607823779)
          ·
            refine ⟨10225467716929719911735669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6816978477953146607823779 10225467716929719911735669)
            ·
              refine ⟨958637598462161241725219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10225467716929719911735669 958637598462161241725219)
              ·
                refine ⟨1437956397693241862587829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958637598462161241725219 1437956397693241862587829)
                ·
                  refine ⟨134808412283741424617609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437956397693241862587829 134808412283741424617609)
                  ·
                    rfl

theorem cell22_1181423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 5].length) (baseStart_1181423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181423 prefixEnd_1181423 := by exact prefixLift 1181423
  have htrace : WordTrace (prefixWord ++ tailWord_1181423) baseStart_1181423 baseEnd_1181423 := by
    simpa [prefixWord, tailWord_1181423, baseEnd_1181423] using wordTrace_append hprefix tailTrace_1181423
  have hstable : (prefixWord ++ tailWord_1181423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181423).length < 2 ^ (prefixWord ++ tailWord_1181423).sum := by decide
  have hdescent : baseEnd_1181423 < baseStart_1181423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181446 : List Nat := [6, 2, 2, 1, 2, 1, 8]
def baseStart_1181446 : Nat := 118140960795 + 1181446 * 2 ^ 59
def prefixEnd_1181446 : Nat := 4983230072969 + 3 ^ 40 * 1181446 * 2
def baseEnd_1181446 : Nat := 14979004082268884463991

theorem tailTrace_1181446 : CollatzResearch.WordTrace tailWord_1181446 prefixEnd_1181446 14979004082268884463991 := by
  unfold tailWord_1181446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346589864932199742430881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28727250451886927838525461 1346589864932199742430881)
  ·
    refine ⟨1009942398699149806823161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1346589864932199742430881 1009942398699149806823161)
    ·
      refine ⟨757456799024362355117371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1009942398699149806823161 757456799024362355117371)
      ·
        refine ⟨1136185198536543532676057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757456799024362355117371 1136185198536543532676057)
        ·
          refine ⟨852138898902407649507043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136185198536543532676057 852138898902407649507043)
          ·
            refine ⟨1278208348353611474260565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852138898902407649507043 1278208348353611474260565)
            ·
              refine ⟨14979004082268884463991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1278208348353611474260565 14979004082268884463991)
              ·
                rfl

theorem cell22_1181446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 8].length) (baseStart_1181446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181446 prefixEnd_1181446 := by exact prefixLift 1181446
  have htrace : WordTrace (prefixWord ++ tailWord_1181446) baseStart_1181446 baseEnd_1181446 := by
    simpa [prefixWord, tailWord_1181446, baseEnd_1181446] using wordTrace_append hprefix tailTrace_1181446
  have hstable : (prefixWord ++ tailWord_1181446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181446).length < 2 ^ (prefixWord ++ tailWord_1181446).sum := by decide
  have hdescent : baseEnd_1181446 < baseStart_1181446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181496 : List Nat := [2, 1, 2, 1, 3, 3, 2, 8]
def baseStart_1181496 : Nat := 118140960795 + 1181496 * 2 ^ 59
def prefixEnd_1181496 : Nat := 4983230072969 + 3 ^ 40 * 1181496 * 2
def baseEnd_1181496 : Nat := 44938914027008490753067

theorem tailTrace_1181496 : CollatzResearch.WordTrace tailWord_1181496 prefixEnd_1181496 44938914027008490753067 := by
  unfold tailWord_1181496
  simp only [CollatzResearch.WordTrace]
  refine ⟨21546349663824625148554171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28728466218432833531405561 21546349663824625148554171)
  ·
    refine ⟨32319524495736937722831257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21546349663824625148554171 32319524495736937722831257)
    ·
      refine ⟨24239643371802703292123443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32319524495736937722831257 24239643371802703292123443)
      ·
        refine ⟨36359465057704054938185165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24239643371802703292123443 36359465057704054938185165)
        ·
          refine ⟨13634799396639020601819437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36359465057704054938185165 13634799396639020601819437)
          ·
            refine ⟨5113049773739632725682289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13634799396639020601819437 5113049773739632725682289)
            ·
              refine ⟨3834787330304724544261717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5113049773739632725682289 3834787330304724544261717)
              ·
                refine ⟨44938914027008490753067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3834787330304724544261717 44938914027008490753067)
                ·
                  rfl

theorem cell22_1181496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_1181496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181496 prefixEnd_1181496 := by exact prefixLift 1181496
  have htrace : WordTrace (prefixWord ++ tailWord_1181496) baseStart_1181496 baseEnd_1181496 := by
    simpa [prefixWord, tailWord_1181496, baseEnd_1181496] using wordTrace_append hprefix tailTrace_1181496
  have hstable : (prefixWord ++ tailWord_1181496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181496).length < 2 ^ (prefixWord ++ tailWord_1181496).sum := by decide
  have hdescent : baseEnd_1181496 < baseStart_1181496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181498 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_1181498 : Nat := 118140960795 + 1181498 * 2 ^ 59
def prefixEnd_1181498 : Nat := 4983230072969 + 3 ^ 40 * 1181498 * 2
def baseEnd_1181498 : Nat := 404450910883949078227597

theorem tailTrace_1181498 : CollatzResearch.WordTrace tailWord_1181498 prefixEnd_1181498 404450910883949078227597 := by
  unfold tailWord_1181498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10773193068410501159670287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28728514849094669759120765 10773193068410501159670287)
  ·
    refine ⟨16159789602615751739505431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10773193068410501159670287 16159789602615751739505431)
    ·
      refine ⟨24239684403923627609258147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16159789602615751739505431 24239684403923627609258147)
      ·
        refine ⟨36359526605885441413887221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24239684403923627609258147 36359526605885441413887221)
        ·
          refine ⟨3408705619301760132551927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36359526605885441413887221 3408705619301760132551927)
          ·
            refine ⟨5113058428952640198827891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408705619301760132551927 5113058428952640198827891)
            ·
              refine ⟨7669587643428960298241837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113058428952640198827891 7669587643428960298241837)
              ·
                refine ⟨2876095366285860111840689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7669587643428960298241837 2876095366285860111840689)
                ·
                  refine ⟨2157071524714395083880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876095366285860111840689 2157071524714395083880517)
                  ·
                    refine ⟨404450910883949078227597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2157071524714395083880517 404450910883949078227597)
                    ·
                      rfl

theorem cell22_1181498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_1181498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181498 prefixEnd_1181498 := by exact prefixLift 1181498
  have htrace : WordTrace (prefixWord ++ tailWord_1181498) baseStart_1181498 baseEnd_1181498 := by
    simpa [prefixWord, tailWord_1181498, baseEnd_1181498] using wordTrace_append hprefix tailTrace_1181498
  have hstable : (prefixWord ++ tailWord_1181498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181498).length < 2 ^ (prefixWord ++ tailWord_1181498).sum := by decide
  have hdescent : baseEnd_1181498 < baseStart_1181498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181517 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1181517 : Nat := 118140960795 + 1181517 * 2 ^ 59
def prefixEnd_1181517 : Nat := 4983230072969 + 3 ^ 40 * 1181517 * 2
def baseEnd_1181517 : Nat := 404457414972239362002539

theorem tailTrace_1181517 : CollatzResearch.WordTrace tailWord_1181517 prefixEnd_1181517 404457414972239362002539 := by
  unfold tailWord_1181517
  simp only [CollatzResearch.WordTrace]
  refine ⟨43093465260573170883622805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28728976840382113922415203 43093465260573170883622805)
  ·
    refine ⟨2020006184089367385169819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43093465260573170883622805 2020006184089367385169819)
    ·
      refine ⟨3030009276134051077754729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020006184089367385169819 3030009276134051077754729)
      ·
        refine ⟨2272506957100538308316047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3030009276134051077754729 2272506957100538308316047)
        ·
          refine ⟨3408760435650807462474071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272506957100538308316047 3408760435650807462474071)
          ·
            refine ⟨5113140653476211193711107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408760435650807462474071 5113140653476211193711107)
            ·
              refine ⟨7669710980214316790566661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113140653476211193711107 7669710980214316790566661)
              ·
                refine ⟨1438070808790184398231249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7669710980214316790566661 1438070808790184398231249)
                ·
                  refine ⟨1078553106592638298673437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1438070808790184398231249 1078553106592638298673437)
                  ·
                    refine ⟨404457414972239362002539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078553106592638298673437 404457414972239362002539)
                    ·
                      rfl

theorem cell22_1181517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1181517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181517 prefixEnd_1181517 := by exact prefixLift 1181517
  have htrace : WordTrace (prefixWord ++ tailWord_1181517) baseStart_1181517 baseEnd_1181517 := by
    simpa [prefixWord, tailWord_1181517, baseEnd_1181517] using wordTrace_append hprefix tailTrace_1181517
  have hstable : (prefixWord ++ tailWord_1181517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181517).length < 2 ^ (prefixWord ++ tailWord_1181517).sum := by decide
  have hdescent : baseEnd_1181517 < baseStart_1181517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181541 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 9]
def baseStart_1181541 : Nat := 118140960795 + 1181541 * 2 ^ 59
def prefixEnd_1181541 : Nat := 4983230072969 + 3 ^ 40 * 1181541 * 2
def baseEnd_1181541 : Nat := 134821876887570433134155

theorem tailTrace_1181541 : CollatzResearch.WordTrace tailWord_1181541 prefixEnd_1181541 134821876887570433134155 := by
  unfold tailWord_1181541
  simp only [CollatzResearch.WordTrace]
  refine ⟨43094340612486222982496477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28729560408324148654997651 43094340612486222982496477)
  ·
    refine ⟨16160377729682333618436179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43094340612486222982496477 16160377729682333618436179)
    ·
      refine ⟨24240566594523500427654269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16160377729682333618436179 24240566594523500427654269)
      ·
        refine ⟨9090212472946312660370351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24240566594523500427654269 9090212472946312660370351)
        ·
          refine ⟨13635318709419468990555527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9090212472946312660370351 13635318709419468990555527)
          ·
            refine ⟨20452978064129203485833291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13635318709419468990555527 20452978064129203485833291)
            ·
              refine ⟨30679467096193805228749937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20452978064129203485833291 30679467096193805228749937)
              ·
                refine ⟨23009600322145353921562453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30679467096193805228749937 23009600322145353921562453)
                ·
                  refine ⟨134821876887570433134155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23009600322145353921562453 134821876887570433134155)
                  ·
                    rfl

theorem cell22_1181541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_1181541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181541 prefixEnd_1181541 := by exact prefixLift 1181541
  have htrace : WordTrace (prefixWord ++ tailWord_1181541) baseStart_1181541 baseEnd_1181541 := by
    simpa [prefixWord, tailWord_1181541, baseEnd_1181541] using wordTrace_append hprefix tailTrace_1181541
  have hstable : (prefixWord ++ tailWord_1181541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181541).length < 2 ^ (prefixWord ++ tailWord_1181541).sum := by decide
  have hdescent : baseEnd_1181541 < baseStart_1181541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181618 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1181618 : Nat := 118140960795 + 1181618 * 2 ^ 59
def prefixEnd_1181618 : Nat := 4983230072969 + 3 ^ 40 * 1181618 * 2
def baseEnd_1181618 : Nat := 404491989336308765227229

theorem tailTrace_1181618 : CollatzResearch.WordTrace tailWord_1181618 prefixEnd_1181618 404491989336308765227229 := by
  unfold tailWord_1181618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10774287258301816283262377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28731432688804843422033005 10774287258301816283262377)
  ·
    refine ⟨8080715443726362212446783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10774287258301816283262377 8080715443726362212446783)
    ·
      refine ⟨12121073165589543318670175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8080715443726362212446783 12121073165589543318670175)
      ·
        refine ⟨18181609748384314978005263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12121073165589543318670175 18181609748384314978005263)
        ·
          refine ⟨27272414622576472467007895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18181609748384314978005263 27272414622576472467007895)
          ·
            refine ⟨40908621933864708700511843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27272414622576472467007895 40908621933864708700511843)
            ·
              refine ⟨61362932900797063050767765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40908621933864708700511843 61362932900797063050767765)
              ·
                refine ⟨2876387479724862330504739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61362932900797063050767765 2876387479724862330504739)
                ·
                  refine ⟨4314581219587293495757109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876387479724862330504739 4314581219587293495757109)
                  ·
                    refine ⟨404491989336308765227229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4314581219587293495757109 404491989336308765227229)
                    ·
                      rfl

theorem cell22_1181618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1181618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181618 prefixEnd_1181618 := by exact prefixLift 1181618
  have htrace : WordTrace (prefixWord ++ tailWord_1181618) baseStart_1181618 baseEnd_1181618 := by
    simpa [prefixWord, tailWord_1181618, baseEnd_1181618] using wordTrace_append hprefix tailTrace_1181618
  have hstable : (prefixWord ++ tailWord_1181618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181618).length < 2 ^ (prefixWord ++ tailWord_1181618).sum := by decide
  have hdescent : baseEnd_1181618 < baseStart_1181618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181652 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1181652 : Nat := 118140960795 + 1181652 * 2 ^ 59
def prefixEnd_1181652 : Nat := 4983230072969 + 3 ^ 40 * 1181652 * 2
def baseEnd_1181652 : Nat := 404503628231144009877125

theorem tailTrace_1181652 : CollatzResearch.WordTrace tailWord_1181652 prefixEnd_1181652 404503628231144009877125 := by
  unfold tailWord_1181652
  simp only [CollatzResearch.WordTrace]
  refine ⟨21549194557542044469893605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28732259410056059293191473 21549194557542044469893605)
  ·
    refine ⟨4040473979539133338105051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21549194557542044469893605 4040473979539133338105051)
    ·
      refine ⟨6060710969308700007157577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040473979539133338105051 6060710969308700007157577)
      ·
        refine ⟨4545533226981525005368183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6060710969308700007157577 4545533226981525005368183)
        ·
          refine ⟨6818299840472287508052275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545533226981525005368183 6818299840472287508052275)
          ·
            refine ⟨10227449760708431262078413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818299840472287508052275 10227449760708431262078413)
            ·
              refine ⟨3835293660265661723279405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10227449760708431262078413 3835293660265661723279405)
              ·
                refine ⟨1438235122599623146229777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3835293660265661723279405 1438235122599623146229777)
                ·
                  refine ⟨1078676341949717359672333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1438235122599623146229777 1078676341949717359672333)
                  ·
                    refine ⟨404503628231144009877125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078676341949717359672333 404503628231144009877125)
                    ·
                      rfl

theorem cell22_1181652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1181652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181652 prefixEnd_1181652 := by exact prefixLift 1181652
  have htrace : WordTrace (prefixWord ++ tailWord_1181652) baseStart_1181652 baseEnd_1181652 := by
    simpa [prefixWord, tailWord_1181652, baseEnd_1181652] using wordTrace_append hprefix tailTrace_1181652
  have hstable : (prefixWord ++ tailWord_1181652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181652).length < 2 ^ (prefixWord ++ tailWord_1181652).sum := by decide
  have hdescent : baseEnd_1181652 < baseStart_1181652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181693 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 7]
def baseStart_1181693 : Nat := 118140960795 + 1181693 * 2 ^ 59
def prefixEnd_1181693 : Nat := 4983230072969 + 3 ^ 40 * 1181693 * 2
def baseEnd_1181693 : Nat := 134839221123011189867333

theorem tailTrace_1181693 : CollatzResearch.WordTrace tailWord_1181693 prefixEnd_1181693 134839221123011189867333 := by
  unfold tailWord_1181693
  simp only [CollatzResearch.WordTrace]
  refine ⟨43099884507935552942029733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28733256338623701961353155 43099884507935552942029733)
  ·
    refine ⟨8081228345237916176630575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43099884507935552942029733 8081228345237916176630575)
    ·
      refine ⟨12121842517856874264945863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8081228345237916176630575 12121842517856874264945863)
      ·
        refine ⟨18182763776785311397418795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12121842517856874264945863 18182763776785311397418795)
        ·
          refine ⟨27274145665177967096128193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18182763776785311397418795 27274145665177967096128193)
          ·
            refine ⟨20455609248883475322096145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27274145665177967096128193 20455609248883475322096145)
            ·
              refine ⟨15341706936662606491572109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20455609248883475322096145 15341706936662606491572109)
              ·
                refine ⟨5753140101248477434339541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15341706936662606491572109 5753140101248477434339541)
                ·
                  refine ⟨134839221123011189867333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5753140101248477434339541 134839221123011189867333)
                  ·
                    rfl

theorem cell22_1181693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_1181693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181693 prefixEnd_1181693 := by exact prefixLift 1181693
  have htrace : WordTrace (prefixWord ++ tailWord_1181693) baseStart_1181693 baseEnd_1181693 := by
    simpa [prefixWord, tailWord_1181693, baseEnd_1181693] using wordTrace_append hprefix tailTrace_1181693
  have hstable : (prefixWord ++ tailWord_1181693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181693).length < 2 ^ (prefixWord ++ tailWord_1181693).sum := by decide
  have hdescent : baseEnd_1181693 < baseStart_1181693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181710 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1181710 : Nat := 118140960795 + 1181710 * 2 ^ 59
def prefixEnd_1181710 : Nat := 4983230072969 + 3 ^ 40 * 1181710 * 2
def baseEnd_1181710 : Nat := 134841160938817063975649

theorem tailTrace_1181710 : CollatzResearch.WordTrace tailWord_1181710 prefixEnd_1181710 134841160938817063975649 := by
  unfold tailWord_1181710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387563068609245605674823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28733669699249309896932389 5387563068609245605674823)
  ·
    refine ⟨8081344602913868408512235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5387563068609245605674823 8081344602913868408512235)
    ·
      refine ⟨12122016904370802612768353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8081344602913868408512235 12122016904370802612768353)
      ·
        refine ⟨9091512678278101959576265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12122016904370802612768353 9091512678278101959576265)
        ·
          refine ⟨6818634508708576469682199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9091512678278101959576265 6818634508708576469682199)
          ·
            refine ⟨10227951763062864704523299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818634508708576469682199 10227951763062864704523299)
            ·
              refine ⟨15341927644594297056784949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10227951763062864704523299 15341927644594297056784949)
              ·
                refine ⟨1438305716680715349073589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15341927644594297056784949 1438305716680715349073589)
                ·
                  refine ⟨134841160938817063975649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1438305716680715349073589 134841160938817063975649)
                  ·
                    rfl

theorem cell22_1181710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1181710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181710 prefixEnd_1181710 := by exact prefixLift 1181710
  have htrace : WordTrace (prefixWord ++ tailWord_1181710) baseStart_1181710 baseEnd_1181710 := by
    simpa [prefixWord, tailWord_1181710, baseEnd_1181710] using wordTrace_append hprefix tailTrace_1181710
  have hstable : (prefixWord ++ tailWord_1181710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181710).length < 2 ^ (prefixWord ++ tailWord_1181710).sum := by decide
  have hdescent : baseEnd_1181710 < baseStart_1181710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181785 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_1181785 : Nat := 118140960795 + 1181785 * 2 ^ 59
def prefixEnd_1181785 : Nat := 4983230072969 + 3 ^ 40 * 1181785 * 2
def baseEnd_1181785 : Nat := 404549156849175996301717

theorem tailTrace_1181785 : CollatzResearch.WordTrace tailWord_1181785 prefixEnd_1181785 404549156849175996301717 := by
  unfold tailWord_1181785
  simp only [CollatzResearch.WordTrace]
  refine ⟨43103240023602252654378809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28735493349068168436252539 43103240023602252654378809)
  ·
    refine ⟨32327430017701689490784107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43103240023602252654378809 32327430017701689490784107)
    ·
      refine ⟨48491145026552534236176161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32327430017701689490784107 48491145026552534236176161)
      ·
        refine ⟨36368358769914400677132121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48491145026552534236176161 36368358769914400677132121)
        ·
          refine ⟨27276269077435800507849091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36368358769914400677132121 27276269077435800507849091)
          ·
            refine ⟨40914403616153700761773637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27276269077435800507849091 40914403616153700761773637)
            ·
              refine ⟨7671450678028818892832557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40914403616153700761773637 7671450678028818892832557)
              ·
                refine ⟨2876794004260807084812209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7671450678028818892832557 2876794004260807084812209)
                ·
                  refine ⟨2157595503195605313609157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876794004260807084812209 2157595503195605313609157)
                  ·
                    refine ⟨404549156849175996301717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2157595503195605313609157 404549156849175996301717)
                    ·
                      rfl

theorem cell22_1181785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_1181785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181785 prefixEnd_1181785 := by exact prefixLift 1181785
  have htrace : WordTrace (prefixWord ++ tailWord_1181785) baseStart_1181785 baseEnd_1181785 := by
    simpa [prefixWord, tailWord_1181785, baseEnd_1181785] using wordTrace_append hprefix tailTrace_1181785
  have hstable : (prefixWord ++ tailWord_1181785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181785).length < 2 ^ (prefixWord ++ tailWord_1181785).sum := by decide
  have hdescent : baseEnd_1181785 < baseStart_1181785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181821 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_1181821 : Nat := 118140960795 + 1181821 * 2 ^ 59
def prefixEnd_1181821 : Nat := 4983230072969 + 3 ^ 40 * 1181821 * 2
def baseEnd_1181821 : Nat := 404561480384883902401607

theorem tailTrace_1181821 : CollatzResearch.WordTrace tailWord_1181821 prefixEnd_1181821 404561480384883902401607 := by
  unfold tailWord_1181821
  simp only [CollatzResearch.WordTrace]
  refine ⟨43104553051471830802689317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28736368700981220535126211 43104553051471830802689317)
  ·
    refine ⟨8082103697150968275504247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43104553051471830802689317 8082103697150968275504247)
    ·
      refine ⟨12123155545726452413256371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8082103697150968275504247 12123155545726452413256371)
      ·
        refine ⟨18184733318589678619884557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12123155545726452413256371 18184733318589678619884557)
        ·
          refine ⟨6819274994471129482456709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18184733318589678619884557 6819274994471129482456709)
          ·
            refine ⟨1278614061463336777960633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6819274994471129482456709 1278614061463336777960633)
            ·
              refine ⟨958960546097502583470475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278614061463336777960633 958960546097502583470475)
              ·
                refine ⟨1438440819146253875205713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958960546097502583470475 1438440819146253875205713)
                ·
                  refine ⟨1078830614359690406404285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1438440819146253875205713 1078830614359690406404285)
                  ·
                    refine ⟨404561480384883902401607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078830614359690406404285 404561480384883902401607)
                    ·
                      rfl

theorem cell22_1181821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_1181821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181821 prefixEnd_1181821 := by exact prefixLift 1181821
  have htrace : WordTrace (prefixWord ++ tailWord_1181821) baseStart_1181821 baseEnd_1181821 := by
    simpa [prefixWord, tailWord_1181821, baseEnd_1181821] using wordTrace_append hprefix tailTrace_1181821
  have hstable : (prefixWord ++ tailWord_1181821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181821).length < 2 ^ (prefixWord ++ tailWord_1181821).sum := by decide
  have hdescent : baseEnd_1181821 < baseStart_1181821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181952 : List Nat := [2, 1, 1, 2, 1, 1, 8, 6]
def baseStart_1181952 : Nat := 118140960795 + 1181952 * 2 ^ 59
def prefixEnd_1181952 : Nat := 4983230072969 + 3 ^ 40 * 1181952 * 2
def baseEnd_1181952 : Nat := 44956258262449247486245

theorem tailTrace_1181952 : CollatzResearch.WordTrace tailWord_1181952 prefixEnd_1181952 44956258262449247486245 := by
  unfold tailWord_1181952
  simp only [CollatzResearch.WordTrace]
  refine ⟨21554665506998620087854055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28739554009331493450472073 21554665506998620087854055)
  ·
    refine ⟨32331998260497930131781083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21554665506998620087854055 32331998260497930131781083)
    ·
      refine ⟨48497997390746895197671625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32331998260497930131781083 48497997390746895197671625)
      ·
        refine ⟨36373498043060171398253719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48497997390746895197671625 36373498043060171398253719)
        ·
          refine ⟨54560247064590257097380579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36373498043060171398253719 54560247064590257097380579)
          ·
            refine ⟨81840370596885385646070869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54560247064590257097380579 81840370596885385646070869)
            ·
              refine ⟨959066842932250613039893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 81840370596885385646070869 959066842932250613039893)
              ·
                refine ⟨44956258262449247486245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 959066842932250613039893 44956258262449247486245)
                ·
                  rfl

theorem cell22_1181952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_1181952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181952 prefixEnd_1181952 := by exact prefixLift 1181952
  have htrace : WordTrace (prefixWord ++ tailWord_1181952) baseStart_1181952 baseEnd_1181952 := by
    simpa [prefixWord, tailWord_1181952, baseEnd_1181952] using wordTrace_append hprefix tailTrace_1181952
  have hstable : (prefixWord ++ tailWord_1181952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181952).length < 2 ^ (prefixWord ++ tailWord_1181952).sum := by decide
  have hdescent : baseEnd_1181952 < baseStart_1181952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181954 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1181954 : Nat := 118140960795 + 1181954 * 2 ^ 59
def prefixEnd_1181954 : Nat := 4983230072969 + 3 ^ 40 * 1181954 * 2
def baseEnd_1181954 : Nat := 404607009002915888826199

theorem tailTrace_1181954 : CollatzResearch.WordTrace tailWord_1181954 prefixEnd_1181954 404607009002915888826199 := by
  unfold tailWord_1181954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777350989997498629320229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28739602639993329678187277 10777350989997498629320229)
  ·
    refine ⟨2020753310624530992997543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10777350989997498629320229 2020753310624530992997543)
    ·
      refine ⟨3031129965936796489496315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020753310624530992997543 3031129965936796489496315)
      ·
        refine ⟨4546694948905194734244473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031129965936796489496315 4546694948905194734244473)
        ·
          refine ⟨3410021211678896050683355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4546694948905194734244473 3410021211678896050683355)
          ·
            refine ⟨5115031817518344076025033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410021211678896050683355 5115031817518344076025033)
            ·
              refine ⟨3836273863138758057018775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5115031817518344076025033 3836273863138758057018775)
              ·
                refine ⟨5754410794708137085528163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3836273863138758057018775 5754410794708137085528163)
                ·
                  refine ⟨8631616192062205628292245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5754410794708137085528163 8631616192062205628292245)
                  ·
                    refine ⟨404607009002915888826199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8631616192062205628292245 404607009002915888826199)
                    ·
                      rfl

theorem cell22_1181954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1181954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181954 prefixEnd_1181954 := by exact prefixLift 1181954
  have htrace : WordTrace (prefixWord ++ tailWord_1181954) baseStart_1181954 baseEnd_1181954 := by
    simpa [prefixWord, tailWord_1181954, baseEnd_1181954] using wordTrace_append hprefix tailTrace_1181954
  have hstable : (prefixWord ++ tailWord_1181954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181954).length < 2 ^ (prefixWord ++ tailWord_1181954).sum := by decide
  have hdescent : baseEnd_1181954 < baseStart_1181954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181967 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 5, 3]
def baseStart_1181967 : Nat := 118140960795 + 1181967 * 2 ^ 59
def prefixEnd_1181967 : Nat := 4983230072969 + 3 ^ 40 * 1181967 * 2
def baseEnd_1181967 : Nat := 404611459168588188251159

theorem tailTrace_1181967 : CollatzResearch.WordTrace tailWord_1181967 prefixEnd_1181967 404611459168588188251159 := by
  unfold tailWord_1181967
  simp only [CollatzResearch.WordTrace]
  refine ⟨43109878108942897737504155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28739918739295265158336103 43109878108942897737504155)
  ·
    refine ⟨64664817163414346606256233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43109878108942897737504155 64664817163414346606256233)
    ·
      refine ⟨48498612872560759954692175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64664817163414346606256233 48498612872560759954692175)
      ·
        refine ⟨72747919308841139932038263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48498612872560759954692175 72747919308841139932038263)
        ·
          refine ⟨109121878963261709898057395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72747919308841139932038263 109121878963261709898057395)
          ·
            refine ⟨163682818444892564847086093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109121878963261709898057395 163682818444892564847086093)
            ·
              refine ⟨61381056916834711817657285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163682818444892564847086093 61381056916834711817657285)
              ·
                refine ⟨11508948171906508465810741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61381056916834711817657285 11508948171906508465810741)
                ·
                  refine ⟨1078963891116235168669757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11508948171906508465810741 1078963891116235168669757)
                  ·
                    refine ⟨404611459168588188251159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1078963891116235168669757 404611459168588188251159)
                    ·
                      rfl

theorem cell22_1181967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_1181967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1181967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1181967 prefixEnd_1181967 := by exact prefixLift 1181967
  have htrace : WordTrace (prefixWord ++ tailWord_1181967) baseStart_1181967 baseEnd_1181967 := by
    simpa [prefixWord, tailWord_1181967, baseEnd_1181967] using wordTrace_append hprefix tailTrace_1181967
  have hstable : (prefixWord ++ tailWord_1181967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181967).length < 2 ^ (prefixWord ++ tailWord_1181967).sum := by decide
  have hdescent : baseEnd_1181967 < baseStart_1181967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182042 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_1182042 : Nat := 118140960795 + 1182042 * 2 ^ 59
def prefixEnd_1182042 : Nat := 4983230072969 + 3 ^ 40 * 1182042 * 2
def baseEnd_1182042 : Nat := 134879044400437664208643

theorem tailTrace_1182042 : CollatzResearch.WordTrace tailWord_1182042 prefixEnd_1182042 134879044400437664208643 := by
  unfold tailWord_1182042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778153395917796386621095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28741742389114123697656253 10778153395917796386621095)
  ·
    refine ⟨16167230093876694579931643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10778153395917796386621095 16167230093876694579931643)
    ·
      refine ⟨24250845140815041869897465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16167230093876694579931643 24250845140815041869897465)
      ·
        refine ⟨18188133855611281402423099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24250845140815041869897465 18188133855611281402423099)
        ·
          refine ⟨27282200783416922103634649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18188133855611281402423099 27282200783416922103634649)
          ·
            refine ⟨20461650587562691577725987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27282200783416922103634649 20461650587562691577725987)
            ·
              refine ⟨30692475881344037366588981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20461650587562691577725987 30692475881344037366588981)
              ·
                refine ⟨2877419613876003503117717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30692475881344037366588981 2877419613876003503117717)
                ·
                  refine ⟨134879044400437664208643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2877419613876003503117717 134879044400437664208643)
                  ·
                    rfl

theorem cell22_1182042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_1182042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182042 prefixEnd_1182042 := by exact prefixLift 1182042
  have htrace : WordTrace (prefixWord ++ tailWord_1182042) baseStart_1182042 baseEnd_1182042 := by
    simpa [prefixWord, tailWord_1182042, baseEnd_1182042] using wordTrace_append hprefix tailTrace_1182042
  have hstable : (prefixWord ++ tailWord_1182042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182042).length < 2 ^ (prefixWord ++ tailWord_1182042).sum := by decide
  have hdescent : baseEnd_1182042 < baseStart_1182042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182087 : List Nat := [1, 1, 4, 2, 2, 1, 11]
def baseStart_1182087 : Nat := 118140960795 + 1182087 * 2 ^ 59
def prefixEnd_1182087 : Nat := 4983230072969 + 3 ^ 40 * 1182087 * 2
def baseEnd_1182087 : Nat := 14987131022998069453733

theorem tailTrace_1182087 : CollatzResearch.WordTrace tailWord_1182087 prefixEnd_1182087 14987131022998069453733 := by
  unfold tailWord_1182087
  simp only [CollatzResearch.WordTrace]
  refine ⟨43114254868508158231872515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28742836579005438821248343 43114254868508158231872515)
  ·
    refine ⟨64671382302762237347808773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43114254868508158231872515 64671382302762237347808773)
    ·
      refine ⟨12125884181767919502714145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64671382302762237347808773 12125884181767919502714145)
      ·
        refine ⟨9094413136325939627035609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12125884181767919502714145 9094413136325939627035609)
        ·
          refine ⟨6820809852244454720276707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9094413136325939627035609 6820809852244454720276707)
          ·
            refine ⟨10231214778366682080415061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6820809852244454720276707 10231214778366682080415061)
            ·
              refine ⟨14987131022998069453733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10231214778366682080415061 14987131022998069453733)
              ·
                rfl

theorem cell22_1182087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 11].length) (baseStart_1182087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182087 prefixEnd_1182087 := by exact prefixLift 1182087
  have htrace : WordTrace (prefixWord ++ tailWord_1182087) baseStart_1182087 baseEnd_1182087 := by
    simpa [prefixWord, tailWord_1182087, baseEnd_1182087] using wordTrace_append hprefix tailTrace_1182087
  have hstable : (prefixWord ++ tailWord_1182087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182087).length < 2 ^ (prefixWord ++ tailWord_1182087).sum := by decide
  have hdescent : baseEnd_1182087 < baseStart_1182087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182091 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 2, 3]
def baseStart_1182091 : Nat := 118140960795 + 1182091 * 2 ^ 59
def prefixEnd_1182091 : Nat := 4983230072969 + 3 ^ 40 * 1182091 * 2
def baseEnd_1182091 : Nat := 404653906902693198150779

theorem tailTrace_1182091 : CollatzResearch.WordTrace tailWord_1182091 prefixEnd_1182091 404653906902693198150779 := by
  unfold tailWord_1182091
  simp only [CollatzResearch.WordTrace]
  refine ⟨43114400760493666915018127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28742933840329111276678751 43114400760493666915018127)
  ·
    refine ⟨64671601140740500372527191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43114400760493666915018127 64671601140740500372527191)
    ·
      refine ⟨97007401711110750558790787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64671601140740500372527191 97007401711110750558790787)
      ·
        refine ⟨145511102566666125838186181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97007401711110750558790787 145511102566666125838186181)
        ·
          refine ⟨27283331731249898594659909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145511102566666125838186181 27283331731249898594659909)
          ·
            refine ⟨5115624699609355986498733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27283331731249898594659909 5115624699609355986498733)
            ·
              refine ⟨1918359262353508494937025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5115624699609355986498733 1918359262353508494937025)
              ·
                refine ⟨1438769446765131371202769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918359262353508494937025 1438769446765131371202769)
                ·
                  refine ⟨1079077085073848528402077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1438769446765131371202769 1079077085073848528402077)
                  ·
                    refine ⟨404653906902693198150779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079077085073848528402077 404653906902693198150779)
                    ·
                      rfl

theorem cell22_1182091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3].length) (baseStart_1182091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182091 prefixEnd_1182091 := by exact prefixLift 1182091
  have htrace : WordTrace (prefixWord ++ tailWord_1182091) baseStart_1182091 baseEnd_1182091 := by
    simpa [prefixWord, tailWord_1182091, baseEnd_1182091] using wordTrace_append hprefix tailTrace_1182091
  have hstable : (prefixWord ++ tailWord_1182091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182091).length < 2 ^ (prefixWord ++ tailWord_1182091).sum := by decide
  have hdescent : baseEnd_1182091 < baseStart_1182091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182211 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 4]
def baseStart_1182211 : Nat := 118140960795 + 1182211 * 2 ^ 59
def prefixEnd_1182211 : Nat := 4983230072969 + 3 ^ 40 * 1182211 * 2
def baseEnd_1182211 : Nat := 134898328451684295050137

theorem tailTrace_1182211 : CollatzResearch.WordTrace tailWord_1182211 prefixEnd_1182211 134898328451684295050137 := by
  unfold tailWord_1182211
  simp only [CollatzResearch.WordTrace]
  refine ⟨43118777520058927409386487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28745851680039284939590991 43118777520058927409386487)
  ·
    refine ⟨64678166280088391114079731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43118777520058927409386487 64678166280088391114079731)
    ·
      refine ⟨97017249420132586671119597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64678166280088391114079731 97017249420132586671119597)
      ·
        refine ⟨36381468532549720001669849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97017249420132586671119597 36381468532549720001669849)
        ·
          refine ⟨27286101399412290001252387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36381468532549720001669849 27286101399412290001252387)
          ·
            refine ⟨40929152099118435001878581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27286101399412290001252387 40929152099118435001878581)
            ·
              refine ⟨3837108009292353281426117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40929152099118435001878581 3837108009292353281426117)
              ·
                refine ⟨719457751742316240267397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3837108009292353281426117 719457751742316240267397)
                ·
                  refine ⟨134898328451684295050137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719457751742316240267397 134898328451684295050137)
                  ·
                    rfl

theorem cell22_1182211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 4].length) (baseStart_1182211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182211 prefixEnd_1182211 := by exact prefixLift 1182211
  have htrace : WordTrace (prefixWord ++ tailWord_1182211) baseStart_1182211 baseEnd_1182211 := by
    simpa [prefixWord, tailWord_1182211, baseEnd_1182211] using wordTrace_append hprefix tailTrace_1182211
  have hstable : (prefixWord ++ tailWord_1182211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182211).length < 2 ^ (prefixWord ++ tailWord_1182211).sum := by decide
  have hdescent : baseEnd_1182211 < baseStart_1182211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182228 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1182228 : Nat := 118140960795 + 1182228 * 2 ^ 59
def prefixEnd_1182228 : Nat := 4983230072969 + 3 ^ 40 * 1182228 * 2
def baseEnd_1182228 : Nat := 134900268267490169158453

theorem tailTrace_1182228 : CollatzResearch.WordTrace tailWord_1182228 prefixEnd_1182228 134900268267490169158453 := by
  unfold tailWord_1182228
  simp only [CollatzResearch.WordTrace]
  refine ⟨21559698780498669656377669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28746265040664892875170225 21559698780498669656377669)
  ·
    refine ⟨4042443521343500560570813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21559698780498669656377669 4042443521343500560570813)
    ·
      refine ⟨1515916320503812710214055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4042443521343500560570813 1515916320503812710214055)
      ·
        refine ⟨2273874480755719065321083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515916320503812710214055 2273874480755719065321083)
        ·
          refine ⟨3410811721133578597981625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273874480755719065321083 3410811721133578597981625)
          ·
            refine ⟨2558108790850183948486219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3410811721133578597981625 2558108790850183948486219)
            ·
              refine ⟨3837163186275275922729329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558108790850183948486219 3837163186275275922729329)
              ·
                refine ⟨2877872389706456942046997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837163186275275922729329 2877872389706456942046997)
                ·
                  refine ⟨134900268267490169158453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2877872389706456942046997 134900268267490169158453)
                  ·
                    rfl

theorem cell22_1182228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1182228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182228 prefixEnd_1182228 := by exact prefixLift 1182228
  have htrace : WordTrace (prefixWord ++ tailWord_1182228) baseStart_1182228 baseEnd_1182228 := by
    simpa [prefixWord, tailWord_1182228, baseEnd_1182228] using wordTrace_append hprefix tailTrace_1182228
  have hstable : (prefixWord ++ tailWord_1182228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182228).length < 2 ^ (prefixWord ++ tailWord_1182228).sum := by decide
  have hdescent : baseEnd_1182228 < baseStart_1182228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182305 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 1, 3]
def baseStart_1182305 : Nat := 118140960795 + 1182305 * 2 ^ 59
def prefixEnd_1182305 : Nat := 4983230072969 + 3 ^ 40 * 1182305 * 2
def baseEnd_1182305 : Nat := 404727163476067973300123

theorem tailTrace_1182305 : CollatzResearch.WordTrace tailWord_1182305 prefixEnd_1182305 404727163476067973300123 := by
  unfold tailWord_1182305
  simp only [CollatzResearch.WordTrace]
  refine ⟨43122205981718381463308369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28748137321145587642205579 43122205981718381463308369)
  ·
    refine ⟨32341654486288786097481277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43122205981718381463308369 32341654486288786097481277)
    ·
      refine ⟨12128120432358294786555479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32341654486288786097481277 12128120432358294786555479)
      ·
        refine ⟨18192180648537442179833219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12128120432358294786555479 18192180648537442179833219)
        ·
          refine ⟨27288270972806163269749829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18192180648537442179833219 27288270972806163269749829)
          ·
            refine ⟨5116550807401155613078093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27288270972806163269749829 5116550807401155613078093)
            ·
              refine ⟨1918706552775433354904285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5116550807401155613078093 1918706552775433354904285)
              ·
                refine ⟨719514957290787508089107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1918706552775433354904285 719514957290787508089107)
                ·
                  refine ⟨1079272435936181262133661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719514957290787508089107 1079272435936181262133661)
                  ·
                    refine ⟨404727163476067973300123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079272435936181262133661 404727163476067973300123)
                    ·
                      rfl

theorem cell22_1182305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_1182305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182305 prefixEnd_1182305 := by exact prefixLift 1182305
  have htrace : WordTrace (prefixWord ++ tailWord_1182305) baseStart_1182305 baseEnd_1182305 := by
    simpa [prefixWord, tailWord_1182305, baseEnd_1182305] using wordTrace_append hprefix tailTrace_1182305
  have hstable : (prefixWord ++ tailWord_1182305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182305).length < 2 ^ (prefixWord ++ tailWord_1182305).sum := by decide
  have hdescent : baseEnd_1182305 < baseStart_1182305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182322 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_1182322 : Nat := 118140960795 + 1182322 * 2 ^ 59
def prefixEnd_1182322 : Nat := 4983230072969 + 3 ^ 40 * 1182322 * 2
def baseEnd_1182322 : Nat := 404732982923485595625071

theorem tailTrace_1182322 : CollatzResearch.WordTrace tailWord_1182322 prefixEnd_1182322 404732982923485595625071 := by
  unfold tailWord_1182322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10780706505664198341669305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28748550681771195577784813 10780706505664198341669305)
  ·
    refine ⟨8085529879248148756251979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10780706505664198341669305 8085529879248148756251979)
    ·
      refine ⟨12128294818872223134377969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8085529879248148756251979 12128294818872223134377969)
      ·
        refine ⟨9096221114154167350783477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12128294818872223134377969 9096221114154167350783477)
        ·
          refine ⟨852770729451953189135951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9096221114154167350783477 852770729451953189135951)
          ·
            refine ⟨1279156094177929783703927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852770729451953189135951 1279156094177929783703927)
            ·
              refine ⟨1918734141266894675555891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279156094177929783703927 1918734141266894675555891)
              ·
                refine ⟨2878101211900342013333837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918734141266894675555891 2878101211900342013333837)
                ·
                  refine ⟨1079287954462628255000189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2878101211900342013333837 1079287954462628255000189)
                  ·
                    refine ⟨404732982923485595625071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079287954462628255000189 404732982923485595625071)
                    ·
                      rfl

theorem cell22_1182322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_1182322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182322 prefixEnd_1182322 := by exact prefixLift 1182322
  have htrace : WordTrace (prefixWord ++ tailWord_1182322) baseStart_1182322 baseEnd_1182322 := by
    simpa [prefixWord, tailWord_1182322, baseEnd_1182322] using wordTrace_append hprefix tailTrace_1182322
  have hstable : (prefixWord ++ tailWord_1182322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182322).length < 2 ^ (prefixWord ++ tailWord_1182322).sum := by decide
  have hdescent : baseEnd_1182322 < baseStart_1182322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182361 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_1182361 : Nat := 118140960795 + 1182361 * 2 ^ 59
def prefixEnd_1182361 : Nat := 4983230072969 + 3 ^ 40 * 1182361 * 2
def baseEnd_1182361 : Nat := 404746333420502493899951

theorem tailTrace_1182361 : CollatzResearch.WordTrace tailWord_1182361 prefixEnd_1182361 404746333420502493899951 := by
  unfold tailWord_1182361
  simp only [CollatzResearch.WordTrace]
  refine ⟨43124248469515503027346937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28749498979677002018231291 43124248469515503027346937)
  ·
    refine ⟨32343186352136627270510203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43124248469515503027346937 32343186352136627270510203)
    ·
      refine ⟨48514779528204940905765305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32343186352136627270510203 48514779528204940905765305)
      ·
        refine ⟨36386084646153705679323979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48514779528204940905765305 36386084646153705679323979)
        ·
          refine ⟨54579126969230558518985969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36386084646153705679323979 54579126969230558518985969)
          ·
            refine ⟨40934345226922918889239477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54579126969230558518985969 40934345226922918889239477)
            ·
              refine ⟨3837594865024023645866201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40934345226922918889239477 3837594865024023645866201)
              ·
                refine ⟨2878196148768017734399651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837594865024023645866201 2878196148768017734399651)
                ·
                  refine ⟨4317294223152026601599477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878196148768017734399651 4317294223152026601599477)
                  ·
                    refine ⟨404746333420502493899951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4317294223152026601599477 404746333420502493899951)
                    ·
                      rfl

theorem cell22_1182361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_1182361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182361 prefixEnd_1182361 := by exact prefixLift 1182361
  have htrace : WordTrace (prefixWord ++ tailWord_1182361) baseStart_1182361 baseEnd_1182361 := by
    simpa [prefixWord, tailWord_1182361, baseEnd_1182361] using wordTrace_append hprefix tailTrace_1182361
  have hstable : (prefixWord ++ tailWord_1182361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182361).length < 2 ^ (prefixWord ++ tailWord_1182361).sum := by decide
  have hdescent : baseEnd_1182361 < baseStart_1182361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182408 : List Nat := [2, 1, 3, 1, 2, 4, 3, 6]
def baseStart_1182408 : Nat := 118140960795 + 1182408 * 2 ^ 59
def prefixEnd_1182408 : Nat := 4983230072969 + 3 ^ 40 * 1182408 * 2
def baseEnd_1182408 : Nat := 44973602497890004219423

theorem tailTrace_1182408 : CollatzResearch.WordTrace tailWord_1182408 prefixEnd_1182408 44973602497890004219423 := by
  unfold tailWord_1182408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562981350172615027153939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28750641800230153369538585 21562981350172615027153939)
  ·
    refine ⟨32344472025258922540730909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562981350172615027153939 32344472025258922540730909)
    ·
      refine ⟨12129177009472095952774091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32344472025258922540730909 12129177009472095952774091)
      ·
        refine ⟨18193765514208143929161137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12129177009472095952774091 18193765514208143929161137)
        ·
          refine ⟨13645324135656107946870853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18193765514208143929161137 13645324135656107946870853)
          ·
            refine ⟨2558498275435520240038285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13645324135656107946870853 2558498275435520240038285)
            ·
              refine ⟨959436853288320090014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2558498275435520240038285 959436853288320090014357)
              ·
                refine ⟨44973602497890004219423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 959436853288320090014357 44973602497890004219423)
                ·
                  rfl

theorem cell22_1182408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_1182408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182408 prefixEnd_1182408 := by exact prefixLift 1182408
  have htrace : WordTrace (prefixWord ++ tailWord_1182408) baseStart_1182408 baseEnd_1182408 := by
    simpa [prefixWord, tailWord_1182408, baseEnd_1182408] using wordTrace_append hprefix tailTrace_1182408
  have hstable : (prefixWord ++ tailWord_1182408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182408).length < 2 ^ (prefixWord ++ tailWord_1182408).sum := by decide
  have hdescent : baseEnd_1182408 < baseStart_1182408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182410 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_1182410 : Nat := 118140960795 + 1182410 * 2 ^ 59
def prefixEnd_1182410 : Nat := 4983230072969 + 3 ^ 40 * 1182410 * 2
def baseEnd_1182410 : Nat := 404763107121882699424801

theorem tailTrace_1182410 : CollatzResearch.WordTrace tailWord_1182410 prefixEnd_1182410 404763107121882699424801 := by
  unfold tailWord_1182410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10781508911584496098970171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28750690430891989597253789 10781508911584496098970171)
  ·
    refine ⟨16172263367376744148455257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10781508911584496098970171 16172263367376744148455257)
    ·
      refine ⟨12129197525532558111341443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16172263367376744148455257 12129197525532558111341443)
      ·
        refine ⟨18193796288298837167012165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12129197525532558111341443 18193796288298837167012165)
        ·
          refine ⟨3411336804056031968814781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18193796288298837167012165 3411336804056031968814781)
          ·
            refine ⟨1279251301521011988305543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3411336804056031968814781 1279251301521011988305543)
            ·
              refine ⟨1918876952281517982458315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279251301521011988305543 1918876952281517982458315)
              ·
                refine ⟨2878315428422276973687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918876952281517982458315 2878315428422276973687473)
                ·
                  refine ⟨2158736571316707730265605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878315428422276973687473 2158736571316707730265605)
                  ·
                    refine ⟨404763107121882699424801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158736571316707730265605 404763107121882699424801)
                    ·
                      rfl

theorem cell22_1182410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_1182410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182410 prefixEnd_1182410 := by exact prefixLift 1182410
  have htrace : WordTrace (prefixWord ++ tailWord_1182410) baseStart_1182410 baseEnd_1182410 := by
    simpa [prefixWord, tailWord_1182410, baseEnd_1182410] using wordTrace_append hprefix tailTrace_1182410
  have hstable : (prefixWord ++ tailWord_1182410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182410).length < 2 ^ (prefixWord ++ tailWord_1182410).sum := by decide
  have hdescent : baseEnd_1182410 < baseStart_1182410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182481 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 8]
def baseStart_1182481 : Nat := 118140960795 + 1182481 * 2 ^ 59
def prefixEnd_1182481 : Nat := 4983230072969 + 3 ^ 40 * 1182481 * 2
def baseEnd_1182481 : Nat := 134929137290954060299861

theorem tailTrace_1182481 : CollatzResearch.WordTrace tailWord_1182481 prefixEnd_1182481 134929137290954060299861 := by
  unfold tailWord_1182481
  simp only [CollatzResearch.WordTrace]
  refine ⟨43128625229080763521715297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28752416819387175681143531 43128625229080763521715297)
  ·
    refine ⟨32346468921810572641286473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43128625229080763521715297 32346468921810572641286473)
    ·
      refine ⟨24259851691357929480964855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32346468921810572641286473 24259851691357929480964855)
      ·
        refine ⟨36389777537036894221447283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24259851691357929480964855 36389777537036894221447283)
        ·
          refine ⟨54584666305555341332170925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36389777537036894221447283 54584666305555341332170925)
          ·
            refine ⟨20469249864583252999564097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54584666305555341332170925 20469249864583252999564097)
            ·
              refine ⟨15351937398437439749673073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20469249864583252999564097 15351937398437439749673073)
              ·
                refine ⟨11513953048828079812254805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15351937398437439749673073 11513953048828079812254805)
                ·
                  refine ⟨134929137290954060299861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11513953048828079812254805 134929137290954060299861)
                  ·
                    rfl

theorem cell22_1182481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_1182481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182481 prefixEnd_1182481 := by exact prefixLift 1182481
  have htrace : WordTrace (prefixWord ++ tailWord_1182481) baseStart_1182481 baseEnd_1182481 := by
    simpa [prefixWord, tailWord_1182481, baseEnd_1182481] using wordTrace_append hprefix tailTrace_1182481
  have hstable : (prefixWord ++ tailWord_1182481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182481).length < 2 ^ (prefixWord ++ tailWord_1182481).sum := by decide
  have hdescent : baseEnd_1182481 < baseStart_1182481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182483 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 1, 4]
def baseStart_1182483 : Nat := 118140960795 + 1182483 * 2 ^ 59
def prefixEnd_1182483 : Nat := 4983230072969 + 3 ^ 40 * 1182483 * 2
def baseEnd_1182483 : Nat := 404788096513734842349577

theorem tailTrace_1182483 : CollatzResearch.WordTrace tailWord_1182483 prefixEnd_1182483 404788096513734842349577 := by
  unfold tailWord_1182483
  simp only [CollatzResearch.WordTrace]
  refine ⟨43128698175073517863288103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28752465450049011908858735 43128698175073517863288103)
  ·
    refine ⟨64693047262610276794932155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43128698175073517863288103 64693047262610276794932155)
    ·
      refine ⟨97039570893915415192398233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64693047262610276794932155 97039570893915415192398233)
      ·
        refine ⟨72779678170436561394298675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97039570893915415192398233 72779678170436561394298675)
        ·
          refine ⟨109169517255654842091448013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72779678170436561394298675 109169517255654842091448013)
          ·
            refine ⟨40938568970870565784293005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109169517255654842091448013 40938568970870565784293005)
            ·
              refine ⟨15351963364076462169109877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40938568970870565784293005 15351963364076462169109877)
              ·
                refine ⟨1439246565382168328354051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15351963364076462169109877 1439246565382168328354051)
                ·
                  refine ⟨2158869848073252492531077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439246565382168328354051 2158869848073252492531077)
                  ·
                    refine ⟨404788096513734842349577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158869848073252492531077 404788096513734842349577)
                    ·
                      rfl

theorem cell22_1182483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 4].length) (baseStart_1182483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182483 prefixEnd_1182483 := by exact prefixLift 1182483
  have htrace : WordTrace (prefixWord ++ tailWord_1182483) baseStart_1182483 baseEnd_1182483 := by
    simpa [prefixWord, tailWord_1182483, baseEnd_1182483] using wordTrace_append hprefix tailTrace_1182483
  have hstable : (prefixWord ++ tailWord_1182483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182483).length < 2 ^ (prefixWord ++ tailWord_1182483).sum := by decide
  have hdescent : baseEnd_1182483 < baseStart_1182483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182513 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1182513 : Nat := 118140960795 + 1182513 * 2 ^ 59
def prefixEnd_1182513 : Nat := 4983230072969 + 3 ^ 40 * 1182513 * 2
def baseEnd_1182513 : Nat := 404798366126824764099485

theorem tailTrace_1182513 : CollatzResearch.WordTrace tailWord_1182513 prefixEnd_1182513 404798366126824764099485 := by
  unfold tailWord_1182513
  simp only [CollatzResearch.WordTrace]
  refine ⟨43129792364964832986880193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28753194909976555324586795 43129792364964832986880193)
  ·
    refine ⟨32347344273723624740160145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43129792364964832986880193 32347344273723624740160145)
    ·
      refine ⟨24260508205292718555120109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32347344273723624740160145 24260508205292718555120109)
      ·
        refine ⟨9097690576984769458170041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24260508205292718555120109 9097690576984769458170041)
        ·
          refine ⟨6823267932738577093627531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9097690576984769458170041 6823267932738577093627531)
          ·
            refine ⟨10234901899107865640441297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823267932738577093627531 10234901899107865640441297)
            ·
              refine ⟨7676176424330899230330973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10234901899107865640441297 7676176424330899230330973)
              ·
                refine ⟨2878566159124087211374115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7676176424330899230330973 2878566159124087211374115)
                ·
                  refine ⟨4317849238686130817061173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878566159124087211374115 4317849238686130817061173)
                  ·
                    refine ⟨404798366126824764099485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4317849238686130817061173 404798366126824764099485)
                    ·
                      rfl

theorem cell22_1182513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1182513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182513 prefixEnd_1182513 := by exact prefixLift 1182513
  have htrace : WordTrace (prefixWord ++ tailWord_1182513) baseStart_1182513 baseEnd_1182513 := by
    simpa [prefixWord, tailWord_1182513, baseEnd_1182513] using wordTrace_append hprefix tailTrace_1182513
  have hstable : (prefixWord ++ tailWord_1182513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182513).length < 2 ^ (prefixWord ++ tailWord_1182513).sum := by decide
  have hdescent : baseEnd_1182513 < baseStart_1182513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182517 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1182517 : Nat := 118140960795 + 1182517 * 2 ^ 59
def prefixEnd_1182517 : Nat := 4983230072969 + 3 ^ 40 * 1182517 * 2
def baseEnd_1182517 : Nat := 404799735408570086999473

theorem tailTrace_1182517 : CollatzResearch.WordTrace tailWord_1182517 prefixEnd_1182517 404799735408570086999473 := by
  unfold tailWord_1182517
  simp only [CollatzResearch.WordTrace]
  refine ⟨43129938256950341670025805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28753292171300227780017203 43129938256950341670025805)
  ·
    refine ⟨16173726846356378126259677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43129938256950341670025805 16173726846356378126259677)
    ·
      refine ⟨6065147567383641797347379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16173726846356378126259677 6065147567383641797347379)
      ·
        refine ⟨9097721351075462696021069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065147567383641797347379 9097721351075462696021069)
        ·
          refine ⟨3411645506653298511007901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9097721351075462696021069 3411645506653298511007901)
          ·
            refine ⟨1279367064994986941627963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3411645506653298511007901 1279367064994986941627963)
            ·
              refine ⟨1919050597492480412441945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279367064994986941627963 1919050597492480412441945)
              ·
                refine ⟨1439287948119360309331459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919050597492480412441945 1439287948119360309331459)
                ·
                  refine ⟨2158931922179040463997189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439287948119360309331459 2158931922179040463997189)
                  ·
                    refine ⟨404799735408570086999473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158931922179040463997189 404799735408570086999473)
                    ·
                      rfl

theorem cell22_1182517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1182517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182517 prefixEnd_1182517 := by exact prefixLift 1182517
  have htrace : WordTrace (prefixWord ++ tailWord_1182517) baseStart_1182517 baseEnd_1182517 := by
    simpa [prefixWord, tailWord_1182517, baseEnd_1182517] using wordTrace_append hprefix tailTrace_1182517
  have hstable : (prefixWord ++ tailWord_1182517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182517).length < 2 ^ (prefixWord ++ tailWord_1182517).sum := by decide
  have hdescent : baseEnd_1182517 < baseStart_1182517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182573 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1182573 : Nat := 118140960795 + 1182573 * 2 ^ 59
def prefixEnd_1182573 : Nat := 4983230072969 + 3 ^ 40 * 1182573 * 2
def baseEnd_1182573 : Nat := 404818905353004607599301

theorem tailTrace_1182573 : CollatzResearch.WordTrace tailWord_1182573 prefixEnd_1182573 404818905353004607599301 := by
  unfold tailWord_1182573
  simp only [CollatzResearch.WordTrace]
  refine ⟨43131980744747463234064373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28754653829831642156042915 43131980744747463234064373)
  ·
    refine ⟨4043623194820074678193535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43131980744747463234064373 4043623194820074678193535)
    ·
      refine ⟨6065434792230112017290303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043623194820074678193535 6065434792230112017290303)
      ·
        refine ⟨9098152188345168025935455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065434792230112017290303 9098152188345168025935455)
        ·
          refine ⟨13647228282517752038903183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9098152188345168025935455 13647228282517752038903183)
          ·
            refine ⟨20470842423776628058354775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13647228282517752038903183 20470842423776628058354775)
            ·
              refine ⟨30706263635664942087532163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20470842423776628058354775 30706263635664942087532163)
              ·
                refine ⟨46059395453497413131298245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30706263635664942087532163 46059395453497413131298245)
                ·
                  refine ⟨8636136647530764962118421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46059395453497413131298245 8636136647530764962118421)
                  ·
                    refine ⟨404818905353004607599301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8636136647530764962118421 404818905353004607599301)
                    ·
                      rfl

theorem cell22_1182573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1182573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182573 prefixEnd_1182573 := by exact prefixLift 1182573
  have htrace : WordTrace (prefixWord ++ tailWord_1182573) baseStart_1182573 baseEnd_1182573 := by
    simpa [prefixWord, tailWord_1182573, baseEnd_1182573] using wordTrace_append hprefix tailTrace_1182573
  have hstable : (prefixWord ++ tailWord_1182573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182573).length < 2 ^ (prefixWord ++ tailWord_1182573).sum := by decide
  have hdescent : baseEnd_1182573 < baseStart_1182573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182603 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_1182603 : Nat := 118140960795 + 1182603 * 2 ^ 59
def prefixEnd_1182603 : Nat := 4983230072969 + 3 ^ 40 * 1182603 * 2
def baseEnd_1182603 : Nat := 404829174966094529349209

theorem tailTrace_1182603 : CollatzResearch.WordTrace tailWord_1182603 prefixEnd_1182603 404829174966094529349209 := by
  unfold tailWord_1182603
  simp only [CollatzResearch.WordTrace]
  refine ⟨43133074934638778357656463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28755383289759185571770975 43133074934638778357656463)
  ·
    refine ⟨64699612401958167536484695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43133074934638778357656463 64699612401958167536484695)
    ·
      refine ⟨97049418602937251304727043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64699612401958167536484695 97049418602937251304727043)
      ·
        refine ⟨145574127904405876957090565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97049418602937251304727043 145574127904405876957090565)
        ·
          refine ⟨27295148982076101929454481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145574127904405876957090565 27295148982076101929454481)
          ·
            refine ⟨20471361736557076447090861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27295148982076101929454481 20471361736557076447090861)
            ·
              refine ⟨7676760651208903667659073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20471361736557076447090861 7676760651208903667659073)
              ·
                refine ⟨5757570488406677750744305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7676760651208903667659073 5757570488406677750744305)
                ·
                  refine ⟨4318177866305008313058229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5757570488406677750744305 4318177866305008313058229)
                  ·
                    refine ⟨404829174966094529349209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4318177866305008313058229 404829174966094529349209)
                    ·
                      rfl

theorem cell22_1182603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_1182603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182603 prefixEnd_1182603 := by exact prefixLift 1182603
  have htrace : WordTrace (prefixWord ++ tailWord_1182603) baseStart_1182603 baseEnd_1182603 := by
    simpa [prefixWord, tailWord_1182603, baseEnd_1182603] using wordTrace_append hprefix tailTrace_1182603
  have hstable : (prefixWord ++ tailWord_1182603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182603).length < 2 ^ (prefixWord ++ tailWord_1182603).sum := by decide
  have hdescent : baseEnd_1182603 < baseStart_1182603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182633 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 6]
def baseStart_1182633 : Nat := 118140960795 + 1182633 * 2 ^ 59
def prefixEnd_1182633 : Nat := 4983230072969 + 3 ^ 40 * 1182633 * 2
def baseEnd_1182633 : Nat := 134946481526394817033039

theorem tailTrace_1182633 : CollatzResearch.WordTrace tailWord_1182633 prefixEnd_1182633 134946481526394817033039 := by
  unfold tailWord_1182633
  simp only [CollatzResearch.WordTrace]
  refine ⟨43134169124530093481248553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28756112749686728987499035 43134169124530093481248553)
  ·
    refine ⟨32350626843397570110936415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43134169124530093481248553 32350626843397570110936415)
    ·
      refine ⟨48525940265096355166404623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32350626843397570110936415 48525940265096355166404623)
      ·
        refine ⟨72788910397644532749606935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48525940265096355166404623 72788910397644532749606935)
        ·
          refine ⟨109183365596466799124410403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72788910397644532749606935 109183365596466799124410403)
          ·
            refine ⟨163775048394700198686615605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109183365596466799124410403 163775048394700198686615605)
            ·
              refine ⟨15353910787003143626870213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163775048394700198686615605 15353910787003143626870213)
              ·
                refine ⟨2878858272563089430038165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15353910787003143626870213 2878858272563089430038165)
                ·
                  refine ⟨134946481526394817033039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2878858272563089430038165 134946481526394817033039)
                  ·
                    rfl

theorem cell22_1182633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_1182633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182633 prefixEnd_1182633 := by exact prefixLift 1182633
  have htrace : WordTrace (prefixWord ++ tailWord_1182633) baseStart_1182633 baseEnd_1182633 := by
    simpa [prefixWord, tailWord_1182633, baseEnd_1182633] using wordTrace_append hprefix tailTrace_1182633
  have hstable : (prefixWord ++ tailWord_1182633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182633).length < 2 ^ (prefixWord ++ tailWord_1182633).sum := by decide
  have hdescent : baseEnd_1182633 < baseStart_1182633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182695 : List Nat := [1, 1, 5, 2, 2, 1, 2, 8]
def baseStart_1182695 : Nat := 118140960795 + 1182695 * 2 ^ 59
def prefixEnd_1182695 : Nat := 4983230072969 + 3 ^ 40 * 1182695 * 2
def baseEnd_1182695 : Nat := 44984518716248550672103

theorem tailTrace_1182695 : CollatzResearch.WordTrace tailWord_1182695 prefixEnd_1182695 44984518716248550672103 := by
  unfold tailWord_1182695
  simp only [CollatzResearch.WordTrace]
  refine ⟨43136430450305478070005539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28757620300203652046670359 43136430450305478070005539)
  ·
    refine ⟨64704645675458217105008309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43136430450305478070005539 64704645675458217105008309)
    ·
      refine ⟨6066060532074207853594529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64704645675458217105008309 6066060532074207853594529)
      ·
        refine ⟨4549545399055655890195897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066060532074207853594529 4549545399055655890195897)
        ·
          refine ⟨3412159049291741917646923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4549545399055655890195897 3412159049291741917646923)
          ·
            refine ⟨5118238573937612876470385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412159049291741917646923 5118238573937612876470385)
            ·
              refine ⟨3838678930453209657352789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118238573937612876470385 3838678930453209657352789)
              ·
                refine ⟨44984518716248550672103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3838678930453209657352789 44984518716248550672103)
                ·
                  rfl

theorem cell22_1182695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 8].length) (baseStart_1182695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182695 prefixEnd_1182695 := by exact prefixLift 1182695
  have htrace : WordTrace (prefixWord ++ tailWord_1182695) baseStart_1182695 baseEnd_1182695 := by
    simpa [prefixWord, tailWord_1182695, baseEnd_1182695] using wordTrace_append hprefix tailTrace_1182695
  have hstable : (prefixWord ++ tailWord_1182695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182695).length < 2 ^ (prefixWord ++ tailWord_1182695).sum := by decide
  have hdescent : baseEnd_1182695 < baseStart_1182695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182718 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1182718 : Nat := 118140960795 + 1182718 * 2 ^ 59
def prefixEnd_1182718 : Nat := 4983230072969 + 3 ^ 40 * 1182718 * 2
def baseEnd_1182718 : Nat := 134956180605424187574619

theorem tailTrace_1182718 : CollatzResearch.WordTrace tailWord_1182718 prefixEnd_1182718 134956180605424187574619 := by
  unfold tailWord_1182718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392158666152769124761601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28758179552814768665395205 5392158666152769124761601)
  ·
    refine ⟨4044118999614576843571201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5392158666152769124761601 4044118999614576843571201)
    ·
      refine ⟨3033089249710932632678401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4044118999614576843571201 3033089249710932632678401)
      ·
        refine ⟨2274816937283199474508801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3033089249710932632678401 2274816937283199474508801)
        ·
          refine ⟨1706112702962399605881601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274816937283199474508801 1706112702962399605881601)
          ·
            refine ⟨1279584527221799704411201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706112702962399605881601 1279584527221799704411201)
            ·
              refine ⟨959688395416349778308401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279584527221799704411201 959688395416349778308401)
              ·
                refine ⟨719766296562262333731301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959688395416349778308401 719766296562262333731301)
                ·
                  refine ⟨134956180605424187574619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719766296562262333731301 134956180605424187574619)
                  ·
                    rfl

theorem cell22_1182718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1182718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182718 prefixEnd_1182718 := by exact prefixLift 1182718
  have htrace : WordTrace (prefixWord ++ tailWord_1182718) baseStart_1182718 baseEnd_1182718 := by
    simpa [prefixWord, tailWord_1182718, baseEnd_1182718] using wordTrace_append hprefix tailTrace_1182718
  have hstable : (prefixWord ++ tailWord_1182718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182718).length < 2 ^ (prefixWord ++ tailWord_1182718).sum := by decide
  have hdescent : baseEnd_1182718 < baseStart_1182718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182727 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1182727 : Nat := 118140960795 + 1182727 * 2 ^ 59
def prefixEnd_1182727 : Nat := 4983230072969 + 3 ^ 40 * 1182727 * 2
def baseEnd_1182727 : Nat := 404871622700199539248829

theorem tailTrace_1182727 : CollatzResearch.WordTrace tailWord_1182727 prefixEnd_1182727 404871622700199539248829 := by
  unfold tailWord_1182727
  simp only [CollatzResearch.WordTrace]
  refine ⟨43137597586189547535170435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28758398390793031690113623 43137597586189547535170435)
  ·
    refine ⟨64706396379284321302755653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43137597586189547535170435 64706396379284321302755653)
    ·
      refine ⟨12132449321115810244266685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64706396379284321302755653 12132449321115810244266685)
      ·
        refine ⟨4549668495418428841600007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12132449321115810244266685 4549668495418428841600007)
        ·
          refine ⟨6824502743127643262400011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549668495418428841600007 6824502743127643262400011)
          ·
            refine ⟨10236754114691464893600017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6824502743127643262400011 10236754114691464893600017)
            ·
              refine ⟨7677565586018598670200013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10236754114691464893600017 7677565586018598670200013)
              ·
                refine ⟨2879087094756974501325005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7677565586018598670200013 2879087094756974501325005)
                ·
                  refine ⟨1079657660533865437996877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2879087094756974501325005 1079657660533865437996877)
                  ·
                    refine ⟨404871622700199539248829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079657660533865437996877 404871622700199539248829)
                    ·
                      rfl

theorem cell22_1182727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1182727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182727 prefixEnd_1182727 := by exact prefixLift 1182727
  have htrace : WordTrace (prefixWord ++ tailWord_1182727) baseStart_1182727 baseEnd_1182727 := by
    simpa [prefixWord, tailWord_1182727, baseEnd_1182727] using wordTrace_append hprefix tailTrace_1182727
  have hstable : (prefixWord ++ tailWord_1182727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182727).length < 2 ^ (prefixWord ++ tailWord_1182727).sum := by decide
  have hdescent : baseEnd_1182727 < baseStart_1182727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182774 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1182774 : Nat := 118140960795 + 1182774 * 2 ^ 59
def prefixEnd_1182774 : Nat := 4983230072969 + 3 ^ 40 * 1182774 * 2
def baseEnd_1182774 : Nat := 134962570586902361107895

theorem tailTrace_1182774 : CollatzResearch.WordTrace tailWord_1182774 prefixEnd_1182774 134962570586902361107895 := by
  unfold tailWord_1182774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696206988563704660133211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28759541211346183041420917 2696206988563704660133211)
  ·
    refine ⟨4044310482845556990199817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2696206988563704660133211 4044310482845556990199817)
    ·
      refine ⟨3033232862134167742649863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4044310482845556990199817 3033232862134167742649863)
      ·
        refine ⟨4549849293201251613974795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033232862134167742649863 4549849293201251613974795)
        ·
          refine ⟨6824773939801877420962193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549849293201251613974795 6824773939801877420962193)
          ·
            refine ⟨5118580454851408065721645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6824773939801877420962193 5118580454851408065721645)
            ·
              refine ⟨1919467670569278024645617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5118580454851408065721645 1919467670569278024645617)
              ·
                refine ⟨1439600752926958518484213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919467670569278024645617 1439600752926958518484213)
                ·
                  refine ⟨134962570586902361107895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1439600752926958518484213 134962570586902361107895)
                  ·
                    rfl

theorem cell22_1182774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1182774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182774 prefixEnd_1182774 := by exact prefixLift 1182774
  have htrace : WordTrace (prefixWord ++ tailWord_1182774) baseStart_1182774 baseEnd_1182774 := by
    simpa [prefixWord, tailWord_1182774, baseEnd_1182774] using wordTrace_append hprefix tailTrace_1182774
  have hstable : (prefixWord ++ tailWord_1182774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182774).length < 2 ^ (prefixWord ++ tailWord_1182774).sum := by decide
  have hdescent : baseEnd_1182774 < baseStart_1182774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182802 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1182802 : Nat := 118140960795 + 1182802 * 2 ^ 59
def prefixEnd_1182802 : Nat := 4983230072969 + 3 ^ 40 * 1182802 * 2
def baseEnd_1182802 : Nat := 134965765577641447874533

theorem tailTrace_1182802 : CollatzResearch.WordTrace tailWord_1182802 prefixEnd_1182802 134965765577641447874533 := by
  unfold tailWord_1182802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10785083265229458836037665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28760222040611890229433773 10785083265229458836037665)
  ·
    refine ⟨8088812448922094127028249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10785083265229458836037665 8088812448922094127028249)
    ·
      refine ⟨6066609336691570595271187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8088812448922094127028249 6066609336691570595271187)
      ·
        refine ⟨9099914005037355892906781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066609336691570595271187 9099914005037355892906781)
        ·
          refine ⟨3412467751889008459840043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9099914005037355892906781 3412467751889008459840043)
          ·
            refine ⟨5118701627833512689760065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412467751889008459840043 5118701627833512689760065)
            ·
              refine ⟨3839026220875134517320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118701627833512689760065 3839026220875134517320049)
              ·
                refine ⟨2879269665656350887990037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839026220875134517320049 2879269665656350887990037)
                ·
                  refine ⟨134965765577641447874533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2879269665656350887990037 134965765577641447874533)
                  ·
                    rfl

theorem cell22_1182802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1182802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182802 prefixEnd_1182802 := by exact prefixLift 1182802
  have htrace : WordTrace (prefixWord ++ tailWord_1182802) baseStart_1182802 baseEnd_1182802 := by
    simpa [prefixWord, tailWord_1182802, baseEnd_1182802] using wordTrace_append hprefix tailTrace_1182802
  have hstable : (prefixWord ++ tailWord_1182802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182802).length < 2 ^ (prefixWord ++ tailWord_1182802).sum := by decide
  have hdescent : baseEnd_1182802 < baseStart_1182802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182815 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_1182815 : Nat := 118140960795 + 1182815 * 2 ^ 59
def prefixEnd_1182815 : Nat := 4983230072969 + 3 ^ 40 * 1182815 * 2
def baseEnd_1182815 : Nat := 404901746898596643048559

theorem tailTrace_1182815 : CollatzResearch.WordTrace tailWord_1182815 prefixEnd_1182815 404901746898596643048559 := by
  unfold tailWord_1182815
  simp only [CollatzResearch.WordTrace]
  refine ⟨43140807209870738564373899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28760538139913825709582599 43140807209870738564373899)
  ·
    refine ⟨64711210814806107846560849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43140807209870738564373899 64711210814806107846560849)
    ·
      refine ⟨48533408111104580884920637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64711210814806107846560849 48533408111104580884920637)
      ·
        refine ⟨18200028041664217831845239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48533408111104580884920637 18200028041664217831845239)
        ·
          refine ⟨27300042062496326747767859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18200028041664217831845239 27300042062496326747767859)
          ·
            refine ⟨40950063093744490121651789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27300042062496326747767859 40950063093744490121651789)
            ·
              refine ⟨15356273660154183795619421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40950063093744490121651789 15356273660154183795619421)
              ·
                refine ⟨5758602622557818923357283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15356273660154183795619421 5758602622557818923357283)
                ·
                  refine ⟨8637903933836728385035925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5758602622557818923357283 8637903933836728385035925)
                  ·
                    refine ⟨404901746898596643048559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8637903933836728385035925 404901746898596643048559)
                    ·
                      rfl

theorem cell22_1182815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_1182815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182815 prefixEnd_1182815 := by exact prefixLift 1182815
  have htrace : WordTrace (prefixWord ++ tailWord_1182815) baseStart_1182815 baseEnd_1182815 := by
    simpa [prefixWord, tailWord_1182815, baseEnd_1182815] using wordTrace_append hprefix tailTrace_1182815
  have hstable : (prefixWord ++ tailWord_1182815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182815).length < 2 ^ (prefixWord ++ tailWord_1182815).sum := by decide
  have hdescent : baseEnd_1182815 < baseStart_1182815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182817 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1182817 : Nat := 118140960795 + 1182817 * 2 ^ 59
def prefixEnd_1182817 : Nat := 4983230072969 + 3 ^ 40 * 1182817 * 2
def baseEnd_1182817 : Nat := 404902431539469304498553

theorem tailTrace_1182817 : CollatzResearch.WordTrace tailWord_1182817 prefixEnd_1182817 404902431539469304498553 := by
  unfold tailWord_1182817
  simp only [CollatzResearch.WordTrace]
  refine ⟨43140880155863492905946705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28760586770575661937297803 43140880155863492905946705)
  ·
    refine ⟨32355660116897619679460029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43140880155863492905946705 32355660116897619679460029)
    ·
      refine ⟨12133372543836607379797511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32355660116897619679460029 12133372543836607379797511)
      ·
        refine ⟨18200058815754911069696267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12133372543836607379797511 18200058815754911069696267)
        ·
          refine ⟨27300088223632366604544401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18200058815754911069696267 27300088223632366604544401)
          ·
            refine ⟨20475066167724274953408301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27300088223632366604544401 20475066167724274953408301)
            ·
              refine ⟨7678149812896603107528113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20475066167724274953408301 7678149812896603107528113)
              ·
                refine ⟨5758612359672452330646085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7678149812896603107528113 5758612359672452330646085)
                ·
                  refine ⟨1079739817438584811996141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5758612359672452330646085 1079739817438584811996141)
                  ·
                    refine ⟨404902431539469304498553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079739817438584811996141 404902431539469304498553)
                    ·
                      rfl

theorem cell22_1182817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1182817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182817 prefixEnd_1182817 := by exact prefixLift 1182817
  have htrace : WordTrace (prefixWord ++ tailWord_1182817) baseStart_1182817 baseEnd_1182817 := by
    simpa [prefixWord, tailWord_1182817, baseEnd_1182817] using wordTrace_append hprefix tailTrace_1182817
  have hstable : (prefixWord ++ tailWord_1182817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182817).length < 2 ^ (prefixWord ++ tailWord_1182817).sum := by decide
  have hdescent : baseEnd_1182817 < baseStart_1182817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182832 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_1182832 : Nat := 118140960795 + 1182832 * 2 ^ 59
def prefixEnd_1182832 : Nat := 4983230072969 + 3 ^ 40 * 1182832 * 2
def baseEnd_1182832 : Nat := 404907566346014265373507

theorem tailTrace_1182832 : CollatzResearch.WordTrace tailWord_1182832 prefixEnd_1182832 404907566346014265373507 := by
  unfold tailWord_1182832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570713625404575233871375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28760951500539433645161833 21570713625404575233871375)
  ·
    refine ⟨32356070438106862850807063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21570713625404575233871375 32356070438106862850807063)
    ·
      refine ⟨48534105657160294276210595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32356070438106862850807063 48534105657160294276210595)
      ·
        refine ⟨72801158485740441414315893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48534105657160294276210595 72801158485740441414315893)
        ·
          refine ⟨6825108608038166382592115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72801158485740441414315893 6825108608038166382592115)
          ·
            refine ⟨10237662912057249573888173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825108608038166382592115 10237662912057249573888173)
            ·
              refine ⟨3839123592021468590208065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10237662912057249573888173 3839123592021468590208065)
              ·
                refine ⟨2879342694016101442656049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839123592021468590208065 2879342694016101442656049)
                ·
                  refine ⟨2159507020512076081992037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2879342694016101442656049 2159507020512076081992037)
                  ·
                    refine ⟨404907566346014265373507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159507020512076081992037 404907566346014265373507)
                    ·
                      rfl

theorem cell22_1182832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_1182832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182832 prefixEnd_1182832 := by exact prefixLift 1182832
  have htrace : WordTrace (prefixWord ++ tailWord_1182832) baseStart_1182832 baseEnd_1182832 := by
    simpa [prefixWord, tailWord_1182832, baseEnd_1182832] using wordTrace_append hprefix tailTrace_1182832
  have hstable : (prefixWord ++ tailWord_1182832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182832).length < 2 ^ (prefixWord ++ tailWord_1182832).sum := by decide
  have hdescent : baseEnd_1182832 < baseStart_1182832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182834 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1182834 : Nat := 118140960795 + 1182834 * 2 ^ 59
def prefixEnd_1182834 : Nat := 4983230072969 + 3 ^ 40 * 1182834 * 2
def baseEnd_1182834 : Nat := 404908250986886926823501

theorem tailTrace_1182834 : CollatzResearch.WordTrace tailWord_1182834 prefixEnd_1182834 404908250986886926823501 := by
  unfold tailWord_1182834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10785375049200476202328889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28761000131201269872877037 10785375049200476202328889)
  ·
    refine ⟨8089031286900357151746667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10785375049200476202328889 8089031286900357151746667)
    ·
      refine ⟨12133546930350535727620001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8089031286900357151746667 12133546930350535727620001)
      ·
        refine ⟨9100160197762901795715001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12133546930350535727620001 9100160197762901795715001)
        ·
          refine ⟨6825120148322176346786251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9100160197762901795715001 6825120148322176346786251)
          ·
            refine ⟨10237680222483264520179377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825120148322176346786251 10237680222483264520179377)
            ·
              refine ⟨7678260166862448390134533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10237680222483264520179377 7678260166862448390134533)
              ·
                refine ⟨1439673781286709073150225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7678260166862448390134533 1439673781286709073150225)
                ·
                  refine ⟨1079755335965031804862669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1439673781286709073150225 1079755335965031804862669)
                  ·
                    refine ⟨404908250986886926823501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1079755335965031804862669 404908250986886926823501)
                    ·
                      rfl

theorem cell22_1182834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1182834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182834 prefixEnd_1182834 := by exact prefixLift 1182834
  have htrace : WordTrace (prefixWord ++ tailWord_1182834) baseStart_1182834 baseEnd_1182834 := by
    simpa [prefixWord, tailWord_1182834, baseEnd_1182834] using wordTrace_append hprefix tailTrace_1182834
  have hstable : (prefixWord ++ tailWord_1182834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182834).length < 2 ^ (prefixWord ++ tailWord_1182834).sum := by decide
  have hdescent : baseEnd_1182834 < baseStart_1182834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182954 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_1182954 : Nat := 118140960795 + 1182954 * 2 ^ 59
def prefixEnd_1182954 : Nat := 4983230072969 + 3 ^ 40 * 1182954 * 2
def baseEnd_1182954 : Nat := 134983109813082204607711

theorem tailTrace_1182954 : CollatzResearch.WordTrace tailWord_1182954 prefixEnd_1182954 134983109813082204607711 := by
  unfold tailWord_1182954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786469239091791325920979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28763917970911443535789277 10786469239091791325920979)
  ·
    refine ⟨16179703858637686988881469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10786469239091791325920979 16179703858637686988881469)
    ·
      refine ⟨6067388946989132620830551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16179703858637686988881469 6067388946989132620830551)
      ·
        refine ⟨9101083420483698931245827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6067388946989132620830551 9101083420483698931245827)
        ·
          refine ⟨13651625130725548396868741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9101083420483698931245827 13651625130725548396868741)
          ·
            refine ⟨2559679712011040324412889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13651625130725548396868741 2559679712011040324412889)
            ·
              refine ⟨1919759784008280243309667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559679712011040324412889 1919759784008280243309667)
              ·
                refine ⟨2879639676012420364964501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919759784008280243309667 2879639676012420364964501)
                ·
                  refine ⟨134983109813082204607711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2879639676012420364964501 134983109813082204607711)
                  ·
                    rfl

theorem cell22_1182954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_1182954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182954 prefixEnd_1182954 := by exact prefixLift 1182954
  have htrace : WordTrace (prefixWord ++ tailWord_1182954) baseStart_1182954 baseEnd_1182954 := by
    simpa [prefixWord, tailWord_1182954, baseEnd_1182954] using wordTrace_append hprefix tailTrace_1182954
  have hstable : (prefixWord ++ tailWord_1182954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182954).length < 2 ^ (prefixWord ++ tailWord_1182954).sum := by decide
  have hdescent : baseEnd_1182954 < baseStart_1182954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182967 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1182967 : Nat := 118140960795 + 1182967 * 2 ^ 59
def prefixEnd_1182967 : Nat := 4983230072969 + 3 ^ 40 * 1182967 * 2
def baseEnd_1182967 : Nat := 404953779604918913248093

theorem tailTrace_1182967 : CollatzResearch.WordTrace tailWord_1182967 prefixEnd_1182967 404953779604918913248093 := by
  unfold tailWord_1182967
  simp only [CollatzResearch.WordTrace]
  refine ⟨43146351105320068523907155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28764234070213379015938103 43146351105320068523907155)
  ·
    refine ⟨64719526657980102785860733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43146351105320068523907155 64719526657980102785860733)
    ·
      refine ⟨24269822496742538544697775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64719526657980102785860733 24269822496742538544697775)
      ·
        refine ⟨36404733745113807817046663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24269822496742538544697775 36404733745113807817046663)
        ·
          refine ⟨54607100617670711725569995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36404733745113807817046663 54607100617670711725569995)
          ·
            refine ⟨81910650926506067588354993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54607100617670711725569995 81910650926506067588354993)
            ·
              refine ⟨61432988194879550691266245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81910650926506067588354993 61432988194879550691266245)
              ·
                refine ⟨11518685286539915754612421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61432988194879550691266245 11518685286539915754612421)
                ·
                  refine ⟨2159753491226234203989829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11518685286539915754612421 2159753491226234203989829)
                  ·
                    refine ⟨404953779604918913248093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159753491226234203989829 404953779604918913248093)
                    ·
                      rfl

theorem cell22_1182967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1182967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1182967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1182967 prefixEnd_1182967 := by exact prefixLift 1182967
  have htrace : WordTrace (prefixWord ++ tailWord_1182967) baseStart_1182967 baseEnd_1182967 := by
    simpa [prefixWord, tailWord_1182967, baseEnd_1182967] using wordTrace_append hprefix tailTrace_1182967
  have hstable : (prefixWord ++ tailWord_1182967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182967).length < 2 ^ (prefixWord ++ tailWord_1182967).sum := by decide
  have hdescent : baseEnd_1182967 < baseStart_1182967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183061 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 5]
def baseStart_1183061 : Nat := 118140960795 + 1183061 * 2 ^ 59
def prefixEnd_1183061 : Nat := 4983230072969 + 3 ^ 40 * 1183061 * 2
def baseEnd_1183061 : Nat := 134995319241978000465935

theorem tailTrace_1183061 : CollatzResearch.WordTrace tailWord_1183061 prefixEnd_1183061 134995319241978000465935 := by
  unfold tailWord_1183061
  simp only [CollatzResearch.WordTrace]
  refine ⟨43149779566979522577829037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28766519711319681718552691 43149779566979522577829037)
  ·
    refine ⟨16181167337617320966685889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43149779566979522577829037 16181167337617320966685889)
    ·
      refine ⟨12135875503212990725014417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16181167337617320966685889 12135875503212990725014417)
      ·
        refine ⟨9101906627409743043760813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12135875503212990725014417 9101906627409743043760813)
        ·
          refine ⟨3413214985278653641410305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9101906627409743043760813 3413214985278653641410305)
          ·
            refine ⟨2559911238958990231057729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413214985278653641410305 2559911238958990231057729)
            ·
              refine ⟨1919933429219242673293297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559911238958990231057729 1919933429219242673293297)
              ·
                refine ⟨1439950071914432004969973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919933429219242673293297 1439950071914432004969973)
                ·
                  refine ⟨134995319241978000465935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1439950071914432004969973 134995319241978000465935)
                  ·
                    rfl

theorem cell22_1183061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_1183061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183061 prefixEnd_1183061 := by exact prefixLift 1183061
  have htrace : WordTrace (prefixWord ++ tailWord_1183061) baseStart_1183061 baseEnd_1183061 := by
    simpa [prefixWord, tailWord_1183061, baseEnd_1183061] using wordTrace_append hprefix tailTrace_1183061
  have hstable : (prefixWord ++ tailWord_1183061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183061).length < 2 ^ (prefixWord ++ tailWord_1183061).sum := by decide
  have hdescent : baseEnd_1183061 < baseStart_1183061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183108 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1183108 : Nat := 118140960795 + 1183108 * 2 ^ 59
def prefixEnd_1183108 : Nat := 4983230072969 + 3 ^ 40 * 1183108 * 2
def baseEnd_1183108 : Nat := 405002046786441545472661

theorem tailTrace_1183108 : CollatzResearch.WordTrace tailWord_1183108 prefixEnd_1183108 405002046786441545472661 := by
  unfold tailWord_1183108
  simp only [CollatzResearch.WordTrace]
  refine ⟨21575746898904624802394989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28767662531872833069859985 21575746898904624802394989)
  ·
    refine ⟨8090905087089234300898121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21575746898904624802394989 8090905087089234300898121)
    ·
      refine ⟨6068178815316925725673591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8090905087089234300898121 6068178815316925725673591)
      ·
        refine ⟨9102268222975388588510387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068178815316925725673591 9102268222975388588510387)
        ·
          refine ⟨13653402334463082882765581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9102268222975388588510387 13653402334463082882765581)
          ·
            refine ⟨5120025875423656081037093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13653402334463082882765581 5120025875423656081037093)
            ·
              refine ⟨960004851641935515194455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5120025875423656081037093 960004851641935515194455)
              ·
                refine ⟨1440007277462903272791683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960004851641935515194455 1440007277462903272791683)
                ·
                  refine ⟨2160010916194354909187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440007277462903272791683 2160010916194354909187525)
                  ·
                    refine ⟨405002046786441545472661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160010916194354909187525 405002046786441545472661)
                    ·
                      rfl

theorem cell22_1183108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1183108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183108 prefixEnd_1183108 := by exact prefixLift 1183108
  have htrace : WordTrace (prefixWord ++ tailWord_1183108) baseStart_1183108 baseEnd_1183108 := by
    simpa [prefixWord, tailWord_1183108, baseEnd_1183108] using wordTrace_append hprefix tailTrace_1183108
  have hstable : (prefixWord ++ tailWord_1183108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183108).length < 2 ^ (prefixWord ++ tailWord_1183108).sum := by decide
  have hdescent : baseEnd_1183108 < baseStart_1183108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183138 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1183138 : Nat := 118140960795 + 1183138 * 2 ^ 59
def prefixEnd_1183138 : Nat := 4983230072969 + 3 ^ 40 * 1183138 * 2
def baseEnd_1183138 : Nat := 405012316399531467222569

theorem tailTrace_1183138 : CollatzResearch.WordTrace tailWord_1183138 prefixEnd_1183138 405012316399531467222569 := by
  unfold tailWord_1183138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10788146996925141182095517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28768391991800376485588045 10788146996925141182095517)
  ·
    refine ⟨4045555123846927943285819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10788146996925141182095517 4045555123846927943285819)
    ·
      refine ⟨6068332685770391914928729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045555123846927943285819 6068332685770391914928729)
      ·
        refine ⟨4551249514327793936196547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6068332685770391914928729 4551249514327793936196547)
        ·
          refine ⟨6826874271491690904294821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551249514327793936196547 6826874271491690904294821)
          ·
            refine ⟨1280038925904692044555279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6826874271491690904294821 1280038925904692044555279)
            ·
              refine ⟨1920058388857038066832919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280038925904692044555279 1920058388857038066832919)
              ·
                refine ⟨2880087583285557100249379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920058388857038066832919 2880087583285557100249379)
                ·
                  refine ⟨4320131374928335650374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880087583285557100249379 4320131374928335650374069)
                  ·
                    refine ⟨405012316399531467222569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4320131374928335650374069 405012316399531467222569)
                    ·
                      rfl

theorem cell22_1183138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1183138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183138 prefixEnd_1183138 := by exact prefixLift 1183138
  have htrace : WordTrace (prefixWord ++ tailWord_1183138) baseStart_1183138 baseEnd_1183138 := by
    simpa [prefixWord, tailWord_1183138, baseEnd_1183138] using wordTrace_append hprefix tailTrace_1183138
  have hstable : (prefixWord ++ tailWord_1183138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183138).length < 2 ^ (prefixWord ++ tailWord_1183138).sum := by decide
  have hdescent : baseEnd_1183138 < baseStart_1183138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183179 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 7]
def baseStart_1183179 : Nat := 118140960795 + 1183179 * 2 ^ 59
def prefixEnd_1183179 : Nat := 4983230072969 + 3 ^ 40 * 1183179 * 2
def baseEnd_1183179 : Nat := 135008783845807008982481

theorem tailTrace_1183179 : CollatzResearch.WordTrace tailWord_1183179 prefixEnd_1183179 135008783845807008982481 := by
  unfold tailWord_1183179
  simp only [CollatzResearch.WordTrace]
  refine ⟨43154083380552028730624591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28769388920368019153749727 43154083380552028730624591)
  ·
    refine ⟨64731125070828043095936887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43154083380552028730624591 64731125070828043095936887)
    ·
      refine ⟨97096687606242064643905331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64731125070828043095936887 97096687606242064643905331)
      ·
        refine ⟨145645031409363096965857997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97096687606242064643905331 145645031409363096965857997)
        ·
          refine ⟨54616886778511161362196749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145645031409363096965857997 54616886778511161362196749)
          ·
            refine ⟨20481332541941685510823781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54616886778511161362196749 20481332541941685510823781)
            ·
              refine ⟨3840249851614066033279459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20481332541941685510823781 3840249851614066033279459)
              ·
                refine ⟨5760374777421099049919189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840249851614066033279459 5760374777421099049919189)
                ·
                  refine ⟨135008783845807008982481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5760374777421099049919189 135008783845807008982481)
                  ·
                    rfl

theorem cell22_1183179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_1183179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183179 prefixEnd_1183179 := by exact prefixLift 1183179
  have htrace : WordTrace (prefixWord ++ tailWord_1183179) baseStart_1183179 baseEnd_1183179 := by
    simpa [prefixWord, tailWord_1183179, baseEnd_1183179] using wordTrace_append hprefix tailTrace_1183179
  have hstable : (prefixWord ++ tailWord_1183179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183179).length < 2 ^ (prefixWord ++ tailWord_1183179).sum := by decide
  have hdescent : baseEnd_1183179 < baseStart_1183179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183183 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 1, 3]
def baseStart_1183183 : Nat := 118140960795 + 1183183 * 2 ^ 59
def prefixEnd_1183183 : Nat := 4983230072969 + 3 ^ 40 * 1183183 * 2
def baseEnd_1183183 : Nat := 405027720819166349847431

theorem tailTrace_1183183 : CollatzResearch.WordTrace tailWord_1183183 prefixEnd_1183183 405027720819166349847431 := by
  unfold tailWord_1183183
  simp only [CollatzResearch.WordTrace]
  refine ⟨43154229272537537413770203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28769486181691691609180135 43154229272537537413770203)
  ·
    refine ⟨64731343908806306120655305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43154229272537537413770203 64731343908806306120655305)
    ·
      refine ⟨48548507931604729590491479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64731343908806306120655305 48548507931604729590491479)
      ·
        refine ⟨72822761897407094385737219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48548507931604729590491479 72822761897407094385737219)
        ·
          refine ⟨109234142846110641578605829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72822761897407094385737219 109234142846110641578605829)
          ·
            refine ⟨20481401783645745295988593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109234142846110641578605829 20481401783645745295988593)
            ·
              refine ⟨15361051337734308971991445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20481401783645745295988593 15361051337734308971991445)
              ·
                refine ⟨720049281456295733062099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15361051337734308971991445 720049281456295733062099)
                ·
                  refine ⟨1080073922184443599593149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720049281456295733062099 1080073922184443599593149)
                  ·
                    refine ⟨405027720819166349847431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080073922184443599593149 405027720819166349847431)
                    ·
                      rfl

theorem cell22_1183183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_1183183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183183 prefixEnd_1183183 := by exact prefixLift 1183183
  have htrace : WordTrace (prefixWord ++ tailWord_1183183) baseStart_1183183 baseEnd_1183183 := by
    simpa [prefixWord, tailWord_1183183, baseEnd_1183183] using wordTrace_append hprefix tailTrace_1183183
  have hstable : (prefixWord ++ tailWord_1183183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183183).length < 2 ^ (prefixWord ++ tailWord_1183183).sum := by decide
  have hdescent : baseEnd_1183183 < baseStart_1183183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183234 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1183234 : Nat := 118140960795 + 1183234 * 2 ^ 59
def prefixEnd_1183234 : Nat := 4983230072969 + 3 ^ 40 * 1183234 * 2
def baseEnd_1183234 : Nat := 405045179161419216822275

theorem tailTrace_1183234 : CollatzResearch.WordTrace tailWord_1183234 prefixEnd_1183234 405045179161419216822275 := by
  unfold tailWord_1183234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789022348838193280969189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28770726263568515415917837 10789022348838193280969189)
  ·
    refine ⟨2022941690407161240181723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10789022348838193280969189 2022941690407161240181723)
    ·
      refine ⟨3034412535610741860272585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022941690407161240181723 3034412535610741860272585)
      ·
        refine ⟨2275809401708056395204439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3034412535610741860272585 2275809401708056395204439)
        ·
          refine ⟨3413714102562084592806659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275809401708056395204439 3413714102562084592806659)
          ·
            refine ⟨5120571153843126889209989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413714102562084592806659 5120571153843126889209989)
            ·
              refine ⟨960107091345586291726873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5120571153843126889209989 960107091345586291726873)
              ·
                refine ⟨720080318509189718795155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960107091345586291726873 720080318509189718795155)
                ·
                  refine ⟨1080120477763784578192733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720080318509189718795155 1080120477763784578192733)
                  ·
                    refine ⟨405045179161419216822275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080120477763784578192733 405045179161419216822275)
                    ·
                      rfl

theorem cell22_1183234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1183234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183234 prefixEnd_1183234 := by exact prefixLift 1183234
  have htrace : WordTrace (prefixWord ++ tailWord_1183234) baseStart_1183234 baseEnd_1183234 := by
    simpa [prefixWord, tailWord_1183234, baseEnd_1183234] using wordTrace_append hprefix tailTrace_1183234
  have hstable : (prefixWord ++ tailWord_1183234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183234).length < 2 ^ (prefixWord ++ tailWord_1183234).sum := by decide
  have hdescent : baseEnd_1183234 < baseStart_1183234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183331 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 7]
def baseStart_1183331 : Nat := 118140960795 + 1183331 * 2 ^ 59
def prefixEnd_1183331 : Nat := 4983230072969 + 3 ^ 40 * 1183331 * 2
def baseEnd_1183331 : Nat := 135026128081247765715659

theorem tailTrace_1183331 : CollatzResearch.WordTrace tailWord_1183331 prefixEnd_1183331 135026128081247765715659 := by
  unfold tailWord_1183331
  simp only [CollatzResearch.WordTrace]
  refine ⟨43159627276001358690157847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28773084850667572460105231 43159627276001358690157847)
  ·
    refine ⟨64739440914002038035236771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43159627276001358690157847 64739440914002038035236771)
    ·
      refine ⟨97109161371003057052855157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64739440914002038035236771 97109161371003057052855157)
      ·
        refine ⟨9103983878531536598705171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97109161371003057052855157 9103983878531536598705171)
        ·
          refine ⟨13655975817797304898057757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103983878531536598705171 13655975817797304898057757)
          ·
            refine ⟨5120990931673989336771659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13655975817797304898057757 5120990931673989336771659)
            ·
              refine ⟨7681486397510984005157489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120990931673989336771659 7681486397510984005157489)
              ·
                refine ⟨5761114798133238003868117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7681486397510984005157489 5761114798133238003868117)
                ·
                  refine ⟨135026128081247765715659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5761114798133238003868117 135026128081247765715659)
                  ·
                    rfl

theorem cell22_1183331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_1183331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183331 prefixEnd_1183331 := by exact prefixLift 1183331
  have htrace : WordTrace (prefixWord ++ tailWord_1183331) baseStart_1183331 baseEnd_1183331 := by
    simpa [prefixWord, tailWord_1183331, baseEnd_1183331] using wordTrace_append hprefix tailTrace_1183331
  have hstable : (prefixWord ++ tailWord_1183331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183331).length < 2 ^ (prefixWord ++ tailWord_1183331).sum := by decide
  have hdescent : baseEnd_1183331 < baseStart_1183331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183376 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_1183376 : Nat := 118140960795 + 1183376 * 2 ^ 59
def prefixEnd_1183376 : Nat := 4983230072969 + 3 ^ 40 * 1183376 * 2
def baseEnd_1183376 : Nat := 135031262887792726590613

theorem tailTrace_1183376 : CollatzResearch.WordTrace tailWord_1183376 prefixEnd_1183376 135031262887792726590613 := by
  unfold tailWord_1183376
  simp only [CollatzResearch.WordTrace]
  refine ⟨21580634280419165687772991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28774179040558887583697321 21580634280419165687772991)
  ·
    refine ⟨32370951420628748531659487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21580634280419165687772991 32370951420628748531659487)
    ·
      refine ⟨48556427130943122797489231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32370951420628748531659487 48556427130943122797489231)
      ·
        refine ⟨72834640696414684196233847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48556427130943122797489231 72834640696414684196233847)
        ·
          refine ⟨109251961044622026294350771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72834640696414684196233847 109251961044622026294350771)
          ·
            refine ⟨163877941566933039441526157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109251961044622026294350771 163877941566933039441526157)
            ·
              refine ⟨61454228087599889790572309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163877941566933039441526157 61454228087599889790572309)
              ·
                refine ⟨2880666941606244833933077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61454228087599889790572309 2880666941606244833933077)
                ·
                  refine ⟨135031262887792726590613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2880666941606244833933077 135031262887792726590613)
                  ·
                    rfl

theorem cell22_1183376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_1183376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183376 prefixEnd_1183376 := by exact prefixLift 1183376
  have htrace : WordTrace (prefixWord ++ tailWord_1183376) baseStart_1183376 baseEnd_1183376 := by
    simpa [prefixWord, tailWord_1183376, baseEnd_1183376] using wordTrace_append hprefix tailTrace_1183376
  have hstable : (prefixWord ++ tailWord_1183376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183376).length < 2 ^ (prefixWord ++ tailWord_1183376).sum := by decide
  have hdescent : baseEnd_1183376 < baseStart_1183376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183395 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 1, 4]
def baseStart_1183395 : Nat := 118140960795 + 1183395 * 2 ^ 59
def prefixEnd_1183395 : Nat := 4983230072969 + 3 ^ 40 * 1183395 * 2
def baseEnd_1183395 : Nat := 405100292751668463546781

theorem tailTrace_1183395 : CollatzResearch.WordTrace tailWord_1183395 prefixEnd_1183395 405100292751668463546781 := by
  unfold tailWord_1183395
  simp only [CollatzResearch.WordTrace]
  refine ⟨43161961547769497620487639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28774641031846331746991759 43161961547769497620487639)
  ·
    refine ⟨64742942321654246430731459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43161961547769497620487639 64742942321654246430731459)
    ·
      refine ⟨97114413482481369646097189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64742942321654246430731459 97114413482481369646097189)
      ·
        refine ⟨18208952527965256808643223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97114413482481369646097189 18208952527965256808643223)
        ·
          refine ⟨27313428791947885212964835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208952527965256808643223 27313428791947885212964835)
          ·
            refine ⟨40970143187921827819447253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27313428791947885212964835 40970143187921827819447253)
            ·
              refine ⟨960237730966917839518295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40970143187921827819447253 960237730966917839518295)
              ·
                refine ⟨1440356596450376759277443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960237730966917839518295 1440356596450376759277443)
                ·
                  refine ⟨2160534894675565138916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440356596450376759277443 2160534894675565138916165)
                  ·
                    refine ⟨405100292751668463546781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160534894675565138916165 405100292751668463546781)
                    ·
                      rfl

theorem cell22_1183395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 4].length) (baseStart_1183395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183395 prefixEnd_1183395 := by exact prefixLift 1183395
  have htrace : WordTrace (prefixWord ++ tailWord_1183395) baseStart_1183395 baseEnd_1183395 := by
    simpa [prefixWord, tailWord_1183395, baseEnd_1183395] using wordTrace_append hprefix tailTrace_1183395
  have hstable : (prefixWord ++ tailWord_1183395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183395).length < 2 ^ (prefixWord ++ tailWord_1183395).sum := by decide
  have hdescent : baseEnd_1183395 < baseStart_1183395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183408 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_1183408 : Nat := 118140960795 + 1183408 * 2 ^ 59
def prefixEnd_1183408 : Nat := 4983230072969 + 3 ^ 40 * 1183408 * 2
def baseEnd_1183408 : Nat := 405104742917340762971741

theorem tailTrace_1183408 : CollatzResearch.WordTrace tailWord_1183408 prefixEnd_1183408 405104742917340762971741 := by
  unfold tailWord_1183408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21581217848361200420355439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28774957131148267227140585 21581217848361200420355439)
  ·
    refine ⟨32371826772541800630533159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21581217848361200420355439 32371826772541800630533159)
    ·
      refine ⟨48557740158812700945799739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32371826772541800630533159 48557740158812700945799739)
      ·
        refine ⟨72836610238219051418699609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48557740158812700945799739 72836610238219051418699609)
        ·
          refine ⟨54627457678664288564024707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72836610238219051418699609 54627457678664288564024707)
          ·
            refine ⟨81941186517996432846037061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54627457678664288564024707 81941186517996432846037061)
            ·
              refine ⟨15363972472124331158631949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81941186517996432846037061 15363972472124331158631949)
              ·
                refine ⟨5761489677046624184486981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15363972472124331158631949 5761489677046624184486981)
                ·
                  refine ⟨1080279314446242034591309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5761489677046624184486981 1080279314446242034591309)
                  ·
                    refine ⟨405104742917340762971741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080279314446242034591309 405104742917340762971741)
                    ·
                      rfl

theorem cell22_1183408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_1183408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183408 prefixEnd_1183408 := by exact prefixLift 1183408
  have htrace : WordTrace (prefixWord ++ tailWord_1183408) baseStart_1183408 baseEnd_1183408 := by
    simpa [prefixWord, tailWord_1183408, baseEnd_1183408] using wordTrace_append hprefix tailTrace_1183408
  have hstable : (prefixWord ++ tailWord_1183408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183408).length < 2 ^ (prefixWord ++ tailWord_1183408).sum := by decide
  have hdescent : baseEnd_1183408 < baseStart_1183408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183459 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 2, 3]
def baseStart_1183459 : Nat := 118140960795 + 1183459 * 2 ^ 59
def prefixEnd_1183459 : Nat := 4983230072969 + 3 ^ 40 * 1183459 * 2
def baseEnd_1183459 : Nat := 405122201259593629946585

theorem tailTrace_1183459 : CollatzResearch.WordTrace tailWord_1183459 prefixEnd_1183459 405122201259593629946585 := by
  unfold tailWord_1183459
  simp only [CollatzResearch.WordTrace]
  refine ⟨43164295819537636550817431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28776197213025091033878287 43164295819537636550817431)
  ·
    refine ⟨64746443729306454826226147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43164295819537636550817431 64746443729306454826226147)
    ·
      refine ⟨97119665593959682239339221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64746443729306454826226147 97119665593959682239339221)
      ·
        refine ⟨2276242162358430052484513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 97119665593959682239339221 2276242162358430052484513)
        ·
          refine ⟨1707181621768822539363385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276242162358430052484513 1707181621768822539363385)
          ·
            refine ⟨1280386216326616904522539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707181621768822539363385 1280386216326616904522539)
            ·
              refine ⟨1920579324489925356783809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280386216326616904522539 1920579324489925356783809)
              ·
                refine ⟨1440434493367444017587857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920579324489925356783809 1440434493367444017587857)
                ·
                  refine ⟨1080325870025583013190893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440434493367444017587857 1080325870025583013190893)
                  ·
                    refine ⟨405122201259593629946585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080325870025583013190893 405122201259593629946585)
                    ·
                      rfl

theorem cell22_1183459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3].length) (baseStart_1183459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183459 prefixEnd_1183459 := by exact prefixLift 1183459
  have htrace : WordTrace (prefixWord ++ tailWord_1183459) baseStart_1183459 baseEnd_1183459 := by
    simpa [prefixWord, tailWord_1183459, baseEnd_1183459] using wordTrace_append hprefix tailTrace_1183459
  have hstable : (prefixWord ++ tailWord_1183459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183459).length < 2 ^ (prefixWord ++ tailWord_1183459).sum := by decide
  have hdescent : baseEnd_1183459 < baseStart_1183459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183560 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1183560 : Nat := 118140960795 + 1183560 * 2 ^ 59
def prefixEnd_1183560 : Nat := 4983230072969 + 3 ^ 40 * 1183560 * 2
def baseEnd_1183560 : Nat := 405156775623663033171275

theorem tailTrace_1183560 : CollatzResearch.WordTrace tailWord_1183560 prefixEnd_1183560 405156775623663033171275 := by
  unfold tailWord_1183560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21583989796085865400122067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28778653061447820533496089 21583989796085865400122067)
  ·
    refine ⟨32375984694128798100183101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21583989796085865400122067 32375984694128798100183101)
    ·
      refine ⟨12140994260298299287568663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32375984694128798100183101 12140994260298299287568663)
      ·
        refine ⟨18211491390447448931352995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12140994260298299287568663 18211491390447448931352995)
        ·
          refine ⟨27317237085671173397029493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18211491390447448931352995 27317237085671173397029493)
          ·
            refine ⟨2560990976781672505971515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27317237085671173397029493 2560990976781672505971515)
            ·
              refine ⟨3841486465172508758957273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560990976781672505971515 3841486465172508758957273)
              ·
                refine ⟨2881114848879381569217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841486465172508758957273 2881114848879381569217955)
                ·
                  refine ⟨4321672273319072353826933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881114848879381569217955 4321672273319072353826933)
                  ·
                    refine ⟨405156775623663033171275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4321672273319072353826933 405156775623663033171275)
                    ·
                      rfl

theorem cell22_1183560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1183560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183560 prefixEnd_1183560 := by exact prefixLift 1183560
  have htrace : WordTrace (prefixWord ++ tailWord_1183560) baseStart_1183560 baseEnd_1183560 := by
    simpa [prefixWord, tailWord_1183560, baseEnd_1183560] using wordTrace_append hprefix tailTrace_1183560
  have hstable : (prefixWord ++ tailWord_1183560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183560).length < 2 ^ (prefixWord ++ tailWord_1183560).sum := by decide
  have hdescent : baseEnd_1183560 < baseStart_1183560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183564 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_1183564 : Nat := 118140960795 + 1183564 * 2 ^ 59
def prefixEnd_1183564 : Nat := 4983230072969 + 3 ^ 40 * 1183564 * 2
def baseEnd_1183564 : Nat := 405158144905408356071263

theorem tailTrace_1183564 : CollatzResearch.WordTrace tailWord_1183564 prefixEnd_1183564 405158144905408356071263 := by
  unfold tailWord_1183564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21584062742078619741694873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28778750322771492988926497 21584062742078619741694873)
  ·
    refine ⟨16188047056558964806271155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21584062742078619741694873 16188047056558964806271155)
    ·
      refine ⟨24282070584838447209406733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16188047056558964806271155 24282070584838447209406733)
      ·
        refine ⟨9105776469314417703527525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24282070584838447209406733 9105776469314417703527525)
        ·
          refine ⟨1707333087996453319411411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9105776469314417703527525 1707333087996453319411411)
          ·
            refine ⟨2560999631994679979117117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707333087996453319411411 2560999631994679979117117)
            ·
              refine ⟨960374861998004992168919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2560999631994679979117117 960374861998004992168919)
              ·
                refine ⟨1440562292997007488253379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960374861998004992168919 1440562292997007488253379)
                ·
                  refine ⟨2160843439495511232380069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440562292997007488253379 2160843439495511232380069)
                  ·
                    refine ⟨405158144905408356071263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160843439495511232380069 405158144905408356071263)
                    ·
                      rfl

theorem cell22_1183564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_1183564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183564 prefixEnd_1183564 := by exact prefixLift 1183564
  have htrace : WordTrace (prefixWord ++ tailWord_1183564) baseStart_1183564 baseEnd_1183564 := by
    simpa [prefixWord, tailWord_1183564, baseEnd_1183564] using wordTrace_append hprefix tailTrace_1183564
  have hstable : (prefixWord ++ tailWord_1183564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183564).length < 2 ^ (prefixWord ++ tailWord_1183564).sum := by decide
  have hdescent : baseEnd_1183564 < baseStart_1183564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183573 : List Nat := [1, 3, 2, 2, 2, 12]
def baseStart_1183573 : Nat := 118140960795 + 1183573 * 2 ^ 59
def prefixEnd_1183573 : Nat := 4983230072969 + 3 ^ 40 * 1183573 * 2
def baseEnd_1183573 : Nat := 5001990441843646081435

theorem tailTrace_1183573 : CollatzResearch.WordTrace tailWord_1183573 prefixEnd_1183573 5001990441843646081435 := by
  unfold tailWord_1183573
  simp only [CollatzResearch.WordTrace]
  refine ⟨43168453741124634020467373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28778969160749756013644915 43168453741124634020467373)
  ·
    refine ⟨16188170152921737757675265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43168453741124634020467373 16188170152921737757675265)
    ·
      refine ⟨12141127614691303318256449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16188170152921737757675265 12141127614691303318256449)
      ·
        refine ⟨9105845711018477488692337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12141127614691303318256449 9105845711018477488692337)
        ·
          refine ⟨6829384283263858116519253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9105845711018477488692337 6829384283263858116519253)
          ·
            refine ⟨5001990441843646081435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6829384283263858116519253 5001990441843646081435)
            ·
              rfl

theorem cell22_1183573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 12].length) (baseStart_1183573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183573 prefixEnd_1183573 := by exact prefixLift 1183573
  have htrace : WordTrace (prefixWord ++ tailWord_1183573) baseStart_1183573 baseEnd_1183573 := by
    simpa [prefixWord, tailWord_1183573, baseEnd_1183573] using wordTrace_append hprefix tailTrace_1183573
  have hstable : (prefixWord ++ tailWord_1183573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183573).length < 2 ^ (prefixWord ++ tailWord_1183573).sum := by decide
  have hdescent : baseEnd_1183573 < baseStart_1183573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183577 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_1183577 : Nat := 118140960795 + 1183577 * 2 ^ 59
def prefixEnd_1183577 : Nat := 4983230072969 + 3 ^ 40 * 1183577 * 2
def baseEnd_1183577 : Nat := 405162595071080655496223

theorem tailTrace_1183577 : CollatzResearch.WordTrace tailWord_1183577 prefixEnd_1183577 405162595071080655496223 := by
  unfold tailWord_1183577
  simp only [CollatzResearch.WordTrace]
  refine ⟨43168599633110142703612985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28779066422073428469075323 43168599633110142703612985)
  ·
    refine ⟨32376449724832607027709739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43168599633110142703612985 32376449724832607027709739)
    ·
      refine ⟨48564674587248910541564609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32376449724832607027709739 48564674587248910541564609)
      ·
        refine ⟨36423505940436682906173457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48564674587248910541564609 36423505940436682906173457)
        ·
          refine ⟨27317629455327512179630093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36423505940436682906173457 27317629455327512179630093)
          ·
            refine ⟨10244111045747817067361285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27317629455327512179630093 10244111045747817067361285)
            ·
              refine ⟨1920770821077715700130241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10244111045747817067361285 1920770821077715700130241)
              ·
                refine ⟨1440578115808286775097681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920770821077715700130241 1440578115808286775097681)
                ·
                  refine ⟨1080433586856215081323261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440578115808286775097681 1080433586856215081323261)
                  ·
                    refine ⟨405162595071080655496223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080433586856215081323261 405162595071080655496223)
                    ·
                      rfl

theorem cell22_1183577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_1183577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183577 prefixEnd_1183577 := by exact prefixLift 1183577
  have htrace : WordTrace (prefixWord ++ tailWord_1183577) baseStart_1183577 baseEnd_1183577 := by
    simpa [prefixWord, tailWord_1183577, baseEnd_1183577] using wordTrace_append hprefix tailTrace_1183577
  have hstable : (prefixWord ++ tailWord_1183577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183577).length < 2 ^ (prefixWord ++ tailWord_1183577).sum := by decide
  have hdescent : baseEnd_1183577 < baseStart_1183577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183594 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1183594 : Nat := 118140960795 + 1183594 * 2 ^ 59
def prefixEnd_1183594 : Nat := 4983230072969 + 3 ^ 40 * 1183594 * 2
def baseEnd_1183594 : Nat := 405168414518498277821171

theorem tailTrace_1183594 : CollatzResearch.WordTrace tailWord_1183594 prefixEnd_1183594 405168414518498277821171 := by
  unfold tailWord_1183594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10792304918512138651745459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28779479782699036404654557 10792304918512138651745459)
  ·
    refine ⟨16188457377768207977618189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10792304918512138651745459 16188457377768207977618189)
    ·
      refine ⟨6070671516663077991606821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16188457377768207977618189 6070671516663077991606821)
      ·
        refine ⟨1138250909374327123426279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6070671516663077991606821 1138250909374327123426279)
        ·
          refine ⟨1707376364061490685139419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138250909374327123426279 1707376364061490685139419)
          ·
            refine ⟨2561064546092236027709129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707376364061490685139419 2561064546092236027709129)
            ·
              refine ⟨1920798409569177020781847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561064546092236027709129 1920798409569177020781847)
              ·
                refine ⟨2881197614353765531172771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920798409569177020781847 2881197614353765531172771)
                ·
                  refine ⟨4321796421530648296759157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881197614353765531172771 4321796421530648296759157)
                  ·
                    refine ⟨405168414518498277821171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4321796421530648296759157 405168414518498277821171)
                    ·
                      rfl

theorem cell22_1183594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1183594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183594 prefixEnd_1183594 := by exact prefixLift 1183594
  have htrace : WordTrace (prefixWord ++ tailWord_1183594) baseStart_1183594 baseEnd_1183594 := by
    simpa [prefixWord, tailWord_1183594, baseEnd_1183594] using wordTrace_append hprefix tailTrace_1183594
  have hstable : (prefixWord ++ tailWord_1183594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183594).length < 2 ^ (prefixWord ++ tailWord_1183594).sum := by decide
  have hdescent : baseEnd_1183594 < baseStart_1183594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183603 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_1183603 : Nat := 118140960795 + 1183603 * 2 ^ 59
def prefixEnd_1183603 : Nat := 4983230072969 + 3 ^ 40 * 1183603 * 2
def baseEnd_1183603 : Nat := 405171495402425254346143

theorem tailTrace_1183603 : CollatzResearch.WordTrace tailWord_1183603 prefixEnd_1183603 405171495402425254346143 := by
  unfold tailWord_1183603
  simp only [CollatzResearch.WordTrace]
  refine ⟨43169547931015949144059463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28779698620677299429372975 43169547931015949144059463)
  ·
    refine ⟨64754321896523923716089195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43169547931015949144059463 64754321896523923716089195)
    ·
      refine ⟨97131482844785885574133793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64754321896523923716089195 97131482844785885574133793)
      ·
        refine ⟨72848612133589414180600345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97131482844785885574133793 72848612133589414180600345)
        ·
          refine ⟨54636459100192060635450259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72848612133589414180600345 54636459100192060635450259)
          ·
            refine ⟨81954688650288090953175389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54636459100192060635450259 81954688650288090953175389)
            ·
              refine ⟨30733008243858034107440771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81954688650288090953175389 30733008243858034107440771)
              ·
                refine ⟨46099512365787051161161157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30733008243858034107440771 46099512365787051161161157)
                ·
                  refine ⟨8643658568585072092717717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46099512365787051161161157 8643658568585072092717717)
                  ·
                    refine ⟨405171495402425254346143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8643658568585072092717717 405171495402425254346143)
                    ·
                      rfl

theorem cell22_1183603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_1183603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183603 prefixEnd_1183603 := by exact prefixLift 1183603
  have htrace : WordTrace (prefixWord ++ tailWord_1183603) baseStart_1183603 baseEnd_1183603 := by
    simpa [prefixWord, tailWord_1183603, baseEnd_1183603] using wordTrace_append hprefix tailTrace_1183603
  have hstable : (prefixWord ++ tailWord_1183603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183603).length < 2 ^ (prefixWord ++ tailWord_1183603).sum := by decide
  have hdescent : baseEnd_1183603 < baseStart_1183603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183639 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 1, 3]
def baseStart_1183639 : Nat := 118140960795 + 1183639 * 2 ^ 59
def prefixEnd_1183639 : Nat := 4983230072969 + 3 ^ 40 * 1183639 * 2
def baseEnd_1183639 : Nat := 405183818938133160446033

theorem tailTrace_1183639 : CollatzResearch.WordTrace tailWord_1183639 prefixEnd_1183639 405183818938133160446033 := by
  unfold tailWord_1183639
  simp only [CollatzResearch.WordTrace]
  refine ⟨43170860958885527292369971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28780573972590351528246647 43170860958885527292369971)
  ·
    refine ⟨64756291438328290938554957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43170860958885527292369971 64756291438328290938554957)
    ·
      refine ⟨24283609289373109101958109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64756291438328290938554957 24283609289373109101958109)
      ·
        refine ⟨9106353483514915913234291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24283609289373109101958109 9106353483514915913234291)
        ·
          refine ⟨13659530225272373869851437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106353483514915913234291 13659530225272373869851437)
          ·
            refine ⟨5122323834477140201194289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13659530225272373869851437 5122323834477140201194289)
            ·
              refine ⟨3841742875857855150895717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5122323834477140201194289 3841742875857855150895717)
              ·
                refine ⟨720326789223347840792947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3841742875857855150895717 720326789223347840792947)
                ·
                  refine ⟨1080490183835021761189421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720326789223347840792947 1080490183835021761189421)
                  ·
                    refine ⟨405183818938133160446033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080490183835021761189421 405183818938133160446033)
                    ·
                      rfl

theorem cell22_1183639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_1183639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183639 prefixEnd_1183639 := by exact prefixLift 1183639
  have htrace : WordTrace (prefixWord ++ tailWord_1183639) baseStart_1183639 baseEnd_1183639 := by
    simpa [prefixWord, tailWord_1183639, baseEnd_1183639] using wordTrace_append hprefix tailTrace_1183639
  have hstable : (prefixWord ++ tailWord_1183639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183639).length < 2 ^ (prefixWord ++ tailWord_1183639).sum := by decide
  have hdescent : baseEnd_1183639 < baseStart_1183639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183727 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 2, 4]
def baseStart_1183727 : Nat := 118140960795 + 1183727 * 2 ^ 59
def prefixEnd_1183727 : Nat := 4983230072969 + 3 ^ 40 * 1183727 * 2
def baseEnd_1183727 : Nat := 405213943136530264245763

theorem tailTrace_1183727 : CollatzResearch.WordTrace tailWord_1183727 prefixEnd_1183727 405213943136530264245763 := by
  unfold tailWord_1183727
  simp only [CollatzResearch.WordTrace]
  refine ⟨43174070582566718321573435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28782713721711145547715623 43174070582566718321573435)
  ·
    refine ⟨64761105873850077482360153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43174070582566718321573435 64761105873850077482360153)
    ·
      refine ⟨48570829405387558111770115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64761105873850077482360153 48570829405387558111770115)
      ·
        refine ⟨72856244108081337167655173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48570829405387558111770115 72856244108081337167655173)
        ·
          refine ⟨13660545770265250718935345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72856244108081337167655173 13660545770265250718935345)
          ·
            refine ⟨10245409327698938039201509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13660545770265250718935345 10245409327698938039201509)
            ·
              refine ⟨1921014248943550882350283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10245409327698938039201509 1921014248943550882350283)
              ·
                refine ⟨2881521373415326323525425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921014248943550882350283 2881521373415326323525425)
                ·
                  refine ⟨2161141030061494742644069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881521373415326323525425 2161141030061494742644069)
                  ·
                    refine ⟨405213943136530264245763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161141030061494742644069 405213943136530264245763)
                    ·
                      rfl

theorem cell22_1183727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_1183727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183727 prefixEnd_1183727 := by exact prefixLift 1183727
  have htrace : WordTrace (prefixWord ++ tailWord_1183727) baseStart_1183727 baseEnd_1183727 := by
    simpa [prefixWord, tailWord_1183727, baseEnd_1183727] using wordTrace_append hprefix tailTrace_1183727
  have hstable : (prefixWord ++ tailWord_1183727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183727).length < 2 ^ (prefixWord ++ tailWord_1183727).sum := by decide
  have hdescent : baseEnd_1183727 < baseStart_1183727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183742 : List Nat := [4, 2, 2, 2, 1, 11]
def baseStart_1183742 : Nat := 118140960795 + 1183742 * 2 ^ 59
def prefixEnd_1183742 : Nat := 4983230072969 + 3 ^ 40 * 1183742 * 2
def baseEnd_1183742 : Nat := 5002704665963891668157

theorem tailTrace_1183742 : CollatzResearch.WordTrace tailWord_1183742 prefixEnd_1183742 5002704665963891668157 := by
  unfold tailWord_1183742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396827209689046985421185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28783078451674917255579653 5396827209689046985421185)
  ·
    refine ⟨4047620407266785239065889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5396827209689046985421185 4047620407266785239065889)
    ·
      refine ⟨3035715305450088929299417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4047620407266785239065889 3035715305450088929299417)
      ·
        refine ⟨2276786479087566696974563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035715305450088929299417 2276786479087566696974563)
        ·
          refine ⟨3415179718631350045461845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276786479087566696974563 3415179718631350045461845)
          ·
            refine ⟨5002704665963891668157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3415179718631350045461845 5002704665963891668157)
            ·
              rfl

theorem cell22_1183742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 11].length) (baseStart_1183742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183742 prefixEnd_1183742 := by exact prefixLift 1183742
  have htrace : WordTrace (prefixWord ++ tailWord_1183742) baseStart_1183742 baseEnd_1183742 := by
    simpa [prefixWord, tailWord_1183742, baseEnd_1183742] using wordTrace_append hprefix tailTrace_1183742
  have hstable : (prefixWord ++ tailWord_1183742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183742).length < 2 ^ (prefixWord ++ tailWord_1183742).sum := by decide
  have hdescent : baseEnd_1183742 < baseStart_1183742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183755 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_1183755 : Nat := 118140960795 + 1183755 * 2 ^ 59
def prefixEnd_1183755 : Nat := 4983230072969 + 3 ^ 40 * 1183755 * 2
def baseEnd_1183755 : Nat := 405223528108747524545677

theorem tailTrace_1183755 : CollatzResearch.WordTrace tailWord_1183755 prefixEnd_1183755 405223528108747524545677 := by
  unfold tailWord_1183755
  simp only [CollatzResearch.WordTrace]
  refine ⟨43175091826465279103592719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28783394550976852735728479 43175091826465279103592719)
  ·
    refine ⟨64762637739697918655389079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43175091826465279103592719 64762637739697918655389079)
    ·
      refine ⟨97143956609546877983083619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64762637739697918655389079 97143956609546877983083619)
      ·
        refine ⟨145715934914320316974625429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97143956609546877983083619 145715934914320316974625429)
        ·
          refine ⟨6830434449108764858185567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145715934914320316974625429 6830434449108764858185567)
          ·
            refine ⟨10245651673663147287278351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6830434449108764858185567 10245651673663147287278351)
            ·
              refine ⟨15368477510494720930917527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10245651673663147287278351 15368477510494720930917527)
              ·
                refine ⟨23052716265742081396376291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15368477510494720930917527 23052716265742081396376291)
                ·
                  refine ⟨34579074398613122094564437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23052716265742081396376291 34579074398613122094564437)
                  ·
                    refine ⟨405223528108747524545677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34579074398613122094564437 405223528108747524545677)
                    ·
                      rfl

theorem cell22_1183755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_1183755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183755 prefixEnd_1183755 := by exact prefixLift 1183755
  have htrace : WordTrace (prefixWord ++ tailWord_1183755) baseStart_1183755 baseEnd_1183755 := by
    simpa [prefixWord, tailWord_1183755, baseEnd_1183755] using wordTrace_append hprefix tailTrace_1183755
  have hstable : (prefixWord ++ tailWord_1183755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183755).length < 2 ^ (prefixWord ++ tailWord_1183755).sum := by decide
  have hdescent : baseEnd_1183755 < baseStart_1183755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183821 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1183821 : Nat := 118140960795 + 1183821 * 2 ^ 59
def prefixEnd_1183821 : Nat := 4983230072969 + 3 ^ 40 * 1183821 * 2
def baseEnd_1183821 : Nat := 135082040419181784131825

theorem tailTrace_1183821 : CollatzResearch.WordTrace tailWord_1183821 prefixEnd_1183821 135082040419181784131825 := by
  unfold tailWord_1183821
  simp only [CollatzResearch.WordTrace]
  refine ⟨43177499044226172375495317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28784999362817448250330211 43177499044226172375495317)
  ·
    refine ⟨2023945267698101830101343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43177499044226172375495317 2023945267698101830101343)
    ·
      refine ⟨3035917901547152745152015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023945267698101830101343 3035917901547152745152015)
      ·
        refine ⟨4553876852320729117728023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035917901547152745152015 4553876852320729117728023)
        ·
          refine ⟨6830815278481093676592035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4553876852320729117728023 6830815278481093676592035)
          ·
            refine ⟨10246222917721640514888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6830815278481093676592035 10246222917721640514888053)
            ·
              refine ⟨960583398536403798270755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10246222917721640514888053 960583398536403798270755)
              ·
                refine ⟨1440875097804605697406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960583398536403798270755 1440875097804605697406133)
                ·
                  refine ⟨135082040419181784131825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1440875097804605697406133 135082040419181784131825)
                  ·
                    rfl

theorem cell22_1183821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1183821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183821 prefixEnd_1183821 := by exact prefixLift 1183821
  have htrace : WordTrace (prefixWord ++ tailWord_1183821) baseStart_1183821 baseEnd_1183821 := by
    simpa [prefixWord, tailWord_1183821, baseEnd_1183821] using wordTrace_append hprefix tailTrace_1183821
  have hstable : (prefixWord ++ tailWord_1183821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183821).length < 2 ^ (prefixWord ++ tailWord_1183821).sum := by decide
  have hdescent : baseEnd_1183821 < baseStart_1183821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183832 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_1183832 : Nat := 118140960795 + 1183832 * 2 ^ 59
def prefixEnd_1183832 : Nat := 4983230072969 + 3 ^ 40 * 1183832 * 2
def baseEnd_1183832 : Nat := 135083295594114996790147

theorem tailTrace_1183832 : CollatzResearch.WordTrace tailWord_1183832 prefixEnd_1183832 135083295594114996790147 := by
  unfold tailWord_1183832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21588950123593160627072875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28785266831457547502763833 21588950123593160627072875)
  ·
    refine ⟨32383425185389740940609313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21588950123593160627072875 32383425185389740940609313)
    ·
      refine ⟨24287568889042305705456985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32383425185389740940609313 24287568889042305705456985)
      ·
        refine ⟨18215676666781729279092739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24287568889042305705456985 18215676666781729279092739)
        ·
          refine ⟨27323515000172593918639109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18215676666781729279092739 27323515000172593918639109)
          ·
            refine ⟨5123159062532361359744833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27323515000172593918639109 5123159062532361359744833)
            ·
              refine ⟨3842369296899271019808625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123159062532361359744833 3842369296899271019808625)
              ·
                refine ⟨2881776972674453264856469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842369296899271019808625 2881776972674453264856469)
                ·
                  refine ⟨135083295594114996790147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2881776972674453264856469 135083295594114996790147)
                  ·
                    rfl

theorem cell22_1183832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_1183832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183832 prefixEnd_1183832 := by exact prefixLift 1183832
  have htrace : WordTrace (prefixWord ++ tailWord_1183832) baseStart_1183832 baseEnd_1183832 := by
    simpa [prefixWord, tailWord_1183832, baseEnd_1183832] using wordTrace_append hprefix tailTrace_1183832
  have hstable : (prefixWord ++ tailWord_1183832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183832).length < 2 ^ (prefixWord ++ tailWord_1183832).sum := by decide
  have hdescent : baseEnd_1183832 < baseStart_1183832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183834 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_1183834 : Nat := 118140960795 + 1183834 * 2 ^ 59
def prefixEnd_1183834 : Nat := 4983230072969 + 3 ^ 40 * 1183834 * 2
def baseEnd_1183834 : Nat := 405250571423217651820435

theorem tailTrace_1183834 : CollatzResearch.WordTrace tailWord_1183834 prefixEnd_1183834 405250571423217651820435 := by
  unfold tailWord_1183834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10794493298294768898929639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28785315462119383730479037 10794493298294768898929639)
  ·
    refine ⟨16191739947442153348394459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10794493298294768898929639 16191739947442153348394459)
    ·
      refine ⟨24287609921163230022591689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16191739947442153348394459 24287609921163230022591689)
      ·
        refine ⟨18215707440872422516943767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24287609921163230022591689 18215707440872422516943767)
        ·
          refine ⟨27323561161308633775415651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18215707440872422516943767 27323561161308633775415651)
          ·
            refine ⟨40985341741962950663123477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27323561161308633775415651 40985341741962950663123477)
            ·
              refine ⟨1921187894154513312333913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40985341741962950663123477 1921187894154513312333913)
              ·
                refine ⟨1440890920615884984250435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921187894154513312333913 1440890920615884984250435)
                ·
                  refine ⟨2161336380923827476375653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440890920615884984250435 2161336380923827476375653)
                  ·
                    refine ⟨405250571423217651820435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161336380923827476375653 405250571423217651820435)
                    ·
                      rfl

theorem cell22_1183834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_1183834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183834 prefixEnd_1183834 := by exact prefixLift 1183834
  have htrace : WordTrace (prefixWord ++ tailWord_1183834) baseStart_1183834 baseEnd_1183834 := by
    simpa [prefixWord, tailWord_1183834, baseEnd_1183834] using wordTrace_append hprefix tailTrace_1183834
  have hstable : (prefixWord ++ tailWord_1183834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183834).length < 2 ^ (prefixWord ++ tailWord_1183834).sum := by decide
  have hdescent : baseEnd_1183834 < baseStart_1183834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183842 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1183842 : Nat := 118140960795 + 1183842 * 2 ^ 59
def prefixEnd_1183842 : Nat := 4983230072969 + 3 ^ 40 * 1183842 * 2
def baseEnd_1183842 : Nat := 405253309986708297620411

theorem tailTrace_1183842 : CollatzResearch.WordTrace tailWord_1183842 prefixEnd_1183842 405253309986708297620411 := by
  unfold tailWord_1183842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10794566244287523240502445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28785509984766728641339853 10794566244287523240502445)
  ·
    refine ⟨4047962341607821215188417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10794566244287523240502445 4047962341607821215188417)
    ·
      refine ⟨3035971756205865911391313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4047962341607821215188417 3035971756205865911391313)
      ·
        refine ⟨2276978817154399433543485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035971756205865911391313 2276978817154399433543485)
        ·
          refine ⟨853867056432899787578807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2276978817154399433543485 853867056432899787578807)
          ·
            refine ⟨1280800584649349681368211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853867056432899787578807 1280800584649349681368211)
            ·
              refine ⟨1921200876974024522052317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280800584649349681368211 1921200876974024522052317)
              ·
                refine ⟨720450328865259195769619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1921200876974024522052317 720450328865259195769619)
                ·
                  refine ⟨1080675493297888793654429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720450328865259195769619 1080675493297888793654429)
                  ·
                    refine ⟨405253309986708297620411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080675493297888793654429 405253309986708297620411)
                    ·
                      rfl

theorem cell22_1183842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1183842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183842 prefixEnd_1183842 := by exact prefixLift 1183842
  have htrace : WordTrace (prefixWord ++ tailWord_1183842) baseStart_1183842 baseEnd_1183842 := by
    simpa [prefixWord, tailWord_1183842, baseEnd_1183842] using wordTrace_append hprefix tailTrace_1183842
  have hstable : (prefixWord ++ tailWord_1183842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183842).length < 2 ^ (prefixWord ++ tailWord_1183842).sum := by decide
  have hdescent : baseEnd_1183842 < baseStart_1183842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183847 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1183847 : Nat := 118140960795 + 1183847 * 2 ^ 59
def prefixEnd_1183847 : Nat := 4983230072969 + 3 ^ 40 * 1183847 * 2
def baseEnd_1183847 : Nat := 405255021588889951245395

theorem tailTrace_1183847 : CollatzResearch.WordTrace tailWord_1183847 prefixEnd_1183847 405255021588889951245395 := by
  unfold tailWord_1183847
  simp only [CollatzResearch.WordTrace]
  refine ⟨43178447342131978815941795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28785631561421319210627863 43178447342131978815941795)
  ·
    refine ⟨64767671013197968223912693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43178447342131978815941795 64767671013197968223912693)
    ·
      refine ⟨6071969157487309520991815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64767671013197968223912693 6071969157487309520991815)
      ·
        refine ⟨9107953736230964281487723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6071969157487309520991815 9107953736230964281487723)
        ·
          refine ⟨13661930604346446422231585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9107953736230964281487723 13661930604346446422231585)
          ·
            refine ⟨10246447953259834816673689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13661930604346446422231585 10246447953259834816673689)
            ·
              refine ⟨7684835964944876112505267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10246447953259834816673689 7684835964944876112505267)
              ·
                refine ⟨11527253947417314168757901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7684835964944876112505267 11527253947417314168757901)
                ·
                  refine ⟨4322720230281492813284213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11527253947417314168757901 4322720230281492813284213)
                  ·
                    refine ⟨405255021588889951245395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4322720230281492813284213 405255021588889951245395)
                    ·
                      rfl

theorem cell22_1183847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1183847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183847 prefixEnd_1183847 := by exact prefixLift 1183847
  have htrace : WordTrace (prefixWord ++ tailWord_1183847) baseStart_1183847 baseEnd_1183847 := by
    simpa [prefixWord, tailWord_1183847, baseEnd_1183847] using wordTrace_append hprefix tailTrace_1183847
  have hstable : (prefixWord ++ tailWord_1183847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183847).length < 2 ^ (prefixWord ++ tailWord_1183847).sum := by decide
  have hdescent : baseEnd_1183847 < baseStart_1183847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183864 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_1183864 : Nat := 118140960795 + 1183864 * 2 ^ 59
def prefixEnd_1183864 : Nat := 4983230072969 + 3 ^ 40 * 1183864 * 2
def baseEnd_1183864 : Nat := 405260841036307573570343

theorem tailTrace_1183864 : CollatzResearch.WordTrace tailWord_1183864 prefixEnd_1183864 405260841036307573570343 := by
  unfold tailWord_1183864
  simp only [CollatzResearch.WordTrace]
  refine ⟨21589533691535195359655323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28786044922046927146207097 21589533691535195359655323)
  ·
    refine ⟨32384300537302793039482985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21589533691535195359655323 32384300537302793039482985)
    ·
      refine ⟨24288225402977094779612239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32384300537302793039482985 24288225402977094779612239)
      ·
        refine ⟨36432338104465642169418359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24288225402977094779612239 36432338104465642169418359)
        ·
          refine ⟨54648507156698463254127539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36432338104465642169418359 54648507156698463254127539)
          ·
            refine ⟨81972760735047694881191309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54648507156698463254127539 81972760735047694881191309)
            ·
              refine ⟨30739785275642885580446741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81972760735047694881191309 30739785275642885580446741)
              ·
                refine ⟨1440927434795760261583441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30739785275642885580446741 1440927434795760261583441)
                ·
                  refine ⟨1080695576096820196187581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440927434795760261583441 1080695576096820196187581)
                  ·
                    refine ⟨405260841036307573570343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080695576096820196187581 405260841036307573570343)
                    ·
                      rfl

theorem cell22_1183864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_1183864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183864 prefixEnd_1183864 := by exact prefixLift 1183864
  have htrace : WordTrace (prefixWord ++ tailWord_1183864) baseStart_1183864 baseEnd_1183864 := by
    simpa [prefixWord, tailWord_1183864, baseEnd_1183864] using wordTrace_append hprefix tailTrace_1183864
  have hstable : (prefixWord ++ tailWord_1183864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183864).length < 2 ^ (prefixWord ++ tailWord_1183864).sum := by decide
  have hdescent : baseEnd_1183864 < baseStart_1183864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183877 : List Nat := [1, 3, 1, 1, 5, 1, 1, 9]
def baseStart_1183877 : Nat := 118140960795 + 1183877 * 2 ^ 59
def prefixEnd_1183877 : Nat := 4983230072969 + 3 ^ 40 * 1183877 * 2
def baseEnd_1183877 : Nat := 45029476800219985888367

theorem tailTrace_1183877 : CollatzResearch.WordTrace tailWord_1183877 prefixEnd_1183877 45029476800219985888367 := by
  unfold tailWord_1183877
  simp only [CollatzResearch.WordTrace]
  refine ⟨43179541532023293939533885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28786361021348862626355923 43179541532023293939533885)
  ·
    refine ⟨16192328074508735227325207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43179541532023293939533885 16192328074508735227325207)
    ·
      refine ⟨24288492111763102840987811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16192328074508735227325207 24288492111763102840987811)
      ·
        refine ⟨36432738167644654261481717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24288492111763102840987811 36432738167644654261481717)
        ·
          refine ⟨3415569203216686337013911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36432738167644654261481717 3415569203216686337013911)
          ·
            refine ⟨5123353804825029505520867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415569203216686337013911 5123353804825029505520867)
            ·
              refine ⟨7685030707237544258281301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123353804825029505520867 7685030707237544258281301)
              ·
                refine ⟨45029476800219985888367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7685030707237544258281301 45029476800219985888367)
                ·
                  rfl

theorem cell22_1183877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 9].length) (baseStart_1183877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183877 prefixEnd_1183877 := by exact prefixLift 1183877
  have htrace : WordTrace (prefixWord ++ tailWord_1183877) baseStart_1183877 baseEnd_1183877 := by
    simpa [prefixWord, tailWord_1183877, baseEnd_1183877] using wordTrace_append hprefix tailTrace_1183877
  have hstable : (prefixWord ++ tailWord_1183877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183877).length < 2 ^ (prefixWord ++ tailWord_1183877).sum := by decide
  have hdescent : baseEnd_1183877 < baseStart_1183877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183896 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1183896 : Nat := 118140960795 + 1183896 * 2 ^ 59
def prefixEnd_1183896 : Nat := 4983230072969 + 3 ^ 40 * 1183896 * 2
def baseEnd_1183896 : Nat := 405271795290270156770245

theorem tailTrace_1183896 : CollatzResearch.WordTrace tailWord_1183896 prefixEnd_1183896 405271795290270156770245 := by
  unfold tailWord_1183896
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590117259477230092237771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28786823012636306789650361 21590117259477230092237771)
  ·
    refine ⟨32385175889215845138356657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21590117259477230092237771 32385175889215845138356657)
    ·
      refine ⟨24288881916911883853767493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32385175889215845138356657 24288881916911883853767493)
      ·
        refine ⟨4554165359420978222581405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24288881916911883853767493 4554165359420978222581405)
        ·
          refine ⟨1707812009782866833468027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4554165359420978222581405 1707812009782866833468027)
          ·
            refine ⟨2561718014674300250202041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707812009782866833468027 2561718014674300250202041)
            ·
              refine ⟨1921288511005725187651531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561718014674300250202041 1921288511005725187651531)
              ·
                refine ⟨2881932766508587781477297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921288511005725187651531 2881932766508587781477297)
                ·
                  refine ⟨2161449574881440836107973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881932766508587781477297 2161449574881440836107973)
                  ·
                    refine ⟨405271795290270156770245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161449574881440836107973 405271795290270156770245)
                    ·
                      rfl

theorem cell22_1183896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1183896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183896 prefixEnd_1183896 := by exact prefixLift 1183896
  have htrace : WordTrace (prefixWord ++ tailWord_1183896) baseStart_1183896 baseEnd_1183896 := by
    simpa [prefixWord, tailWord_1183896, baseEnd_1183896] using wordTrace_append hprefix tailTrace_1183896
  have hstable : (prefixWord ++ tailWord_1183896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183896).length < 2 ^ (prefixWord ++ tailWord_1183896).sum := by decide
  have hdescent : baseEnd_1183896 < baseStart_1183896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183967 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 10]
def baseStart_1183967 : Nat := 118140960795 + 1183967 * 2 ^ 59
def prefixEnd_1183967 : Nat := 4983230072969 + 3 ^ 40 * 1183967 * 2
def baseEnd_1183967 : Nat := 135098700013749879415009

theorem tailTrace_1183967 : CollatzResearch.WordTrace tailWord_1183967 prefixEnd_1183967 135098700013749879415009 := by
  unfold tailWord_1183967
  simp only [CollatzResearch.WordTrace]
  refine ⟨43182824101697239310310155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28788549401131492873540103 43182824101697239310310155)
  ·
    refine ⟨64774236152545858965465233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43182824101697239310310155 64774236152545858965465233)
    ·
      refine ⟨48580677114409394224098925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64774236152545858965465233 48580677114409394224098925)
      ·
        refine ⟨18217753917903522834037097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48580677114409394224098925 18217753917903522834037097)
        ·
          refine ⟨13663315438427642125527823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18217753917903522834037097 13663315438427642125527823)
          ·
            refine ⟨20494973157641463188291735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13663315438427642125527823 20494973157641463188291735)
            ·
              refine ⟨30742459736462194782437603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20494973157641463188291735 30742459736462194782437603)
              ·
                refine ⟨46113689604693292173656405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30742459736462194782437603 46113689604693292173656405)
                ·
                  refine ⟨135098700013749879415009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46113689604693292173656405 135098700013749879415009)
                  ·
                    rfl

theorem cell22_1183967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_1183967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1183967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1183967 prefixEnd_1183967 := by exact prefixLift 1183967
  have htrace : WordTrace (prefixWord ++ tailWord_1183967) baseStart_1183967 baseEnd_1183967 := by
    simpa [prefixWord, tailWord_1183967, baseEnd_1183967] using wordTrace_append hprefix tailTrace_1183967
  have hstable : (prefixWord ++ tailWord_1183967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183967).length < 2 ^ (prefixWord ++ tailWord_1183967).sum := by decide
  have hdescent : baseEnd_1183967 < baseStart_1183967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184014 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1184014 : Nat := 118140960795 + 1184014 * 2 ^ 59
def prefixEnd_1184014 : Nat := 4983230072969 + 3 ^ 40 * 1184014 * 2
def baseEnd_1184014 : Nat := 405312189101757182319883

theorem tailTrace_1184014 : CollatzResearch.WordTrace tailWord_1184014 prefixEnd_1184014 405312189101757182319883 := by
  unfold tailWord_1184014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398067291565870792158887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28789692221684644224847397 5398067291565870792158887)
  ·
    refine ⟨8097100937348806188238331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5398067291565870792158887 8097100937348806188238331)
    ·
      refine ⟨12145651406023209282357497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097100937348806188238331 12145651406023209282357497)
      ·
        refine ⟨9109238554517406961768123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12145651406023209282357497 9109238554517406961768123)
        ·
          refine ⟨13663857831776110442652185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109238554517406961768123 13663857831776110442652185)
          ·
            refine ⟨10247893373832082831989139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13663857831776110442652185 10247893373832082831989139)
            ·
              refine ⟨15371840060748124247983709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10247893373832082831989139 15371840060748124247983709)
              ·
                refine ⟨5764440022780546592993891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15371840060748124247983709 5764440022780546592993891)
                ·
                  refine ⟨8646660034170819889490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764440022780546592993891 8646660034170819889490837)
                  ·
                    refine ⟨405312189101757182319883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8646660034170819889490837 405312189101757182319883)
                    ·
                      rfl

theorem cell22_1184014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1184014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184014 prefixEnd_1184014 := by exact prefixLift 1184014
  have htrace : WordTrace (prefixWord ++ tailWord_1184014) baseStart_1184014 baseEnd_1184014 := by
    simpa [prefixWord, tailWord_1184014, baseEnd_1184014] using wordTrace_append hprefix tailTrace_1184014
  have hstable : (prefixWord ++ tailWord_1184014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184014).length < 2 ^ (prefixWord ++ tailWord_1184014).sum := by decide
  have hdescent : baseEnd_1184014 < baseStart_1184014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184031 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_1184031 : Nat := 118140960795 + 1184031 * 2 ^ 59
def prefixEnd_1184031 : Nat := 4983230072969 + 3 ^ 40 * 1184031 * 2
def baseEnd_1184031 : Nat := 405318008549174804644831

theorem tailTrace_1184031 : CollatzResearch.WordTrace tailWord_1184031 prefixEnd_1184031 405318008549174804644831 := by
  unfold tailWord_1184031
  simp only [CollatzResearch.WordTrace]
  refine ⟨43185158373465378240639947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28790105582310252160426631 43185158373465378240639947)
  ·
    refine ⟨64777737560198067360959921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43185158373465378240639947 64777737560198067360959921)
    ·
      refine ⟨48583303170148550520719941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64777737560198067360959921 48583303170148550520719941)
      ·
        refine ⟨9109369344402853222634989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48583303170148550520719941 9109369344402853222634989)
        ·
          refine ⟨3416013504151069958488121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9109369344402853222634989 3416013504151069958488121)
          ·
            refine ⟨2562010128113302468866091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416013504151069958488121 2562010128113302468866091)
            ·
              refine ⟨3843015192169953703299137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562010128113302468866091 3843015192169953703299137)
              ·
                refine ⟨2882261394127465277474353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3843015192169953703299137 2882261394127465277474353)
                ·
                  refine ⟨2161696045595598958105765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2882261394127465277474353 2161696045595598958105765)
                  ·
                    refine ⟨405318008549174804644831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161696045595598958105765 405318008549174804644831)
                    ·
                      rfl

theorem cell22_1184031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_1184031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184031 prefixEnd_1184031 := by exact prefixLift 1184031
  have htrace : WordTrace (prefixWord ++ tailWord_1184031) baseStart_1184031 baseEnd_1184031 := by
    simpa [prefixWord, tailWord_1184031, baseEnd_1184031] using wordTrace_append hprefix tailTrace_1184031
  have hstable : (prefixWord ++ tailWord_1184031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184031).length < 2 ^ (prefixWord ++ tailWord_1184031).sum := by decide
  have hdescent : baseEnd_1184031 < baseStart_1184031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184089 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1184089 : Nat := 118140960795 + 1184089 * 2 ^ 59
def prefixEnd_1184089 : Nat := 4983230072969 + 3 ^ 40 * 1184089 * 2
def baseEnd_1184089 : Nat := 405337863134481986694653

theorem tailTrace_1184089 : CollatzResearch.WordTrace tailWord_1184089 prefixEnd_1184089 405337863134481986694653 := by
  unfold tailWord_1184089
  simp only [CollatzResearch.WordTrace]
  refine ⟨43187273807255254146251321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28791515871503502764167547 43187273807255254146251321)
  ·
    refine ⟨32390455355441440609688491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43187273807255254146251321 32390455355441440609688491)
    ·
      refine ⟨48585683033162160914532737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32390455355441440609688491 48585683033162160914532737)
      ·
        refine ⟨36439262274871620685899553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48585683033162160914532737 36439262274871620685899553)
        ·
          refine ⟨27329446706153715514424665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36439262274871620685899553 27329446706153715514424665)
          ·
            refine ⟨20497085029615286635818499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27329446706153715514424665 20497085029615286635818499)
            ·
              refine ⟨30745627544422929953727749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20497085029615286635818499 30745627544422929953727749)
              ·
                refine ⟨5764805164579299366323953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30745627544422929953727749 5764805164579299366323953)
                ·
                  refine ⟨4323603873434474524742965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5764805164579299366323953 4323603873434474524742965)
                  ·
                    refine ⟨405337863134481986694653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4323603873434474524742965 405337863134481986694653)
                    ·
                      rfl

theorem cell22_1184089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1184089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184089 prefixEnd_1184089 := by exact prefixLift 1184089
  have htrace : WordTrace (prefixWord ++ tailWord_1184089) baseStart_1184089 baseEnd_1184089 := by
    simpa [prefixWord, tailWord_1184089, baseEnd_1184089] using wordTrace_append hprefix tailTrace_1184089
  have hstable : (prefixWord ++ tailWord_1184089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184089).length < 2 ^ (prefixWord ++ tailWord_1184089).sum := by decide
  have hdescent : baseEnd_1184089 < baseStart_1184089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184095 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 1, 3]
def baseStart_1184095 : Nat := 118140960795 + 1184095 * 2 ^ 59
def prefixEnd_1184095 : Nat := 4983230072969 + 3 ^ 40 * 1184095 * 2
def baseEnd_1184095 : Nat := 405339917057099971044635

theorem tailTrace_1184095 : CollatzResearch.WordTrace tailWord_1184095 prefixEnd_1184095 405339917057099971044635 := by
  unfold tailWord_1184095
  simp only [CollatzResearch.WordTrace]
  refine ⟨43187492645233517170969739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28791661763489011447313159 43187492645233517170969739)
  ·
    refine ⟨64781238967850275756454609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43187492645233517170969739 64781238967850275756454609)
    ·
      refine ⟨48585929225887706817340957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64781238967850275756454609 48585929225887706817340957)
      ·
        refine ⟨18219723459707890056502859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48585929225887706817340957 18219723459707890056502859)
        ·
          refine ⟨27329585189561835084754289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18219723459707890056502859 27329585189561835084754289)
          ·
            refine ⟨20497188892171376313565717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27329585189561835084754289 20497188892171376313565717)
            ·
              refine ⟨960805729320533264698393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20497188892171376313565717 960805729320533264698393)
              ·
                refine ⟨720604296990399948523795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960805729320533264698393 720604296990399948523795)
                ·
                  refine ⟨1080906445485599922785693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720604296990399948523795 1080906445485599922785693)
                  ·
                    refine ⟨405339917057099971044635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1080906445485599922785693 405339917057099971044635)
                    ·
                      rfl

theorem cell22_1184095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_1184095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184095 prefixEnd_1184095 := by exact prefixLift 1184095
  have htrace : WordTrace (prefixWord ++ tailWord_1184095) baseStart_1184095 baseEnd_1184095 := by
    simpa [prefixWord, tailWord_1184095, baseEnd_1184095] using wordTrace_append hprefix tailTrace_1184095
  have hstable : (prefixWord ++ tailWord_1184095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184095).length < 2 ^ (prefixWord ++ tailWord_1184095).sum := by decide
  have hdescent : baseEnd_1184095 < baseStart_1184095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184106 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1184106 : Nat := 118140960795 + 1184106 * 2 ^ 59
def prefixEnd_1184106 : Nat := 4983230072969 + 3 ^ 40 * 1184106 * 2
def baseEnd_1184106 : Nat := 405343682581899609019601

theorem tailTrace_1184106 : CollatzResearch.WordTrace tailWord_1184106 prefixEnd_1184106 405343682581899609019601 := by
  unfold tailWord_1184106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796973462048416512405043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28791929232129110699746781 10796973462048416512405043)
  ·
    refine ⟨16195460193072624768607565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10796973462048416512405043 16195460193072624768607565)
    ·
      refine ⟨6073297572402234288227837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16195460193072624768607565 6073297572402234288227837)
      ·
        refine ⟨2277486589650837858085439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6073297572402234288227837 2277486589650837858085439)
        ·
          refine ⟨3416229884476256787128159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277486589650837858085439 3416229884476256787128159)
          ·
            refine ⟨5124344826714385180692239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416229884476256787128159 5124344826714385180692239)
            ·
              refine ⟨7686517240071577771038359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124344826714385180692239 7686517240071577771038359)
              ·
                refine ⟨11529775860107366656557539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7686517240071577771038359 11529775860107366656557539)
                ·
                  refine ⟨17294663790161049984836309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11529775860107366656557539 17294663790161049984836309)
                  ·
                    refine ⟨405343682581899609019601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17294663790161049984836309 405343682581899609019601)
                    ·
                      rfl

theorem cell22_1184106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1184106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184106 prefixEnd_1184106 := by exact prefixLift 1184106
  have htrace : WordTrace (prefixWord ++ tailWord_1184106) baseStart_1184106 baseEnd_1184106 := by
    simpa [prefixWord, tailWord_1184106, baseEnd_1184106] using wordTrace_append hprefix tailTrace_1184106
  have hstable : (prefixWord ++ tailWord_1184106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184106).length < 2 ^ (prefixWord ++ tailWord_1184106).sum := by decide
  have hdescent : baseEnd_1184106 < baseStart_1184106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184121 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_1184121 : Nat := 118140960795 + 1184121 * 2 ^ 59
def prefixEnd_1184121 : Nat := 4983230072969 + 3 ^ 40 * 1184121 * 2
def baseEnd_1184121 : Nat := 405348817388444569894555

theorem tailTrace_1184121 : CollatzResearch.WordTrace tailWord_1184121 prefixEnd_1184121 405348817388444569894555 := by
  unfold tailWord_1184121
  simp only [CollatzResearch.WordTrace]
  refine ⟨43188440943139323611416217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28792293962092882407610811 43188440943139323611416217)
  ·
    refine ⟨32391330707354492708562163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43188440943139323611416217 32391330707354492708562163)
    ·
      refine ⟨48586996061031739062843245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32391330707354492708562163 48586996061031739062843245)
      ·
        refine ⟨18220123522886902148566217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48586996061031739062843245 18220123522886902148566217)
        ·
          refine ⟨13665092642165176611424663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18220123522886902148566217 13665092642165176611424663)
          ·
            refine ⟨20497638963247764917136995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13665092642165176611424663 20497638963247764917136995)
            ·
              refine ⟨30746458444871647375705493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20497638963247764917136995 30746458444871647375705493)
              ·
                refine ⟨1441240239603358470736195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30746458444871647375705493 1441240239603358470736195)
                ·
                  refine ⟨2161860359405037706104293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441240239603358470736195 2161860359405037706104293)
                  ·
                    refine ⟨405348817388444569894555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161860359405037706104293 405348817388444569894555)
                    ·
                      rfl

theorem cell22_1184121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_1184121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184121 prefixEnd_1184121 := by exact prefixLift 1184121
  have htrace : WordTrace (prefixWord ++ tailWord_1184121) baseStart_1184121 baseEnd_1184121 := by
    simpa [prefixWord, tailWord_1184121, baseEnd_1184121] using wordTrace_append hprefix tailTrace_1184121
  have hstable : (prefixWord ++ tailWord_1184121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184121).length < 2 ^ (prefixWord ++ tailWord_1184121).sum := by decide
  have hdescent : baseEnd_1184121 < baseStart_1184121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184260 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1184260 : Nat := 118140960795 + 1184260 * 2 ^ 59
def prefixEnd_1184260 : Nat := 4983230072969 + 3 ^ 40 * 1184260 * 2
def baseEnd_1184260 : Nat := 135132133309698180223043

theorem tailTrace_1184260 : CollatzResearch.WordTrace tailWord_1184260 prefixEnd_1184260 135132133309698180223043 := by
  unfold tailWord_1184260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21596755344817875175363117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28795673793090500233817489 21596755344817875175363117)
  ·
    refine ⟨8098783254306703190761169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21596755344817875175363117 8098783254306703190761169)
    ·
      refine ⟨6074087440730027393070877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8098783254306703190761169 6074087440730027393070877)
      ·
        refine ⟨2277782790273760272401579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6074087440730027393070877 2277782790273760272401579)
        ·
          refine ⟨3416674185410640408602369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277782790273760272401579 3416674185410640408602369)
          ·
            refine ⟨2562505639057980306451777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416674185410640408602369 2562505639057980306451777)
            ·
              refine ⟨1921879229293485229838833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562505639057980306451777 1921879229293485229838833)
              ·
                refine ⟨1441409421970113922379125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921879229293485229838833 1441409421970113922379125)
                ·
                  refine ⟨135132133309698180223043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1441409421970113922379125 135132133309698180223043)
                  ·
                    rfl

theorem cell22_1184260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1184260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184260 prefixEnd_1184260 := by exact prefixLift 1184260
  have htrace : WordTrace (prefixWord ++ tailWord_1184260) baseStart_1184260 baseEnd_1184260 := by
    simpa [prefixWord, tailWord_1184260, baseEnd_1184260] using wordTrace_append hprefix tailTrace_1184260
  have hstable : (prefixWord ++ tailWord_1184260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184260).length < 2 ^ (prefixWord ++ tailWord_1184260).sum := by decide
  have hdescent : baseEnd_1184260 < baseStart_1184260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184262 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1184262 : Nat := 118140960795 + 1184262 * 2 ^ 59
def prefixEnd_1184262 : Nat := 4983230072969 + 3 ^ 40 * 1184262 * 2
def baseEnd_1184262 : Nat := 405397084569967202119123

theorem tailTrace_1184262 : CollatzResearch.WordTrace tailWord_1184262 prefixEnd_1184262 405397084569967202119123 := by
  unfold tailWord_1184262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349799488613390771634345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28795722423752336461532693 1349799488613390771634345)
  ·
    refine ⟨1012349616460043078725759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1349799488613390771634345 1012349616460043078725759)
    ·
      refine ⟨1518524424690064618088639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012349616460043078725759 1518524424690064618088639)
      ·
        refine ⟨2277786637035096927132959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518524424690064618088639 2277786637035096927132959)
        ·
          refine ⟨3416679955552645390699439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277786637035096927132959 3416679955552645390699439)
          ·
            refine ⟨5125019933328968086049159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416679955552645390699439 5125019933328968086049159)
            ·
              refine ⟨7687529899993452129073739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125019933328968086049159 7687529899993452129073739)
              ·
                refine ⟨11531294849990178193610609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687529899993452129073739 11531294849990178193610609)
                ·
                  refine ⟨8648471137492633645207957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11531294849990178193610609 8648471137492633645207957)
                  ·
                    refine ⟨405397084569967202119123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8648471137492633645207957 405397084569967202119123)
                    ·
                      rfl

theorem cell22_1184262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1184262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184262 prefixEnd_1184262 := by exact prefixLift 1184262
  have htrace : WordTrace (prefixWord ++ tailWord_1184262) baseStart_1184262 baseEnd_1184262 := by
    simpa [prefixWord, tailWord_1184262, baseEnd_1184262] using wordTrace_append hprefix tailTrace_1184262
  have hstable : (prefixWord ++ tailWord_1184262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184262).length < 2 ^ (prefixWord ++ tailWord_1184262).sum := by decide
  have hdescent : baseEnd_1184262 < baseStart_1184262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184320 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_1184320 : Nat := 118140960795 + 1184320 * 2 ^ 59
def prefixEnd_1184320 : Nat := 4983230072969 + 3 ^ 40 * 1184320 * 2
def baseEnd_1184320 : Nat := 405416939155274384168945

theorem tailTrace_1184320 : CollatzResearch.WordTrace tailWord_1184320 prefixEnd_1184320 405416939155274384168945 := by
  unfold tailWord_1184320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21597849534709190298955207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28797132712945587065273609 21597849534709190298955207)
  ·
    refine ⟨32396774302063785448432811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21597849534709190298955207 32396774302063785448432811)
    ·
      refine ⟨48595161453095678172649217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32396774302063785448432811 48595161453095678172649217)
      ·
        refine ⟨36446371089821758629486913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48595161453095678172649217 36446371089821758629486913)
        ·
          refine ⟨27334778317366318972115185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36446371089821758629486913 27334778317366318972115185)
          ·
            refine ⟨20501083738024739229086389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27334778317366318972115185 20501083738024739229086389)
            ·
              refine ⟨1921976600439819302726849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20501083738024739229086389 1921976600439819302726849)
              ·
                refine ⟨1441482450329864477045137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921976600439819302726849 1441482450329864477045137)
                ·
                  refine ⟨1081111837747398357783853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441482450329864477045137 1081111837747398357783853)
                  ·
                    refine ⟨405416939155274384168945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081111837747398357783853 405416939155274384168945)
                    ·
                      rfl

theorem cell22_1184320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_1184320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184320 prefixEnd_1184320 := by exact prefixLift 1184320
  have htrace : WordTrace (prefixWord ++ tailWord_1184320) baseStart_1184320 baseEnd_1184320 := by
    simpa [prefixWord, tailWord_1184320, baseEnd_1184320] using wordTrace_append hprefix tailTrace_1184320
  have hstable : (prefixWord ++ tailWord_1184320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184320).length < 2 ^ (prefixWord ++ tailWord_1184320).sum := by decide
  have hdescent : baseEnd_1184320 < baseStart_1184320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184337 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_1184337 : Nat := 118140960795 + 1184337 * 2 ^ 59
def prefixEnd_1184337 : Nat := 4983230072969 + 3 ^ 40 * 1184337 * 2
def baseEnd_1184337 : Nat := 405422758602692006493893

theorem tailTrace_1184337 : CollatzResearch.WordTrace tailWord_1184337 prefixEnd_1184337 405422758602692006493893 := by
  unfold tailWord_1184337
  simp only [CollatzResearch.WordTrace]
  refine ⟨43196319110356792501279265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28797546073571195000852843 43196319110356792501279265)
  ·
    refine ⟨32397239332767594375959449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43196319110356792501279265 32397239332767594375959449)
    ·
      refine ⟨24297929499575695781969587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32397239332767594375959449 24297929499575695781969587)
      ·
        refine ⟨36446894249363543672954381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24297929499575695781969587 36446894249363543672954381)
        ·
          refine ⟨13667585343511328877357893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36446894249363543672954381 13667585343511328877357893)
          ·
            refine ⟨2562672251908374164504605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13667585343511328877357893 2562672251908374164504605)
            ·
              refine ⟨961002094465640311689227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2562672251908374164504605 961002094465640311689227)
              ·
                refine ⟨1441503141698460467533841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961002094465640311689227 1441503141698460467533841)
                ·
                  refine ⟨1081127356273845350650381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441503141698460467533841 1081127356273845350650381)
                  ·
                    refine ⟨405422758602692006493893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081127356273845350650381 405422758602692006493893)
                    ·
                      rfl

theorem cell22_1184337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_1184337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184337 prefixEnd_1184337 := by exact prefixLift 1184337
  have htrace : WordTrace (prefixWord ++ tailWord_1184337) baseStart_1184337 baseEnd_1184337 := by
    simpa [prefixWord, tailWord_1184337, baseEnd_1184337] using wordTrace_append hprefix tailTrace_1184337
  have hstable : (prefixWord ++ tailWord_1184337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184337).length < 2 ^ (prefixWord ++ tailWord_1184337).sum := by decide
  have hdescent : baseEnd_1184337 < baseStart_1184337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184433 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 1, 3]
def baseStart_1184433 : Nat := 118140960795 + 1184433 * 2 ^ 59
def prefixEnd_1184433 : Nat := 4983230072969 + 3 ^ 40 * 1184433 * 2
def baseEnd_1184433 : Nat := 405455621364579756093599

theorem tailTrace_1184433 : CollatzResearch.WordTrace tailWord_1184433 prefixEnd_1184433 405455621364579756093599 := by
  unfold tailWord_1184433
  simp only [CollatzResearch.WordTrace]
  refine ⟨43199820518009000896773953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28799880345339333931182635 43199820518009000896773953)
  ·
    refine ⟨32399865388506750672580465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43199820518009000896773953 32399865388506750672580465)
    ·
      refine ⟨24299899041380063004435349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32399865388506750672580465 24299899041380063004435349)
      ·
        refine ⟨1139057767564690453332907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24299899041380063004435349 1139057767564690453332907)
        ·
          refine ⟨1708586651347035679999361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139057767564690453332907 1708586651347035679999361)
          ·
            refine ⟨1281439988510276759999521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708586651347035679999361 1281439988510276759999521)
            ·
              refine ⟨961079991382707569999641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281439988510276759999521 961079991382707569999641)
              ·
                refine ⟨720809993537030677499731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961079991382707569999641 720809993537030677499731)
                ·
                  refine ⟨1081214990305546016249597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720809993537030677499731 1081214990305546016249597)
                  ·
                    refine ⟨405455621364579756093599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081214990305546016249597 405455621364579756093599)
                    ·
                      rfl

theorem cell22_1184433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_1184433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184433 prefixEnd_1184433 := by exact prefixLift 1184433
  have htrace : WordTrace (prefixWord ++ tailWord_1184433) baseStart_1184433 baseEnd_1184433 := by
    simpa [prefixWord, tailWord_1184433, baseEnd_1184433] using wordTrace_append hprefix tailTrace_1184433
  have hstable : (prefixWord ++ tailWord_1184433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184433).length < 2 ^ (prefixWord ++ tailWord_1184433).sum := by decide
  have hdescent : baseEnd_1184433 < baseStart_1184433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184476 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1184476 : Nat := 118140960795 + 1184476 * 2 ^ 59
def prefixEnd_1184476 : Nat := 4983230072969 + 3 ^ 40 * 1184476 * 2
def baseEnd_1184476 : Nat := 405470341143341977268467

theorem tailTrace_1184476 : CollatzResearch.WordTrace tailWord_1184476 prefixEnd_1184476 405470341143341977268467 := by
  unfold tailWord_1184476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21600694428426609620294641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28800925904568812827059521 21600694428426609620294641)
  ·
    refine ⟨16200520821319957215220981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21600694428426609620294641 16200520821319957215220981)
    ·
      refine ⟨1518798826998745988926967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16200520821319957215220981 1518798826998745988926967)
      ·
        refine ⟨2278198240498118983390451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518798826998745988926967 2278198240498118983390451)
        ·
          refine ⟨3417297360747178475085677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278198240498118983390451 3417297360747178475085677)
          ·
            refine ⟨1281486510280191928157129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3417297360747178475085677 1281486510280191928157129)
            ·
              refine ⟨961114882710143946117847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281486510280191928157129 961114882710143946117847)
              ·
                refine ⟨1441672324065215919176771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961114882710143946117847 1441672324065215919176771)
                ·
                  refine ⟨2162508486097823878765157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441672324065215919176771 2162508486097823878765157)
                  ·
                    refine ⟨405470341143341977268467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2162508486097823878765157 405470341143341977268467)
                    ·
                      rfl

theorem cell22_1184476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1184476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184476 prefixEnd_1184476 := by exact prefixLift 1184476
  have htrace : WordTrace (prefixWord ++ tailWord_1184476) baseStart_1184476 baseEnd_1184476 := by
    simpa [prefixWord, tailWord_1184476, baseEnd_1184476] using wordTrace_append hprefix tailTrace_1184476
  have hstable : (prefixWord ++ tailWord_1184476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184476).length < 2 ^ (prefixWord ++ tailWord_1184476).sum := by decide
  have hdescent : baseEnd_1184476 < baseStart_1184476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184564 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1184564 : Nat := 118140960795 + 1184564 * 2 ^ 59
def prefixEnd_1184564 : Nat := 4983230072969 + 3 ^ 40 * 1184564 * 2
def baseEnd_1184564 : Nat := 135166821780579693689399

theorem tailTrace_1184564 : CollatzResearch.WordTrace tailWord_1184564 prefixEnd_1184564 135166821780579693689399 := by
  unfold tailWord_1184564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21602299240267205134896373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28803065653689606846528497 21602299240267205134896373)
  ·
    refine ⟨2025215553775050481396535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21602299240267205134896373 2025215553775050481396535)
    ·
      refine ⟨3037823330662575722094803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2025215553775050481396535 3037823330662575722094803)
      ·
        refine ⟨4556734995993863583142205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037823330662575722094803 4556734995993863583142205)
        ·
          refine ⟨1708775623497698843678327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4556734995993863583142205 1708775623497698843678327)
          ·
            refine ⟨2563163435246548265517491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708775623497698843678327 2563163435246548265517491)
            ·
              refine ⟨3844745152869822398276237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563163435246548265517491 3844745152869822398276237)
              ·
                refine ⟨1441779432326183399353589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3844745152869822398276237 1441779432326183399353589)
                ·
                  refine ⟨135166821780579693689399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1441779432326183399353589 135166821780579693689399)
                  ·
                    rfl

theorem cell22_1184564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1184564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184564 prefixEnd_1184564 := by exact prefixLift 1184564
  have htrace : WordTrace (prefixWord ++ tailWord_1184564) baseStart_1184564 baseEnd_1184564 := by
    simpa [prefixWord, tailWord_1184564, baseEnd_1184564] using wordTrace_append hprefix tailTrace_1184564
  have hstable : (prefixWord ++ tailWord_1184564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184564).length < 2 ^ (prefixWord ++ tailWord_1184564).sum := by decide
  have hdescent : baseEnd_1184564 < baseStart_1184564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184594 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_1184594 : Nat := 118140960795 + 1184594 * 2 ^ 59
def prefixEnd_1184594 : Nat := 4983230072969 + 3 ^ 40 * 1184594 * 2
def baseEnd_1184594 : Nat := 405510734954829002818105

theorem tailTrace_1184594 : CollatzResearch.WordTrace tailWord_1184594 prefixEnd_1184594 405510734954829002818105 := by
  unfold tailWord_1184594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801423167606431348346209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28803795113617150262256557 10801423167606431348346209)
  ·
    refine ⟨8101067375704823511259657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10801423167606431348346209 8101067375704823511259657)
    ·
      refine ⟨6075800531778617633444743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101067375704823511259657 6075800531778617633444743)
      ·
        refine ⟨9113700797667926450167115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075800531778617633444743 9113700797667926450167115)
        ·
          refine ⟨13670551196501889675250673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113700797667926450167115 13670551196501889675250673)
          ·
            refine ⟨10252913397376417256438005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13670551196501889675250673 10252913397376417256438005)
            ·
              refine ⟨961210631004039117791063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10252913397376417256438005 961210631004039117791063)
              ·
                refine ⟨1441815946506058676686595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961210631004039117791063 1441815946506058676686595)
                ·
                  refine ⟨2162723919759088015029893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441815946506058676686595 2162723919759088015029893)
                  ·
                    refine ⟨405510734954829002818105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2162723919759088015029893 405510734954829002818105)
                    ·
                      rfl

theorem cell22_1184594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_1184594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184594 prefixEnd_1184594 := by exact prefixLift 1184594
  have htrace : WordTrace (prefixWord ++ tailWord_1184594) baseStart_1184594 baseEnd_1184594 := by
    simpa [prefixWord, tailWord_1184594, baseEnd_1184594] using wordTrace_append hprefix tailTrace_1184594
  have hstable : (prefixWord ++ tailWord_1184594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184594).length < 2 ^ (prefixWord ++ tailWord_1184594).sum := by decide
  have hdescent : baseEnd_1184594 < baseStart_1184594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184658 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1184658 : Nat := 118140960795 + 1184658 * 2 ^ 59
def prefixEnd_1184658 : Nat := 4983230072969 + 3 ^ 40 * 1184658 * 2
def baseEnd_1184658 : Nat := 405532643462754169217909

theorem tailTrace_1184658 : CollatzResearch.WordTrace tailWord_1184658 prefixEnd_1184658 405532643462754169217909 := by
  unfold tailWord_1184658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10802006735548466080928657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28805351294795909549143085 10802006735548466080928657)
  ·
    refine ⟨8101505051661349560696493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10802006735548466080928657 8101505051661349560696493)
    ·
      refine ⟨3038064394373006085261185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8101505051661349560696493 3038064394373006085261185)
      ·
        refine ⟨2278548295779754563945889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3038064394373006085261185 2278548295779754563945889)
        ·
          refine ⟨1708911221834815922959417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2278548295779754563945889 1708911221834815922959417)
          ·
            refine ⟨1281683416376111942219563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708911221834815922959417 1281683416376111942219563)
            ·
              refine ⟨1922525124564167913329345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281683416376111942219563 1922525124564167913329345)
              ·
                refine ⟨1441893843423125934997009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922525124564167913329345 1441893843423125934997009)
                ·
                  refine ⟨1081420382567344451247757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441893843423125934997009 1081420382567344451247757)
                  ·
                    refine ⟨405532643462754169217909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081420382567344451247757 405532643462754169217909)
                    ·
                      rfl

theorem cell22_1184658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1184658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184658 prefixEnd_1184658 := by exact prefixLift 1184658
  have htrace : WordTrace (prefixWord ++ tailWord_1184658) baseStart_1184658 baseEnd_1184658 := by
    simpa [prefixWord, tailWord_1184658, baseEnd_1184658] using wordTrace_append hprefix tailTrace_1184658
  have hstable : (prefixWord ++ tailWord_1184658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184658).length < 2 ^ (prefixWord ++ tailWord_1184658).sum := by decide
  have hdescent : baseEnd_1184658 < baseStart_1184658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184669 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1184669 : Nat := 118140960795 + 1184669 * 2 ^ 59
def prefixEnd_1184669 : Nat := 4983230072969 + 3 ^ 40 * 1184669 * 2
def baseEnd_1184669 : Nat := 405536408987553807192875

theorem tailTrace_1184669 : CollatzResearch.WordTrace tailWord_1184669 prefixEnd_1184669 405536408987553807192875 := by
  unfold tailWord_1184669
  simp only [CollatzResearch.WordTrace]
  refine ⟨43208428145154013202365061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28805618763436008801576707 43208428145154013202365061)
  ·
    refine ⟨8101580277216377475443449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43208428145154013202365061 8101580277216377475443449)
    ·
      refine ⟨6076185207912283106582587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101580277216377475443449 6076185207912283106582587)
      ·
        refine ⟨9114277811868424659873881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076185207912283106582587 9114277811868424659873881)
        ·
          refine ⟨6835708358901318494905411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9114277811868424659873881 6835708358901318494905411)
          ·
            refine ⟨10253562538351977742358117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6835708358901318494905411 10253562538351977742358117)
            ·
              refine ⟨1922542975940995826692147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10253562538351977742358117 1922542975940995826692147)
              ·
                refine ⟨2883814463911493740038221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922542975940995826692147 2883814463911493740038221)
                ·
                  refine ⟨1081430423966810152514333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2883814463911493740038221 1081430423966810152514333)
                  ·
                    refine ⟨405536408987553807192875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081430423966810152514333 405536408987553807192875)
                    ·
                      rfl

theorem cell22_1184669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1184669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184669 prefixEnd_1184669 := by exact prefixLift 1184669
  have htrace : WordTrace (prefixWord ++ tailWord_1184669) baseStart_1184669 baseEnd_1184669 := by
    simpa [prefixWord, tailWord_1184669, baseEnd_1184669] using wordTrace_append hprefix tailTrace_1184669
  have hstable : (prefixWord ++ tailWord_1184669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184669).length < 2 ^ (prefixWord ++ tailWord_1184669).sum := by decide
  have hdescent : baseEnd_1184669 < baseStart_1184669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184746 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1184746 : Nat := 118140960795 + 1184746 * 2 ^ 59
def prefixEnd_1184746 : Nat := 4983230072969 + 3 ^ 40 * 1184746 * 2
def baseEnd_1184746 : Nat := 405562767661151273017639

theorem tailTrace_1184746 : CollatzResearch.WordTrace tailWord_1184746 prefixEnd_1184746 405562767661151273017639 := by
  unfold tailWord_1184746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10802809141468763838229523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28807491043916703568612061 10802809141468763838229523)
  ·
    refine ⟨16204213712203145757344285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10802809141468763838229523 16204213712203145757344285)
    ·
      refine ⟨6076580142076179659004107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16204213712203145757344285 6076580142076179659004107)
      ·
        refine ⟨9114870213114269488506161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076580142076179659004107 9114870213114269488506161)
        ·
          refine ⟨6836152659835702116379621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9114870213114269488506161 6836152659835702116379621)
          ·
            refine ⟨1281778623719194146821179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6836152659835702116379621 1281778623719194146821179)
            ·
              refine ⟨1922667935578791220231769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281778623719194146821179 1922667935578791220231769)
              ·
                refine ⟨1442000951684093415173827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922667935578791220231769 1442000951684093415173827)
                ·
                  refine ⟨2163001427526140122760741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442000951684093415173827 2163001427526140122760741)
                  ·
                    refine ⟨405562767661151273017639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163001427526140122760741 405562767661151273017639)
                    ·
                      rfl

theorem cell22_1184746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1184746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184746 prefixEnd_1184746 := by exact prefixLift 1184746
  have htrace : WordTrace (prefixWord ++ tailWord_1184746) baseStart_1184746 baseEnd_1184746 := by
    simpa [prefixWord, tailWord_1184746, baseEnd_1184746] using wordTrace_append hprefix tailTrace_1184746
  have hstable : (prefixWord ++ tailWord_1184746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184746).length < 2 ^ (prefixWord ++ tailWord_1184746).sum := by decide
  have hdescent : baseEnd_1184746 < baseStart_1184746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184776 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_1184776 : Nat := 118140960795 + 1184776 * 2 ^ 59
def prefixEnd_1184776 : Nat := 4983230072969 + 3 ^ 40 * 1184776 * 2
def baseEnd_1184776 : Nat := 405573037274241194767547

theorem tailTrace_1184776 : CollatzResearch.WordTrace tailWord_1184776 prefixEnd_1184776 405573037274241194767547 := by
  unfold tailWord_1184776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21606165377883185238255091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28808220503844246984340121 21606165377883185238255091)
  ·
    refine ⟨32409248066824777857382637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21606165377883185238255091 32409248066824777857382637)
    ·
      refine ⟨12153468025059291696518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32409248066824777857382637 12153468025059291696518489)
      ·
        refine ⟨9115101018794468772388867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12153468025059291696518489 9115101018794468772388867)
        ·
          refine ⟨13672651528191703158583301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9115101018794468772388867 13672651528191703158583301)
          ·
            refine ⟨2563622161535944342234369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13672651528191703158583301 2563622161535944342234369)
            ·
              refine ⟨1922716621151958256675777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563622161535944342234369 1922716621151958256675777)
              ·
                refine ⟨1442037465863968692506833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922716621151958256675777 1442037465863968692506833)
                ·
                  refine ⟨1081528099397976519380125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1442037465863968692506833 1081528099397976519380125)
                  ·
                    refine ⟨405573037274241194767547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081528099397976519380125 405573037274241194767547)
                    ·
                      rfl

theorem cell22_1184776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_1184776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184776 prefixEnd_1184776 := by exact prefixLift 1184776
  have htrace : WordTrace (prefixWord ++ tailWord_1184776) baseStart_1184776 baseEnd_1184776 := by
    simpa [prefixWord, tailWord_1184776, baseEnd_1184776] using wordTrace_append hprefix tailTrace_1184776
  have hstable : (prefixWord ++ tailWord_1184776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184776).length < 2 ^ (prefixWord ++ tailWord_1184776).sum := by decide
  have hdescent : baseEnd_1184776 < baseStart_1184776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184778 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_1184778 : Nat := 118140960795 + 1184778 * 2 ^ 59
def prefixEnd_1184778 : Nat := 4983230072969 + 3 ^ 40 * 1184778 * 2
def baseEnd_1184778 : Nat := 135191240638371285405847

theorem tailTrace_1184778 : CollatzResearch.WordTrace tailWord_1184778 prefixEnd_1184778 135191240638371285405847 := by
  unfold tailWord_1184778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803100925439781204520747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28808269134506083212055325 10803100925439781204520747)
  ·
    refine ⟨16204651388159671806781121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10803100925439781204520747 16204651388159671806781121)
    ·
      refine ⟨12153488541119753855085841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16204651388159671806781121 12153488541119753855085841)
      ·
        refine ⟨9115116405839815391314381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12153488541119753855085841 9115116405839815391314381)
        ·
          refine ⟨3418168652189930771742893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9115116405839815391314381 3418168652189930771742893)
          ·
            refine ⟨1281813244571224039403585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418168652189930771742893 1281813244571224039403585)
            ·
              refine ⟨961359933428418029552689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281813244571224039403585 961359933428418029552689)
              ·
                refine ⟨721019950071313522164517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961359933428418029552689 721019950071313522164517)
                ·
                  refine ⟨135191240638371285405847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721019950071313522164517 135191240638371285405847)
                  ·
                    rfl

theorem cell22_1184778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_1184778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184778 prefixEnd_1184778 := by exact prefixLift 1184778
  have htrace : WordTrace (prefixWord ++ tailWord_1184778) baseStart_1184778 baseEnd_1184778 := by
    simpa [prefixWord, tailWord_1184778, baseEnd_1184778] using wordTrace_append hprefix tailTrace_1184778
  have hstable : (prefixWord ++ tailWord_1184778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184778).length < 2 ^ (prefixWord ++ tailWord_1184778).sum := by decide
  have hdescent : baseEnd_1184778 < baseStart_1184778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184789 : List Nat := [1, 3, 2, 1, 4, 3, 1, 7]
def baseStart_1184789 : Nat := 118140960795 + 1184789 * 2 ^ 59
def prefixEnd_1184789 : Nat := 4983230072969 + 3 ^ 40 * 1184789 * 2
def baseEnd_1184789 : Nat := 45064165271101499354723

theorem tailTrace_1184789 : CollatzResearch.WordTrace tailWord_1184789 prefixEnd_1184789 45064165271101499354723 := by
  unfold tailWord_1184789
  simp only [CollatzResearch.WordTrace]
  refine ⟨43212804904719273696733421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28808536603146182464488947 43212804904719273696733421)
  ·
    refine ⟨16204801839269727636275033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43212804904719273696733421 16204801839269727636275033)
    ·
      refine ⟨12153601379452295727206275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16204801839269727636275033 12153601379452295727206275)
      ·
        refine ⟨18230402069178443590809413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12153601379452295727206275 18230402069178443590809413)
        ·
          refine ⟨3418200387970958173276765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18230402069178443590809413 3418200387970958173276765)
          ·
            refine ⟨1281825145489109314978787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418200387970958173276765 1281825145489109314978787)
            ·
              refine ⟨1922737718233663972468181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281825145489109314978787 1922737718233663972468181)
              ·
                refine ⟨45064165271101499354723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1922737718233663972468181 45064165271101499354723)
                ·
                  rfl

theorem cell22_1184789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 7].length) (baseStart_1184789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184789 prefixEnd_1184789 := by exact prefixLift 1184789
  have htrace : WordTrace (prefixWord ++ tailWord_1184789) baseStart_1184789 baseEnd_1184789 := by
    simpa [prefixWord, tailWord_1184789, baseEnd_1184789] using wordTrace_append hprefix tailTrace_1184789
  have hstable : (prefixWord ++ tailWord_1184789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184789).length < 2 ^ (prefixWord ++ tailWord_1184789).sum := by decide
  have hdescent : baseEnd_1184789 < baseStart_1184789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184817 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 7]
def baseStart_1184817 : Nat := 118140960795 + 1184817 * 2 ^ 59
def prefixEnd_1184817 : Nat := 4983230072969 + 3 ^ 40 * 1184817 * 2
def baseEnd_1184817 : Nat := 135195690804043584830807

theorem tailTrace_1184817 : CollatzResearch.WordTrace tailWord_1184817 prefixEnd_1184817 135195690804043584830807 := by
  unfold tailWord_1184817
  simp only [CollatzResearch.WordTrace]
  refine ⟨43213826148617834478752705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28809217432411889652501803 43213826148617834478752705)
  ·
    refine ⟨32410369611463375859064529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43213826148617834478752705 32410369611463375859064529)
    ·
      refine ⟨24307777208597531894298397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32410369611463375859064529 24307777208597531894298397)
      ·
        refine ⟨9115416453224074460361899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24307777208597531894298397 9115416453224074460361899)
        ·
          refine ⟨13673124679836111690542849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9115416453224074460361899 13673124679836111690542849)
          ·
            refine ⟨10254843509877083767907137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13673124679836111690542849 10254843509877083767907137)
            ·
              refine ⟨7691132632407812825930353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10254843509877083767907137 7691132632407812825930353)
              ·
                refine ⟨5768349474305859619447765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691132632407812825930353 5768349474305859619447765)
                ·
                  refine ⟨135195690804043584830807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5768349474305859619447765 135195690804043584830807)
                  ·
                    rfl

theorem cell22_1184817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_1184817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184817 prefixEnd_1184817 := by exact prefixLift 1184817
  have htrace : WordTrace (prefixWord ++ tailWord_1184817) baseStart_1184817 baseEnd_1184817 := by
    simpa [prefixWord, tailWord_1184817, baseEnd_1184817] using wordTrace_append hprefix tailTrace_1184817
  have hstable : (prefixWord ++ tailWord_1184817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184817).length < 2 ^ (prefixWord ++ tailWord_1184817).sum := by decide
  have hdescent : baseEnd_1184817 < baseStart_1184817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184832 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1184832 : Nat := 118140960795 + 1184832 * 2 ^ 59
def prefixEnd_1184832 : Nat := 4983230072969 + 3 ^ 40 * 1184832 * 2
def baseEnd_1184832 : Nat := 405592207218675715367375

theorem tailTrace_1184832 : CollatzResearch.WordTrace tailWord_1184832 prefixEnd_1184832 405592207218675715367375 := by
  unfold tailWord_1184832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21607186621781746020274375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28809582162375661360365833 21607186621781746020274375)
  ·
    refine ⟨32410779932672619030411563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21607186621781746020274375 32410779932672619030411563)
    ·
      refine ⟨48616169899008928545617345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32410779932672619030411563 48616169899008928545617345)
      ·
        refine ⟨36462127424256696409213009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48616169899008928545617345 36462127424256696409213009)
        ·
          refine ⟨27346595568192522306909757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36462127424256696409213009 27346595568192522306909757)
          ·
            refine ⟨10254973338072195865091159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27346595568192522306909757 10254973338072195865091159)
            ·
              refine ⟨15382460007108293797636739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10254973338072195865091159 15382460007108293797636739)
              ·
                refine ⟨23073690010662440696455109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15382460007108293797636739 23073690010662440696455109)
                ·
                  refine ⟨4326316876999207630585333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23073690010662440696455109 4326316876999207630585333)
                  ·
                    refine ⟨405592207218675715367375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4326316876999207630585333 405592207218675715367375)
                    ·
                      rfl

theorem cell22_1184832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1184832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184832 prefixEnd_1184832 := by exact prefixLift 1184832
  have htrace : WordTrace (prefixWord ++ tailWord_1184832) baseStart_1184832 baseEnd_1184832 := by
    simpa [prefixWord, tailWord_1184832, baseEnd_1184832] using wordTrace_append hprefix tailTrace_1184832
  have hstable : (prefixWord ++ tailWord_1184832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184832).length < 2 ^ (prefixWord ++ tailWord_1184832).sum := by decide
  have hdescent : baseEnd_1184832 < baseStart_1184832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184838 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1184838 : Nat := 118140960795 + 1184838 * 2 ^ 59
def prefixEnd_1184838 : Nat := 4983230072969 + 3 ^ 40 * 1184838 * 2
def baseEnd_1184838 : Nat := 405594261141293699717357

theorem tailTrace_1184838 : CollatzResearch.WordTrace tailWord_1184838 prefixEnd_1184838 405594261141293699717357 := by
  unfold tailWord_1184838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350456002548179845789599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28809728054361170043511445 1350456002548179845789599)
  ·
    refine ⟨2025684003822269768684399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1350456002548179845789599 2025684003822269768684399)
    ·
      refine ⟨3038526005733404653026599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2025684003822269768684399 3038526005733404653026599)
      ·
        refine ⟨4557789008600106979539899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038526005733404653026599 4557789008600106979539899)
        ·
          refine ⟨6836683512900160469309849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557789008600106979539899 6836683512900160469309849)
          ·
            refine ⟨5127512634675120351982387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6836683512900160469309849 5127512634675120351982387)
            ·
              refine ⟨7691268952012680527973581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127512634675120351982387 7691268952012680527973581)
              ·
                refine ⟨2884225857004755197990093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7691268952012680527973581 2884225857004755197990093)
                ·
                  refine ⟨1081584696376783199246285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2884225857004755197990093 1081584696376783199246285)
                  ·
                    refine ⟨405594261141293699717357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081584696376783199246285 405594261141293699717357)
                    ·
                      rfl

theorem cell22_1184838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1184838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184838 prefixEnd_1184838 := by exact prefixLift 1184838
  have htrace : WordTrace (prefixWord ++ tailWord_1184838) baseStart_1184838 baseEnd_1184838 := by
    simpa [prefixWord, tailWord_1184838, baseEnd_1184838] using wordTrace_append hprefix tailTrace_1184838
  have hstable : (prefixWord ++ tailWord_1184838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184838).length < 2 ^ (prefixWord ++ tailWord_1184838).sum := by decide
  have hdescent : baseEnd_1184838 < baseStart_1184838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184872 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1184872 : Nat := 118140960795 + 1184872 * 2 ^ 59
def prefixEnd_1184872 : Nat := 4983230072969 + 3 ^ 40 * 1184872 * 2
def baseEnd_1184872 : Nat := 405605900036128944367253

theorem tailTrace_1184872 : CollatzResearch.WordTrace tailWord_1184872 prefixEnd_1184872 405605900036128944367253 := by
  unfold tailWord_1184872
  simp only [CollatzResearch.WordTrace]
  refine ⟨21607916081709289436002435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28810554775612385914669913 21607916081709289436002435)
  ·
    refine ⟨32411874122563934154003653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21607916081709289436002435 32411874122563934154003653)
    ·
      refine ⟨6077226397980737653875685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32411874122563934154003653 6077226397980737653875685)
      ·
        refine ⟨1139479949621388310101691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6077226397980737653875685 1139479949621388310101691)
        ·
          refine ⟨1709219924432082465152537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139479949621388310101691 1709219924432082465152537)
          ·
            refine ⟨1281914943324061848864403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709219924432082465152537 1281914943324061848864403)
            ·
              refine ⟨1922872414986092773296605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281914943324061848864403 1922872414986092773296605)
              ·
                refine ⟨721077155619784789986227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1922872414986092773296605 721077155619784789986227)
                ·
                  refine ⟨1081615733429677184979341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721077155619784789986227 1081615733429677184979341)
                  ·
                    refine ⟨405605900036128944367253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081615733429677184979341 405605900036128944367253)
                    ·
                      rfl

theorem cell22_1184872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1184872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184872 prefixEnd_1184872 := by exact prefixLift 1184872
  have htrace : WordTrace (prefixWord ++ tailWord_1184872) baseStart_1184872 baseEnd_1184872 := by
    simpa [prefixWord, tailWord_1184872, baseEnd_1184872] using wordTrace_append hprefix tailTrace_1184872
  have hstable : (prefixWord ++ tailWord_1184872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184872).length < 2 ^ (prefixWord ++ tailWord_1184872).sum := by decide
  have hdescent : baseEnd_1184872 < baseStart_1184872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184924 : List Nat := [2, 2, 3, 2, 1, 2, 2, 8]
def baseStart_1184924 : Nat := 118140960795 + 1184924 * 2 ^ 59
def prefixEnd_1184924 : Nat := 4983230072969 + 3 ^ 40 * 1184924 * 2
def baseEnd_1184924 : Nat := 45069300077646460229677

theorem tailTrace_1184924 : CollatzResearch.WordTrace tailWord_1184924 prefixEnd_1184924 45069300077646460229677 := by
  unfold tailWord_1184924
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608864379615095876448913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28811819172820127835265217 21608864379615095876448913)
  ·
    refine ⟨16206648284711321907336685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21608864379615095876448913 16206648284711321907336685)
    ·
      refine ⟨6077493106766745715251257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16206648284711321907336685 6077493106766745715251257)
      ·
        refine ⟨4558119830075059286438443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6077493106766745715251257 4558119830075059286438443)
        ·
          refine ⟨6837179745112588929657665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558119830075059286438443 6837179745112588929657665)
          ·
            refine ⟨5127884808834441697243249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6837179745112588929657665 5127884808834441697243249)
            ·
              refine ⟨3845913606625831272932437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5127884808834441697243249 3845913606625831272932437)
              ·
                refine ⟨45069300077646460229677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3845913606625831272932437 45069300077646460229677)
                ·
                  rfl

theorem cell22_1184924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_1184924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184924 prefixEnd_1184924 := by exact prefixLift 1184924
  have htrace : WordTrace (prefixWord ++ tailWord_1184924) baseStart_1184924 baseEnd_1184924 := by
    simpa [prefixWord, tailWord_1184924, baseEnd_1184924] using wordTrace_append hprefix tailTrace_1184924
  have hstable : (prefixWord ++ tailWord_1184924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184924).length < 2 ^ (prefixWord ++ tailWord_1184924).sum := by decide
  have hdescent : baseEnd_1184924 < baseStart_1184924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184941 : List Nat := [1, 5, 2, 1, 4, 9]
def baseStart_1184941 : Nat := 118140960795 + 1184941 * 2 ^ 59
def prefixEnd_1184941 : Nat := 4983230072969 + 3 ^ 40 * 1184941 * 2
def baseEnd_1184941 : Nat := 5007771853657231659161

theorem tailTrace_1184941 : CollatzResearch.WordTrace tailWord_1184941 prefixEnd_1184941 5007771853657231659161 := by
  unfold tailWord_1184941
  simp only [CollatzResearch.WordTrace]
  refine ⟨43218348800168603656266677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28812232533445735770844451 43218348800168603656266677)
  ·
    refine ⟨4051720200015806592775001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43218348800168603656266677 4051720200015806592775001)
    ·
      refine ⟨3038790150011854944581251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051720200015806592775001 3038790150011854944581251)
      ·
        refine ⟨4558185225017782416871877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038790150011854944581251 4558185225017782416871877)
        ·
          refine ⟨854659729690834203163477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4558185225017782416871877 854659729690834203163477)
          ·
            refine ⟨5007771853657231659161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 854659729690834203163477 5007771853657231659161)
            ·
              rfl

theorem cell22_1184941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 9].length) (baseStart_1184941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1184941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1184941 prefixEnd_1184941 := by exact prefixLift 1184941
  have htrace : WordTrace (prefixWord ++ tailWord_1184941) baseStart_1184941 baseEnd_1184941 := by
    simpa [prefixWord, tailWord_1184941, baseEnd_1184941] using wordTrace_append hprefix tailTrace_1184941
  have hstable : (prefixWord ++ tailWord_1184941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184941).length < 2 ^ (prefixWord ++ tailWord_1184941).sum := by decide
  have hdescent : baseEnd_1184941 < baseStart_1184941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185048 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_1185048 : Nat := 118140960795 + 1185048 * 2 ^ 59
def prefixEnd_1185048 : Nat := 4983230072969 + 3 ^ 40 * 1185048 * 2
def baseEnd_1185048 : Nat := 135222049477641050655571

theorem tailTrace_1185048 : CollatzResearch.WordTrace tailWord_1185048 prefixEnd_1185048 135222049477641050655571 := by
  unfold tailWord_1185048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21611125705390480465205899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28814834273853973953607865 21611125705390480465205899)
  ·
    refine ⟨32416688558085720697808849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21611125705390480465205899 32416688558085720697808849)
    ·
      refine ⟨24312516418564290523356637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32416688558085720697808849 24312516418564290523356637)
      ·
        refine ⟨9117193656961608946258739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24312516418564290523356637 9117193656961608946258739)
        ·
          refine ⟨13675790485442413419388109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117193656961608946258739 13675790485442413419388109)
          ·
            refine ⟨5128421432040905032270541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13675790485442413419388109 5128421432040905032270541)
            ·
              refine ⟨1923158037015339387101453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5128421432040905032270541 1923158037015339387101453)
              ·
                refine ⟨721184263880752270163045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1923158037015339387101453 721184263880752270163045)
                ·
                  refine ⟨135222049477641050655571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721184263880752270163045 135222049477641050655571)
                  ·
                    rfl

theorem cell22_1185048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_1185048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185048 prefixEnd_1185048 := by exact prefixLift 1185048
  have htrace : WordTrace (prefixWord ++ tailWord_1185048) baseStart_1185048 baseEnd_1185048 := by
    simpa [prefixWord, tailWord_1185048, baseEnd_1185048] using wordTrace_append hprefix tailTrace_1185048
  have hstable : (prefixWord ++ tailWord_1185048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185048).length < 2 ^ (prefixWord ++ tailWord_1185048).sum := by decide
  have hdescent : baseEnd_1185048 < baseStart_1185048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185059 : List Nat := [1, 1, 1, 4, 2, 3, 10]
def baseStart_1185059 : Nat := 118140960795 + 1185059 * 2 ^ 59
def prefixEnd_1185059 : Nat := 4983230072969 + 3 ^ 40 * 1185059 * 2
def baseEnd_1185059 : Nat := 15024811628063807034877

theorem tailTrace_1185059 : CollatzResearch.WordTrace tailWord_1185059 prefixEnd_1185059 15024811628063807034877 := by
  unfold tailWord_1185059
  simp only [CollatzResearch.WordTrace]
  refine ⟨43222652613741109809062231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28815101742494073206041487 43222652613741109809062231)
  ·
    refine ⟨64833978920611664713593347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43222652613741109809062231 64833978920611664713593347)
    ·
      refine ⟨97250968380917497070390021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64833978920611664713593347 97250968380917497070390021)
      ·
        refine ⟨18234556571422030700698129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97250968380917497070390021 18234556571422030700698129)
        ·
          refine ⟨13675917428566523025523597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18234556571422030700698129 13675917428566523025523597)
          ·
            refine ⟨5128469035712446134571349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13675917428566523025523597 5128469035712446134571349)
            ·
              refine ⟨15024811628063807034877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5128469035712446134571349 15024811628063807034877)
              ·
                rfl

theorem cell22_1185059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 10].length) (baseStart_1185059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185059 prefixEnd_1185059 := by exact prefixLift 1185059
  have htrace : WordTrace (prefixWord ++ tailWord_1185059) baseStart_1185059 baseEnd_1185059 := by
    simpa [prefixWord, tailWord_1185059, baseEnd_1185059] using wordTrace_append hprefix tailTrace_1185059
  have hstable : (prefixWord ++ tailWord_1185059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185059).length < 2 ^ (prefixWord ++ tailWord_1185059).sum := by decide
  have hdescent : baseEnd_1185059 < baseStart_1185059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185061 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1185061 : Nat := 118140960795 + 1185061 * 2 ^ 59
def prefixEnd_1185061 : Nat := 4983230072969 + 3 ^ 40 * 1185061 * 2
def baseEnd_1185061 : Nat := 405670598598595451391673

theorem tailTrace_1185061 : CollatzResearch.WordTrace tailWord_1185061 prefixEnd_1185061 405670598598595451391673 := by
  unfold tailWord_1185061
  simp only [CollatzResearch.WordTrace]
  refine ⟨43222725559733864150635037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28815150373155909433756691 43222725559733864150635037)
  ·
    refine ⟨16208522084900199056488139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43222725559733864150635037 16208522084900199056488139)
    ·
      refine ⟨24312783127350298584732209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16208522084900199056488139 24312783127350298584732209)
      ·
        refine ⟨18234587345512723938549157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24312783127350298584732209 18234587345512723938549157)
        ·
          refine ⟨3418985127283635738477967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18234587345512723938549157 3418985127283635738477967)
          ·
            refine ⟨5128477690925453607716951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418985127283635738477967 5128477690925453607716951)
            ·
              refine ⟨7692716536388180411575427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128477690925453607716951 7692716536388180411575427)
              ·
                refine ⟨11539074804582270617363141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692716536388180411575427 11539074804582270617363141)
                ·
                  refine ⟨2163576525859175740755589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11539074804582270617363141 2163576525859175740755589)
                  ·
                    refine ⟨405670598598595451391673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163576525859175740755589 405670598598595451391673)
                    ·
                      rfl

theorem cell22_1185061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1185061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185061 prefixEnd_1185061 := by exact prefixLift 1185061
  have htrace : WordTrace (prefixWord ++ tailWord_1185061) baseStart_1185061 baseEnd_1185061 := by
    simpa [prefixWord, tailWord_1185061, baseEnd_1185061] using wordTrace_append hprefix tailTrace_1185061
  have hstable : (prefixWord ++ tailWord_1185061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185061).length < 2 ^ (prefixWord ++ tailWord_1185061).sum := by decide
  have hdescent : baseEnd_1185061 < baseStart_1185061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185091 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 5, 3]
def baseStart_1185091 : Nat := 118140960795 + 1185091 * 2 ^ 59
def prefixEnd_1185091 : Nat := 4983230072969 + 3 ^ 40 * 1185091 * 2
def baseEnd_1185091 : Nat := 405680868211685373141581

theorem tailTrace_1185091 : CollatzResearch.WordTrace tailWord_1185091 prefixEnd_1185091 405680868211685373141581 := by
  unfold tailWord_1185091
  simp only [CollatzResearch.WordTrace]
  refine ⟨43223819749625179274227127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28815879833083452849484751 43223819749625179274227127)
  ·
    refine ⟨64835729624437768911340691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43223819749625179274227127 64835729624437768911340691)
    ·
      refine ⟨97253594436656653367011037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64835729624437768911340691 97253594436656653367011037)
      ·
        refine ⟨36470097913746245012629139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97253594436656653367011037 36470097913746245012629139)
        ·
          refine ⟨54705146870619367518943709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36470097913746245012629139 54705146870619367518943709)
          ·
            refine ⟨20514430076482262819603891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54705146870619367518943709 20514430076482262819603891)
            ·
              refine ⟨30771645114723394229405837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20514430076482262819603891 30771645114723394229405837)
              ·
                refine ⟨11539366918021272836027189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30771645114723394229405837 11539366918021272836027189)
                ·
                  refine ⟨1081815648564494328377549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11539366918021272836027189 1081815648564494328377549)
                  ·
                    refine ⟨405680868211685373141581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081815648564494328377549 405680868211685373141581)
                    ·
                      rfl

theorem cell22_1185091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 3].length) (baseStart_1185091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185091 prefixEnd_1185091 := by exact prefixLift 1185091
  have htrace : WordTrace (prefixWord ++ tailWord_1185091) baseStart_1185091 baseEnd_1185091 := by
    simpa [prefixWord, tailWord_1185091, baseEnd_1185091] using wordTrace_append hprefix tailTrace_1185091
  have hstable : (prefixWord ++ tailWord_1185091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185091).length < 2 ^ (prefixWord ++ tailWord_1185091).sum := by decide
  have hdescent : baseEnd_1185091 < baseStart_1185091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185110 : List Nat := [5, 2, 3, 1, 11]
def baseStart_1185110 : Nat := 118140960795 + 1185110 * 2 ^ 59
def prefixEnd_1185110 : Nat := 4983230072969 + 3 ^ 40 * 1185110 * 2
def baseEnd_1185110 : Nat := 1669495359259159081961

theorem tailTrace_1185110 : CollatzResearch.WordTrace tailWord_1185110 prefixEnd_1185110 1669495359259159081961 := by
  unfold tailWord_1185110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701532046034771594948049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28816341824370897012779189 2701532046034771594948049)
  ·
    refine ⟨2026149034526078696211037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2701532046034771594948049 2026149034526078696211037)
    ·
      refine ⟨759805887947279511079139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2026149034526078696211037 759805887947279511079139)
      ·
        refine ⟨1139708831920919266618709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759805887947279511079139 1139708831920919266618709)
        ·
          refine ⟨1669495359259159081961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1139708831920919266618709 1669495359259159081961)
          ·
            rfl

theorem cell22_1185110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 11].length) (baseStart_1185110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185110 prefixEnd_1185110 := by exact prefixLift 1185110
  have htrace : WordTrace (prefixWord ++ tailWord_1185110) baseStart_1185110 baseEnd_1185110 := by
    simpa [prefixWord, tailWord_1185110, baseEnd_1185110] using wordTrace_append hprefix tailTrace_1185110
  have hstable : (prefixWord ++ tailWord_1185110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185110).length < 2 ^ (prefixWord ++ tailWord_1185110).sum := by decide
  have hdescent : baseEnd_1185110 < baseStart_1185110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185125 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_1185125 : Nat := 118140960795 + 1185125 * 2 ^ 59
def prefixEnd_1185125 : Nat := 4983230072969 + 3 ^ 40 * 1185125 * 2
def baseEnd_1185125 : Nat := 405692507106520617791477

theorem tailTrace_1185125 : CollatzResearch.WordTrace tailWord_1185125 prefixEnd_1185125 405692507106520617791477 := by
  unfold tailWord_1185125
  simp only [CollatzResearch.WordTrace]
  refine ⟨43225059831502003080964829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28816706554334668720643219 43225059831502003080964829)
  ·
    refine ⟨16209397436813251155361811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43225059831502003080964829 16209397436813251155361811)
    ·
      refine ⟨24314096155219876733042717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16209397436813251155361811 24314096155219876733042717)
      ·
        refine ⟨9117786058207453774891019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24314096155219876733042717 9117786058207453774891019)
        ·
          refine ⟨13676679087311180662336529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117786058207453774891019 13676679087311180662336529)
          ·
            refine ⟨10257509315483385496752397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13676679087311180662336529 10257509315483385496752397)
            ·
              refine ⟨3846565993306269561282149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10257509315483385496752397 3846565993306269561282149)
              ·
                refine ⟨721231123744925542740403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3846565993306269561282149 721231123744925542740403)
                ·
                  refine ⟨1081846685617388314110605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721231123744925542740403 1081846685617388314110605)
                  ·
                    refine ⟨405692507106520617791477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1081846685617388314110605 405692507106520617791477)
                    ·
                      rfl

theorem cell22_1185125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_1185125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185125 prefixEnd_1185125 := by exact prefixLift 1185125
  have htrace : WordTrace (prefixWord ++ tailWord_1185125) baseStart_1185125 baseEnd_1185125 := by
    simpa [prefixWord, tailWord_1185125, baseEnd_1185125] using wordTrace_append hprefix tailTrace_1185125
  have hstable : (prefixWord ++ tailWord_1185125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185125).length < 2 ^ (prefixWord ++ tailWord_1185125).sum := by decide
  have hdescent : baseEnd_1185125 < baseStart_1185125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185136 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_1185136 : Nat := 118140960795 + 1185136 * 2 ^ 59
def prefixEnd_1185136 : Nat := 4983230072969 + 3 ^ 40 * 1185136 * 2
def baseEnd_1185136 : Nat := 405696272631320255766443

theorem tailTrace_1185136 : CollatzResearch.WordTrace tailWord_1185136 prefixEnd_1185136 405696272631320255766443 := by
  unfold tailWord_1185136
  simp only [CollatzResearch.WordTrace]
  refine ⟨21612730517231075979807631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28816974022974767973076841 21612730517231075979807631)
  ·
    refine ⟨32419095775846613969711447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21612730517231075979807631 32419095775846613969711447)
    ·
      refine ⟨48628643663769920954567171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32419095775846613969711447 48628643663769920954567171)
      ·
        refine ⟨72942965495654881431850757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48628643663769920954567171 72942965495654881431850757)
        ·
          refine ⟨13676806030435290268472017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72942965495654881431850757 13676806030435290268472017)
          ·
            refine ⟨10257604522826467701354013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13676806030435290268472017 10257604522826467701354013)
            ·
              refine ⟨3846601696059925388007755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10257604522826467701354013 3846601696059925388007755)
              ·
                refine ⟨5769902544089888082011633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846601696059925388007755 5769902544089888082011633)
                ·
                  refine ⟨4327426908067416061508725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769902544089888082011633 4327426908067416061508725)
                  ·
                    refine ⟨405696272631320255766443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4327426908067416061508725 405696272631320255766443)
                    ·
                      rfl

theorem cell22_1185136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_1185136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185136 prefixEnd_1185136 := by exact prefixLift 1185136
  have htrace : WordTrace (prefixWord ++ tailWord_1185136) baseStart_1185136 baseEnd_1185136 := by
    simpa [prefixWord, tailWord_1185136, baseEnd_1185136] using wordTrace_append hprefix tailTrace_1185136
  have hstable : (prefixWord ++ tailWord_1185136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185136).length < 2 ^ (prefixWord ++ tailWord_1185136).sum := by decide
  have hdescent : baseEnd_1185136 < baseStart_1185136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185183 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 6]
def baseStart_1185183 : Nat := 118140960795 + 1185183 * 2 ^ 59
def prefixEnd_1185183 : Nat := 4983230072969 + 3 ^ 40 * 1185183 * 2
def baseEnd_1185183 : Nat := 135237453897275933280433

theorem tailTrace_1185183 : CollatzResearch.WordTrace tailWord_1185183 prefixEnd_1185183 135237453897275933280433 := by
  unfold tailWord_1185183
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227175265291878986576203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28818116843527919324384135 43227175265291878986576203)
  ·
    refine ⟨64840762897937818479864305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43227175265291878986576203 64840762897937818479864305)
    ·
      refine ⟨48630572173453363859898229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64840762897937818479864305 48630572173453363859898229)
      ·
        refine ⟨4559116141261252861865459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48630572173453363859898229 4559116141261252861865459)
        ·
          refine ⟨6838674211891879292798189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559116141261252861865459 6838674211891879292798189)
          ·
            refine ⟨2564502829459454734799321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6838674211891879292798189 2564502829459454734799321)
            ·
              refine ⟨1923377122094591051099491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564502829459454734799321 1923377122094591051099491)
              ·
                refine ⟨2885065683141886576649237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923377122094591051099491 2885065683141886576649237)
                ·
                  refine ⟨135237453897275933280433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2885065683141886576649237 135237453897275933280433)
                  ·
                    rfl

theorem cell22_1185183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 6].length) (baseStart_1185183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185183 prefixEnd_1185183 := by exact prefixLift 1185183
  have htrace : WordTrace (prefixWord ++ tailWord_1185183) baseStart_1185183 baseEnd_1185183 := by
    simpa [prefixWord, tailWord_1185183, baseEnd_1185183] using wordTrace_append hprefix tailTrace_1185183
  have hstable : (prefixWord ++ tailWord_1185183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185183).length < 2 ^ (prefixWord ++ tailWord_1185183).sum := by decide
  have hdescent : baseEnd_1185183 < baseStart_1185183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185196 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1185196 : Nat := 118140960795 + 1185196 * 2 ^ 59
def prefixEnd_1185196 : Nat := 4983230072969 + 3 ^ 40 * 1185196 * 2
def baseEnd_1185196 : Nat := 405716811857500099266259

theorem tailTrace_1185196 : CollatzResearch.WordTrace tailWord_1185196 prefixEnd_1185196 405716811857500099266259 := by
  unfold tailWord_1185196
  simp only [CollatzResearch.WordTrace]
  refine ⟨21613824707122391103399721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28818432942829854804532961 21613824707122391103399721)
  ·
    refine ⟨16210368530341793327549791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21613824707122391103399721 16210368530341793327549791)
    ·
      refine ⟨24315552795512689991324687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16210368530341793327549791 24315552795512689991324687)
      ·
        refine ⟨36473329193269034986987031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24315552795512689991324687 36473329193269034986987031)
        ·
          refine ⟨54709993789903552480480547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36473329193269034986987031 54709993789903552480480547)
          ·
            refine ⟨82064990684855328720720821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54709993789903552480480547 82064990684855328720720821)
            ·
              refine ⟨7693592876705187067567577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82064990684855328720720821 7693592876705187067567577)
              ·
                refine ⟨5770194657528890300675683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7693592876705187067567577 5770194657528890300675683)
                ·
                  refine ⟨8655291986293335451013525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770194657528890300675683 8655291986293335451013525)
                  ·
                    refine ⟨405716811857500099266259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8655291986293335451013525 405716811857500099266259)
                    ·
                      rfl

theorem cell22_1185196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1185196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185196 prefixEnd_1185196 := by exact prefixLift 1185196
  have htrace : WordTrace (prefixWord ++ tailWord_1185196) baseStart_1185196 baseEnd_1185196 := by
    simpa [prefixWord, tailWord_1185196, baseEnd_1185196] using wordTrace_append hprefix tailTrace_1185196
  have hstable : (prefixWord ++ tailWord_1185196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185196).length < 2 ^ (prefixWord ++ tailWord_1185196).sum := by decide
  have hdescent : baseEnd_1185196 < baseStart_1185196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185213 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1185213 : Nat := 118140960795 + 1185213 * 2 ^ 59
def prefixEnd_1185213 : Nat := 4983230072969 + 3 ^ 40 * 1185213 * 2
def baseEnd_1185213 : Nat := 405722631304917721591207

theorem tailTrace_1185213 : CollatzResearch.WordTrace tailWord_1185213 prefixEnd_1185213 405722631304917721591207 := by
  unfold tailWord_1185213
  simp only [CollatzResearch.WordTrace]
  refine ⟨43228269455183194110168293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28818846303455462740112195 43228269455183194110168293)
  ·
    refine ⟨8105300522846848895656555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43228269455183194110168293 8105300522846848895656555)
    ·
      refine ⟨12157950784270273343484833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105300522846848895656555 12157950784270273343484833)
      ·
        refine ⟨9118463088202705007613625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12157950784270273343484833 9118463088202705007613625)
        ·
          refine ⟨6838847316152028755710219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9118463088202705007613625 6838847316152028755710219)
          ·
            refine ⟨10258270974228043133565329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838847316152028755710219 10258270974228043133565329)
            ·
              refine ⟨7693703230671032350173997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10258270974228043133565329 7693703230671032350173997)
              ·
                refine ⟨2885138711501637131315249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7693703230671032350173997 2885138711501637131315249)
                ·
                  refine ⟨2163854033626227848486437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2885138711501637131315249 2163854033626227848486437)
                  ·
                    refine ⟨405722631304917721591207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163854033626227848486437 405722631304917721591207)
                    ·
                      rfl

theorem cell22_1185213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1185213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185213 prefixEnd_1185213 := by exact prefixLift 1185213
  have htrace : WordTrace (prefixWord ++ tailWord_1185213) baseStart_1185213 baseEnd_1185213 := by
    simpa [prefixWord, tailWord_1185213, baseEnd_1185213] using wordTrace_append hprefix tailTrace_1185213
  have hstable : (prefixWord ++ tailWord_1185213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185213).length < 2 ^ (prefixWord ++ tailWord_1185213).sum := by decide
  have hdescent : baseEnd_1185213 < baseStart_1185213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185228 : List Nat := [2, 2, 1, 4, 2, 3, 8]
def baseStart_1185228 : Nat := 118140960795 + 1185228 * 2 ^ 59
def prefixEnd_1185228 : Nat := 4983230072969 + 3 ^ 40 * 1185228 * 2
def baseEnd_1185228 : Nat := 15026954300424543795043

theorem tailTrace_1185228 : CollatzResearch.WordTrace tailWord_1185228 prefixEnd_1185228 15026954300424543795043 := by
  unfold tailWord_1185228
  simp only [CollatzResearch.WordTrace]
  refine ⟨21614408275064425835982169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28819211033419234447976225 21614408275064425835982169)
  ·
    refine ⟨16210806206298319376986627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21614408275064425835982169 16210806206298319376986627)
    ·
      refine ⟨24316209309447479065479941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16210806206298319376986627 24316209309447479065479941)
      ·
        refine ⟨4559289245521402324777489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24316209309447479065479941 4559289245521402324777489)
        ·
          refine ⟨3419466934141051743583117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559289245521402324777489 3419466934141051743583117)
          ·
            refine ⟨1282300100302894403843669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3419466934141051743583117 1282300100302894403843669)
            ·
              refine ⟨15026954300424543795043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1282300100302894403843669 15026954300424543795043)
              ·
                rfl

theorem cell22_1185228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 8].length) (baseStart_1185228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185228 prefixEnd_1185228 := by exact prefixLift 1185228
  have htrace : WordTrace (prefixWord ++ tailWord_1185228) baseStart_1185228 baseEnd_1185228 := by
    simpa [prefixWord, tailWord_1185228, baseEnd_1185228] using wordTrace_append hprefix tailTrace_1185228
  have hstable : (prefixWord ++ tailWord_1185228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185228).length < 2 ^ (prefixWord ++ tailWord_1185228).sum := by decide
  have hdescent : baseEnd_1185228 < baseStart_1185228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1185271 : Nat := 118140960795 + 1185271 * 2 ^ 59
def prefixEnd_1185271 : Nat := 4983230072969 + 3 ^ 40 * 1185271 * 2
def baseEnd_1185271 : Nat := 405742485890224903641029

theorem tailTrace_1185271 : CollatzResearch.WordTrace tailWord_1185271 prefixEnd_1185271 405742485890224903641029 := by
  unfold tailWord_1185271
  simp only [CollatzResearch.WordTrace]
  refine ⟨43230384888973070015779667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28820256592648713343853111 43230384888973070015779667)
  ·
    refine ⟨64845577333459605023669501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43230384888973070015779667 64845577333459605023669501)
    ·
      refine ⟨24317091500047351883876063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64845577333459605023669501 24317091500047351883876063)
      ·
        refine ⟨36475637250071027825814095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24317091500047351883876063 36475637250071027825814095)
        ·
          refine ⟨54713455875106541738721143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36475637250071027825814095 54713455875106541738721143)
          ·
            refine ⟨82070183812659812608081715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54713455875106541738721143 82070183812659812608081715)
            ·
              refine ⟨123105275718989718912122573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82070183812659812608081715 123105275718989718912122573)
              ·
                refine ⟨46164478394621144592045965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123105275718989718912122573 46164478394621144592045965)
                ·
                  refine ⟨17311679397982929222017237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46164478394621144592045965 17311679397982929222017237)
                  ·
                    refine ⟨405742485890224903641029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17311679397982929222017237 405742485890224903641029)
                    ·
                      rfl

theorem cell22_1185271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1185271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185271 prefixEnd_1185271 := by exact prefixLift 1185271
  have htrace : WordTrace (prefixWord ++ tailWord_1185271) baseStart_1185271 baseEnd_1185271 := by
    simpa [prefixWord, tailWord_1185271, baseEnd_1185271] using wordTrace_append hprefix tailTrace_1185271
  have hstable : (prefixWord ++ tailWord_1185271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185271).length < 2 ^ (prefixWord ++ tailWord_1185271).sum := by decide
  have hdescent : baseEnd_1185271 < baseStart_1185271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185290 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_1185290 : Nat := 118140960795 + 1185290 * 2 ^ 59
def prefixEnd_1185290 : Nat := 4983230072969 + 3 ^ 40 * 1185290 * 2
def baseEnd_1185290 : Nat := 135249663326171729138657

theorem tailTrace_1185290 : CollatzResearch.WordTrace tailWord_1185290 prefixEnd_1185290 135249663326171729138657 := by
  unfold tailWord_1185290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807769468976059065180331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28820718583936157507147549 10807769468976059065180331)
  ·
    refine ⟨16211654203464088597770497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10807769468976059065180331 16211654203464088597770497)
    ·
      refine ⟨12158740652598066448327873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16211654203464088597770497 12158740652598066448327873)
      ·
        refine ⟨9119055489448549836245905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12158740652598066448327873 9119055489448549836245905)
        ·
          refine ⟨6839291617086412377184429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9119055489448549836245905 6839291617086412377184429)
          ·
            refine ⟨2564734356407404641444161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6839291617086412377184429 2564734356407404641444161)
            ·
              refine ⟨1923550767305553481083121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564734356407404641444161 1923550767305553481083121)
              ·
                refine ⟨1442663075479165110812341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923550767305553481083121 1442663075479165110812341)
                ·
                  refine ⟨135249663326171729138657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1442663075479165110812341 135249663326171729138657)
                  ·
                    rfl

theorem cell22_1185290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_1185290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185290 prefixEnd_1185290 := by exact prefixLift 1185290
  have htrace : WordTrace (prefixWord ++ tailWord_1185290) baseStart_1185290 baseEnd_1185290 := by
    simpa [prefixWord, tailWord_1185290, baseEnd_1185290] using wordTrace_append hprefix tailTrace_1185290
  have hstable : (prefixWord ++ tailWord_1185290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185290).length < 2 ^ (prefixWord ++ tailWord_1185290).sum := by decide
  have hdescent : baseEnd_1185290 < baseStart_1185290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185294 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_1185294 : Nat := 118140960795 + 1185294 * 2 ^ 59
def prefixEnd_1185294 : Nat := 4983230072969 + 3 ^ 40 * 1185294 * 2
def baseEnd_1185294 : Nat := 405750359260260510315959

theorem tailTrace_1185294 : CollatzResearch.WordTrace tailWord_1185294 prefixEnd_1185294 405750359260260510315959 := by
  unfold tailWord_1185294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403902970986218117983367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28820815845259829962577957 5403902970986218117983367)
  ·
    refine ⟨8105854456479327176975051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5403902970986218117983367 8105854456479327176975051)
    ·
      refine ⟨12158781684718990765462577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105854456479327176975051 12158781684718990765462577)
      ·
        refine ⟨9119086263539243074096933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12158781684718990765462577 9119086263539243074096933)
        ·
          refine ⟨1709828674413608076393175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9119086263539243074096933 1709828674413608076393175)
          ·
            refine ⟨2564743011620412114589763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709828674413608076393175 2564743011620412114589763)
            ·
              refine ⟨3847114517430618171884645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564743011620412114589763 3847114517430618171884645)
              ·
                refine ⟨721333972018240907228371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3847114517430618171884645 721333972018240907228371)
                ·
                  refine ⟨1082000958027361360842557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721333972018240907228371 1082000958027361360842557)
                  ·
                    refine ⟨405750359260260510315959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082000958027361360842557 405750359260260510315959)
                    ·
                      rfl

theorem cell22_1185294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_1185294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185294 prefixEnd_1185294 := by exact prefixLift 1185294
  have htrace : WordTrace (prefixWord ++ tailWord_1185294) baseStart_1185294 baseEnd_1185294 := by
    simpa [prefixWord, tailWord_1185294, baseEnd_1185294] using wordTrace_append hprefix tailTrace_1185294
  have hstable : (prefixWord ++ tailWord_1185294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185294).length < 2 ^ (prefixWord ++ tailWord_1185294).sum := by decide
  have hdescent : baseEnd_1185294 < baseStart_1185294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185335 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 4]
def baseStart_1185335 : Nat := 118140960795 + 1185335 * 2 ^ 59
def prefixEnd_1185335 : Nat := 4983230072969 + 3 ^ 40 * 1185335 * 2
def baseEnd_1185335 : Nat := 135254798132716690013611

theorem tailTrace_1185335 : CollatzResearch.WordTrace tailWord_1185335 prefixEnd_1185335 135254798132716690013611 := by
  unfold tailWord_1185335
  simp only [CollatzResearch.WordTrace]
  refine ⟨43232719160741208946109459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28821812773827472630739639 43232719160741208946109459)
  ·
    refine ⟨64849078741111813419164189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43232719160741208946109459 64849078741111813419164189)
    ·
      refine ⟨24318404527916930032186571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64849078741111813419164189 24318404527916930032186571)
      ·
        refine ⟨36477606791875395048279857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24318404527916930032186571 36477606791875395048279857)
        ·
          refine ⟨27358205093906546286209893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36477606791875395048279857 27358205093906546286209893)
          ·
            refine ⟨5129663455107477428664355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27358205093906546286209893 5129663455107477428664355)
            ·
              refine ⟨7694495182661216142996533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129663455107477428664355 7694495182661216142996533)
              ·
                refine ⟨721358923374489013405925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7694495182661216142996533 721358923374489013405925)
                ·
                  refine ⟨135254798132716690013611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721358923374489013405925 135254798132716690013611)
                  ·
                    rfl

theorem cell22_1185335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 4].length) (baseStart_1185335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185335 prefixEnd_1185335 := by exact prefixLift 1185335
  have htrace : WordTrace (prefixWord ++ tailWord_1185335) baseStart_1185335 baseEnd_1185335 := by
    simpa [prefixWord, tailWord_1185335, baseEnd_1185335] using wordTrace_append hprefix tailTrace_1185335
  have hstable : (prefixWord ++ tailWord_1185335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185335).length < 2 ^ (prefixWord ++ tailWord_1185335).sum := by decide
  have hdescent : baseEnd_1185335 < baseStart_1185335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185337 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_1185337 : Nat := 118140960795 + 1185337 * 2 ^ 59
def prefixEnd_1185337 : Nat := 4983230072969 + 3 ^ 40 * 1185337 * 2
def baseEnd_1185337 : Nat := 405765079039022731490827

theorem tailTrace_1185337 : CollatzResearch.WordTrace tailWord_1185337 prefixEnd_1185337 405765079039022731490827 := by
  unfold tailWord_1185337
  simp only [CollatzResearch.WordTrace]
  refine ⟨43232792106733963287682265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28821861404489308858454843 43232792106733963287682265)
  ·
    refine ⟨32424594080050472465761699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43232792106733963287682265 32424594080050472465761699)
    ·
      refine ⟨48636891120075708698642549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32424594080050472465761699 48636891120075708698642549)
      ·
        refine ⟨4559708542507097690497739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48636891120075708698642549 4559708542507097690497739)
        ·
          refine ⟨6839562813760646535746609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559708542507097690497739 6839562813760646535746609)
          ·
            refine ⟨5129672110320484901809957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6839562813760646535746609 5129672110320484901809957)
            ·
              refine ⟨961813520685090919089367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5129672110320484901809957 961813520685090919089367)
              ·
                refine ⟨1442720281027636378634051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961813520685090919089367 1442720281027636378634051)
                ·
                  refine ⟨2164080421541454567951077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442720281027636378634051 2164080421541454567951077)
                  ·
                    refine ⟨405765079039022731490827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2164080421541454567951077 405765079039022731490827)
                    ·
                      rfl

theorem cell22_1185337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_1185337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185337 prefixEnd_1185337 := by exact prefixLift 1185337
  have htrace : WordTrace (prefixWord ++ tailWord_1185337) baseStart_1185337 baseEnd_1185337 := by
    simpa [prefixWord, tailWord_1185337, baseEnd_1185337] using wordTrace_append hprefix tailTrace_1185337
  have hstable : (prefixWord ++ tailWord_1185337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185337).length < 2 ^ (prefixWord ++ tailWord_1185337).sum := by decide
  have hdescent : baseEnd_1185337 < baseStart_1185337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185380 : List Nat := [2, 3, 1, 1, 2, 3, 4, 6]
def baseStart_1185380 : Nat := 118140960795 + 1185380 * 2 ^ 59
def prefixEnd_1185380 : Nat := 4983230072969 + 3 ^ 40 * 1185380 * 2
def baseEnd_1185380 : Nat := 45086644313087216962855

theorem tailTrace_1185380 : CollatzResearch.WordTrace tailWord_1185380 prefixEnd_1185380 45086644313087216962855 := by
  unfold tailWord_1185380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21617180222789090815748797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28822906963718787754331729 21617180222789090815748797)
  ·
    refine ⟨8106442583545909055905799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21617180222789090815748797 8106442583545909055905799)
    ·
      refine ⟨12159663875318863583858699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8106442583545909055905799 12159663875318863583858699)
      ·
        refine ⟨18239495812978295375788049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12159663875318863583858699 18239495812978295375788049)
        ·
          refine ⟨13679621859733721531841037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18239495812978295375788049 13679621859733721531841037)
          ·
            refine ⟨5129858197400145574440389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13679621859733721531841037 5129858197400145574440389)
            ·
              refine ⟨961848412012527295207573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5129858197400145574440389 961848412012527295207573)
              ·
                refine ⟨45086644313087216962855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 961848412012527295207573 45086644313087216962855)
                ·
                  rfl

theorem cell22_1185380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_1185380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185380 prefixEnd_1185380 := by exact prefixLift 1185380
  have htrace : WordTrace (prefixWord ++ tailWord_1185380) baseStart_1185380 baseEnd_1185380 := by
    simpa [prefixWord, tailWord_1185380, baseEnd_1185380] using wordTrace_append hprefix tailTrace_1185380
  have hstable : (prefixWord ++ tailWord_1185380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185380).length < 2 ^ (prefixWord ++ tailWord_1185380).sum := by decide
  have hdescent : baseEnd_1185380 < baseStart_1185380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185408 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_1185408 : Nat := 118140960795 + 1185408 * 2 ^ 59
def prefixEnd_1185408 : Nat := 4983230072969 + 3 ^ 40 * 1185408 * 2
def baseEnd_1185408 : Nat := 135263127930000737655203

theorem tailTrace_1185408 : CollatzResearch.WordTrace tailWord_1185408 prefixEnd_1185408 135263127930000737655203 := by
  unfold tailWord_1185408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21617690844738371206758439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28823587792984494942344585 21617690844738371206758439)
  ·
    refine ⟨32426536267107556810137659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21617690844738371206758439 32426536267107556810137659)
    ·
      refine ⟨48639804400661335215206489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32426536267107556810137659 48639804400661335215206489)
      ·
        refine ⟨36479853300496001411404867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48639804400661335215206489 36479853300496001411404867)
        ·
          refine ⟨54719779950744002117107301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36479853300496001411404867 54719779950744002117107301)
          ·
            refine ⟨10259958740764500396957619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54719779950744002117107301 10259958740764500396957619)
            ·
              refine ⟨15389938111146750595436429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10259958740764500396957619 15389938111146750595436429)
              ·
                refine ⟨5771226791680031473288661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15389938111146750595436429 5771226791680031473288661)
                ·
                  refine ⟨135263127930000737655203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5771226791680031473288661 135263127930000737655203)
                  ·
                    rfl

theorem cell22_1185408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_1185408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185408 prefixEnd_1185408 := by exact prefixLift 1185408
  have htrace : WordTrace (prefixWord ++ tailWord_1185408) baseStart_1185408 baseEnd_1185408 := by
    simpa [prefixWord, tailWord_1185408, baseEnd_1185408] using wordTrace_append hprefix tailTrace_1185408
  have hstable : (prefixWord ++ tailWord_1185408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185408).length < 2 ^ (prefixWord ++ tailWord_1185408).sum := by decide
  have hdescent : baseEnd_1185408 < baseStart_1185408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185547 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 3, 3]
def baseStart_1185547 : Nat := 118140960795 + 1185547 * 2 ^ 59
def prefixEnd_1185547 : Nat := 4983230072969 + 3 ^ 40 * 1185547 * 2
def baseEnd_1185547 : Nat := 405836966330652183740183

theorem tailTrace_1185547 : CollatzResearch.WordTrace tailWord_1185547 prefixEnd_1185547 405836966330652183740183 := by
  unfold tailWord_1185547
  simp only [CollatzResearch.WordTrace]
  refine ⟨43240451435973169152826895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28826967623982112768551263 43240451435973169152826895)
  ·
    refine ⟨64860677153959753729240343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43240451435973169152826895 64860677153959753729240343)
    ·
      refine ⟨97291015730939630593860515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64860677153959753729240343 97291015730939630593860515)
      ·
        refine ⟨145936523596409445890790773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97291015730939630593860515 145936523596409445890790773)
        ·
          refine ⟨13681549087163385552261635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145936523596409445890790773 13681549087163385552261635)
          ·
            refine ⟨20522323630745078328392453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13681549087163385552261635 20522323630745078328392453)
            ·
              refine ⟨3847935680764702186573585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20522323630745078328392453 3847935680764702186573585)
              ·
                refine ⟨2885951760573526639930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847935680764702186573585 2885951760573526639930189)
                ·
                  refine ⟨1082231910215072489973821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2885951760573526639930189 1082231910215072489973821)
                  ·
                    refine ⟨405836966330652183740183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082231910215072489973821 405836966330652183740183)
                    ·
                      rfl

theorem cell22_1185547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 3].length) (baseStart_1185547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185547 prefixEnd_1185547 := by exact prefixLift 1185547
  have htrace : WordTrace (prefixWord ++ tailWord_1185547) baseStart_1185547 baseEnd_1185547 := by
    simpa [prefixWord, tailWord_1185547, baseEnd_1185547] using wordTrace_append hprefix tailTrace_1185547
  have hstable : (prefixWord ++ tailWord_1185547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185547).length < 2 ^ (prefixWord ++ tailWord_1185547).sum := by decide
  have hdescent : baseEnd_1185547 < baseStart_1185547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185560 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_1185560 : Nat := 118140960795 + 1185560 * 2 ^ 59
def prefixEnd_1185560 : Nat := 4983230072969 + 3 ^ 40 * 1185560 * 2
def baseEnd_1185560 : Nat := 135280472165441494388381

theorem tailTrace_1185560 : CollatzResearch.WordTrace tailWord_1185560 prefixEnd_1185560 135280472165441494388381 := by
  unfold tailWord_1185560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620462792463036186525067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28827283723284048248700089 21620462792463036186525067)
  ·
    refine ⟨32430694188694554279787601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21620462792463036186525067 32430694188694554279787601)
    ·
      refine ⟨24323020641520915709840701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32430694188694554279787601 24323020641520915709840701)
      ·
        refine ⟨9121132740570343391190263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24323020641520915709840701 9121132740570343391190263)
        ·
          refine ⟨13681699110855515086785395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9121132740570343391190263 13681699110855515086785395)
          ·
            refine ⟨20522548666283272630178093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13681699110855515086785395 20522548666283272630178093)
            ·
              refine ⟨7695955749856227236316785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20522548666283272630178093 7695955749856227236316785)
              ·
                refine ⟨5771966812392170427237589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7695955749856227236316785 5771966812392170427237589)
                ·
                  refine ⟨135280472165441494388381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5771966812392170427237589 135280472165441494388381)
                  ·
                    rfl

theorem cell22_1185560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_1185560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185560 prefixEnd_1185560 := by exact prefixLift 1185560
  have htrace : WordTrace (prefixWord ++ tailWord_1185560) baseStart_1185560 baseEnd_1185560 := by
    simpa [prefixWord, tailWord_1185560, baseEnd_1185560] using wordTrace_append hprefix tailTrace_1185560
  have hstable : (prefixWord ++ tailWord_1185560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185560).length < 2 ^ (prefixWord ++ tailWord_1185560).sum := by decide
  have hdescent : baseEnd_1185560 < baseStart_1185560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185566 : List Nat := [4, 3, 2, 2, 1, 2, 8]
def baseStart_1185566 : Nat := 118140960795 + 1185566 * 2 ^ 59
def prefixEnd_1185566 : Nat := 4983230072969 + 3 ^ 40 * 1185566 * 2
def baseEnd_1185566 : Nat := 15031239645146017315375

theorem tailTrace_1185566 : CollatzResearch.WordTrace tailWord_1185566 prefixEnd_1185566 15031239645146017315375 := by
  unfold tailWord_1185566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405143052863041924721069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28827429615269556931845701 5405143052863041924721069)
  ·
    refine ⟨2026928644823640721770401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5405143052863041924721069 2026928644823640721770401)
    ·
      refine ⟨1520196483617730541327801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2026928644823640721770401 1520196483617730541327801)
      ·
        refine ⟨1140147362713297905995851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520196483617730541327801 1140147362713297905995851)
        ·
          refine ⟨1710221044069946858993777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140147362713297905995851 1710221044069946858993777)
          ·
            refine ⟨1282665783052460144245333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710221044069946858993777 1282665783052460144245333)
            ·
              refine ⟨15031239645146017315375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1282665783052460144245333 15031239645146017315375)
              ·
                rfl

theorem cell22_1185566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 8].length) (baseStart_1185566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185566 prefixEnd_1185566 := by exact prefixLift 1185566
  have htrace : WordTrace (prefixWord ++ tailWord_1185566) baseStart_1185566 baseEnd_1185566 := by
    simpa [prefixWord, tailWord_1185566, baseEnd_1185566] using wordTrace_append hprefix tailTrace_1185566
  have hstable : (prefixWord ++ tailWord_1185566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185566).length < 2 ^ (prefixWord ++ tailWord_1185566).sum := by decide
  have hdescent : baseEnd_1185566 < baseStart_1185566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185594 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_1185594 : Nat := 118140960795 + 1185594 * 2 ^ 59
def prefixEnd_1185594 : Nat := 4983230072969 + 3 ^ 40 * 1185594 * 2
def baseEnd_1185594 : Nat := 135284351797053242605013

theorem tailTrace_1185594 : CollatzResearch.WordTrace tailWord_1185594 prefixEnd_1185594 135284351797053242605013 := by
  unfold tailWord_1185594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810541416700724044946959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28828110444535264119858557 10810541416700724044946959)
  ·
    refine ⟨16215812125051086067420439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10810541416700724044946959 16215812125051086067420439)
    ·
      refine ⟨24323718187576629101130659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16215812125051086067420439 24323718187576629101130659)
      ·
        refine ⟨36485577281364943651695989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24323718187576629101130659 36485577281364943651695989)
        ·
          refine ⟨3420522870127963467346499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36485577281364943651695989 3420522870127963467346499)
          ·
            refine ⟨5130784305191945201019749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420522870127963467346499 5130784305191945201019749)
            ·
              refine ⟨962022057223489725191203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5130784305191945201019749 962022057223489725191203)
              ·
                refine ⟨1443033085835234587786805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962022057223489725191203 1443033085835234587786805)
                ·
                  refine ⟨135284351797053242605013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1443033085835234587786805 135284351797053242605013)
                  ·
                    rfl

theorem cell22_1185594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_1185594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185594 prefixEnd_1185594 := by exact prefixLift 1185594
  have htrace : WordTrace (prefixWord ++ tailWord_1185594) baseStart_1185594 baseEnd_1185594 := by
    simpa [prefixWord, tailWord_1185594, baseEnd_1185594] using wordTrace_append hprefix tailTrace_1185594
  have hstable : (prefixWord ++ tailWord_1185594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185594).length < 2 ^ (prefixWord ++ tailWord_1185594).sum := by decide
  have hdescent : baseEnd_1185594 < baseStart_1185594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185605 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 8]
def baseStart_1185605 : Nat := 118140960795 + 1185605 * 2 ^ 59
def prefixEnd_1185605 : Nat := 4983230072969 + 3 ^ 40 * 1185605 * 2
def baseEnd_1185605 : Nat := 135285606971986455263335

theorem tailTrace_1185605 : CollatzResearch.WordTrace tailWord_1185605 prefixEnd_1185605 135285606971986455263335 := by
  unfold tailWord_1185605
  simp only [CollatzResearch.WordTrace]
  refine ⟨43242566869763045058438269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28828377913175363372292179 43242566869763045058438269)
  ·
    refine ⟨16215962576161141896914351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43242566869763045058438269 16215962576161141896914351)
    ·
      refine ⟨24323943864241712845371527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16215962576161141896914351 24323943864241712845371527)
      ·
        refine ⟨36485915796362569268057291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24323943864241712845371527 36485915796362569268057291)
        ·
          refine ⟨54728873694543853902085937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36485915796362569268057291 54728873694543853902085937)
          ·
            refine ⟨41046655270907890426564453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54728873694543853902085937 41046655270907890426564453)
            ·
              refine ⟨7696247863295229454980835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41046655270907890426564453 7696247863295229454980835)
              ·
                refine ⟨11544371794942844182471253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696247863295229454980835 11544371794942844182471253)
                ·
                  refine ⟨135285606971986455263335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11544371794942844182471253 135285606971986455263335)
                  ·
                    rfl

theorem cell22_1185605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_1185605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185605 prefixEnd_1185605 := by exact prefixLift 1185605
  have htrace : WordTrace (prefixWord ++ tailWord_1185605) baseStart_1185605 baseEnd_1185605 := by
    simpa [prefixWord, tailWord_1185605, baseEnd_1185605] using wordTrace_append hprefix tailTrace_1185605
  have hstable : (prefixWord ++ tailWord_1185605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185605).length < 2 ^ (prefixWord ++ tailWord_1185605).sum := by decide
  have hdescent : baseEnd_1185605 < baseStart_1185605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185639 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 4]
def baseStart_1185639 : Nat := 118140960795 + 1185639 * 2 ^ 59
def prefixEnd_1185639 : Nat := 4983230072969 + 3 ^ 40 * 1185639 * 2
def baseEnd_1185639 : Nat := 135289486603598203479967

theorem tailTrace_1185639 : CollatzResearch.WordTrace tailWord_1185639 prefixEnd_1185639 135289486603598203479967 := by
  unfold tailWord_1185639
  simp only [CollatzResearch.WordTrace]
  refine ⟨43243806951639868865175971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28829204634426579243450647 43243806951639868865175971)
  ·
    refine ⟨64865710427459803297763957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43243806951639868865175971 64865710427459803297763957)
    ·
      refine ⟨6081160352574356559165371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64865710427459803297763957 6081160352574356559165371)
      ·
        refine ⟨9121740528861534838748057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081160352574356559165371 9121740528861534838748057)
        ·
          refine ⟨6841305396646151129061043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9121740528861534838748057 6841305396646151129061043)
          ·
            refine ⟨10261958094969226693591565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6841305396646151129061043 10261958094969226693591565)
            ·
              refine ⟨3848234285613460010096837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10261958094969226693591565 3848234285613460010096837)
              ·
                refine ⟨721543928552523751893157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3848234285613460010096837 721543928552523751893157)
                ·
                  refine ⟨135289486603598203479967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721543928552523751893157 135289486603598203479967)
                  ·
                    rfl

theorem cell22_1185639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 4].length) (baseStart_1185639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185639 prefixEnd_1185639 := by exact prefixLift 1185639
  have htrace : WordTrace (prefixWord ++ tailWord_1185639) baseStart_1185639 baseEnd_1185639 := by
    simpa [prefixWord, tailWord_1185639, baseEnd_1185639] using wordTrace_append hprefix tailTrace_1185639
  have hstable : (prefixWord ++ tailWord_1185639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185639).length < 2 ^ (prefixWord ++ tailWord_1185639).sum := by decide
  have hdescent : baseEnd_1185639 < baseStart_1185639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185750 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1185750 : Nat := 118140960795 + 1185750 * 2 ^ 59
def prefixEnd_1185750 : Nat := 4983230072969 + 3 ^ 40 * 1185750 * 2
def baseEnd_1185750 : Nat := 405906457379227320914561

theorem tailTrace_1185750 : CollatzResearch.WordTrace tailWord_1185750 prefixEnd_1185750 405906457379227320914561 := by
  unfold tailWord_1185750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702990965889858426404169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28831903636158489881644469 2702990965889858426404169)
  ·
    refine ⟨2027243224417393819803127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2702990965889858426404169 2027243224417393819803127)
    ·
      refine ⟨3040864836626090729704691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027243224417393819803127 3040864836626090729704691)
      ·
        refine ⟨4561297254939136094557037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040864836626090729704691 4561297254939136094557037)
        ·
          refine ⟨1710486470602176035458889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4561297254939136094557037 1710486470602176035458889)
          ·
            refine ⟨1282864852951632026594167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710486470602176035458889 1282864852951632026594167)
            ·
              refine ⟨1924297279427448039891251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282864852951632026594167 1924297279427448039891251)
              ·
                refine ⟨2886445919141172059836877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924297279427448039891251 2886445919141172059836877)
                ·
                  refine ⟨1082417219677939522438829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2886445919141172059836877 1082417219677939522438829)
                  ·
                    refine ⟨405906457379227320914561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082417219677939522438829 405906457379227320914561)
                    ·
                      rfl

theorem cell22_1185750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1185750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185750 prefixEnd_1185750 := by exact prefixLift 1185750
  have htrace : WordTrace (prefixWord ++ tailWord_1185750) baseStart_1185750 baseEnd_1185750 := by
    simpa [prefixWord, tailWord_1185750, baseEnd_1185750] using wordTrace_append hprefix tailTrace_1185750
  have hstable : (prefixWord ++ tailWord_1185750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185750).length < 2 ^ (prefixWord ++ tailWord_1185750).sum := by decide
  have hdescent : baseEnd_1185750 < baseStart_1185750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185772 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1185772 : Nat := 118140960795 + 1185772 * 2 ^ 59
def prefixEnd_1185772 : Nat := 4983230072969 + 3 ^ 40 * 1185772 * 2
def baseEnd_1185772 : Nat := 405913988428826596864493

theorem tailTrace_1185772 : CollatzResearch.WordTrace tailWord_1185772 prefixEnd_1185772 405913988428826596864493 := by
  unfold tailWord_1185772
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624328930079016289883785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28832438573438688386511713 21624328930079016289883785)
  ·
    refine ⟨16218246697559262217412839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21624328930079016289883785 16218246697559262217412839)
    ·
      refine ⟨24327370046338893326119259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16218246697559262217412839 24327370046338893326119259)
      ·
        refine ⟨36491055069508339989178889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24327370046338893326119259 36491055069508339989178889)
        ·
          refine ⟨27368291302131254991884167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36491055069508339989178889 27368291302131254991884167)
          ·
            refine ⟨41052436953196882487826251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27368291302131254991884167 41052436953196882487826251)
            ·
              refine ⟨61578655429795323731739377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41052436953196882487826251 61578655429795323731739377)
              ·
                refine ⟨46183991572346492798804533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61578655429795323731739377 46183991572346492798804533)
                ·
                  refine ⟨4329749209907483699887925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46183991572346492798804533 4329749209907483699887925)
                  ·
                    refine ⟨405913988428826596864493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4329749209907483699887925 405913988428826596864493)
                    ·
                      rfl

theorem cell22_1185772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1185772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185772 prefixEnd_1185772 := by exact prefixLift 1185772
  have htrace : WordTrace (prefixWord ++ tailWord_1185772) baseStart_1185772 baseEnd_1185772 := by
    simpa [prefixWord, tailWord_1185772, baseEnd_1185772] using wordTrace_append hprefix tailTrace_1185772
  have hstable : (prefixWord ++ tailWord_1185772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185772).length < 2 ^ (prefixWord ++ tailWord_1185772).sum := by decide
  have hdescent : baseEnd_1185772 < baseStart_1185772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185787 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_1185787 : Nat := 118140960795 + 1185787 * 2 ^ 59
def prefixEnd_1185787 : Nat := 4983230072969 + 3 ^ 40 * 1185787 * 2
def baseEnd_1185787 : Nat := 405919123235371557739447

theorem tailTrace_1185787 : CollatzResearch.WordTrace tailWord_1185787 prefixEnd_1185787 405919123235371557739447 := by
  unfold tailWord_1185787
  simp only [CollatzResearch.WordTrace]
  refine ⟨43249204955103690141563615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28832803303402460094375743 43249204955103690141563615)
  ·
    refine ⟨64873807432655535212345423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43249204955103690141563615 64873807432655535212345423)
    ·
      refine ⟨97310711148983302818518135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64873807432655535212345423 97310711148983302818518135)
      ·
        refine ⟨145966066723474954227777203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97310711148983302818518135 145966066723474954227777203)
        ·
          refine ⟨218949100085212431341665805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145966066723474954227777203 218949100085212431341665805)
          ·
            refine ⟨82105912531954661753124677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218949100085212431341665805 82105912531954661753124677)
            ·
              refine ⟨15394858599741499078710877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82105912531954661753124677 15394858599741499078710877)
              ·
                refine ⟨5773071974903062154516579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15394858599741499078710877 5773071974903062154516579)
                ·
                  refine ⟨8659607962354593231774869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773071974903062154516579 8659607962354593231774869)
                  ·
                    refine ⟨405919123235371557739447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8659607962354593231774869 405919123235371557739447)
                    ·
                      rfl

theorem cell22_1185787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_1185787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185787 prefixEnd_1185787 := by exact prefixLift 1185787
  have htrace : WordTrace (prefixWord ++ tailWord_1185787) baseStart_1185787 baseEnd_1185787 := by
    simpa [prefixWord, tailWord_1185787, baseEnd_1185787] using wordTrace_append hprefix tailTrace_1185787
  have hstable : (prefixWord ++ tailWord_1185787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185787).length < 2 ^ (prefixWord ++ tailWord_1185787).sum := by decide
  have hdescent : baseEnd_1185787 < baseStart_1185787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185789 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1185789 : Nat := 118140960795 + 1185789 * 2 ^ 59
def prefixEnd_1185789 : Nat := 4983230072969 + 3 ^ 40 * 1185789 * 2
def baseEnd_1185789 : Nat := 405919807876244219189441

theorem tailTrace_1185789 : CollatzResearch.WordTrace tailWord_1185789 prefixEnd_1185789 405919807876244219189441 := by
  unfold tailWord_1185789
  simp only [CollatzResearch.WordTrace]
  refine ⟨43249277901096444483136421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28832851934064296322090947 43249277901096444483136421)
  ·
    refine ⟨8109239606455583340588079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43249277901096444483136421 8109239606455583340588079)
    ·
      refine ⟨12163859409683375010882119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8109239606455583340588079 12163859409683375010882119)
      ·
        refine ⟨18245789114525062516323179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12163859409683375010882119 18245789114525062516323179)
        ·
          refine ⟨27368683671787593774484769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18245789114525062516323179 27368683671787593774484769)
          ·
            refine ⟨20526512753840695330863577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27368683671787593774484769 20526512753840695330863577)
            ·
              refine ⟨15394884565380521498147683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20526512753840695330863577 15394884565380521498147683)
              ·
                refine ⟨23092326848070782247221525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15394884565380521498147683 23092326848070782247221525)
                ·
                  refine ⟨1082452821003317917838509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23092326848070782247221525 1082452821003317917838509)
                  ·
                    refine ⟨405919807876244219189441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082452821003317917838509 405919807876244219189441)
                    ·
                      rfl

theorem cell22_1185789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1185789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185789 prefixEnd_1185789 := by exact prefixLift 1185789
  have htrace : WordTrace (prefixWord ++ tailWord_1185789) baseStart_1185789 baseEnd_1185789 := by
    simpa [prefixWord, tailWord_1185789, baseEnd_1185789] using wordTrace_append hprefix tailTrace_1185789
  have hstable : (prefixWord ++ tailWord_1185789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185789).length < 2 ^ (prefixWord ++ tailWord_1185789).sum := by decide
  have hdescent : baseEnd_1185789 < baseStart_1185789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185802 : List Nat := [3, 1, 2, 2, 14]
def baseStart_1185802 : Nat := 118140960795 + 1185802 * 2 ^ 59
def prefixEnd_1185802 : Nat := 4983230072969 + 3 ^ 40 * 1185802 * 2
def baseEnd_1185802 : Nat := 1670470197703360158907

theorem tailTrace_1185802 : CollatzResearch.WordTrace tailWord_1185802 prefixEnd_1185802 1670470197703360158907 := by
  unfold tailWord_1185802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10812438012512336925839915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28833168033366231802239773 10812438012512336925839915)
  ·
    refine ⟨16218657018768505388759873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10812438012512336925839915 16218657018768505388759873)
    ·
      refine ⟨12163992764076379041569905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16218657018768505388759873 12163992764076379041569905)
      ·
        refine ⟨9122994573057284281177429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12163992764076379041569905 9122994573057284281177429)
        ·
          refine ⟨1670470197703360158907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 9122994573057284281177429 1670470197703360158907)
          ·
            rfl

theorem cell22_1185802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 14].length) (baseStart_1185802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185802 prefixEnd_1185802 := by exact prefixLift 1185802
  have htrace : WordTrace (prefixWord ++ tailWord_1185802) baseStart_1185802 baseEnd_1185802 := by
    simpa [prefixWord, tailWord_1185802, baseEnd_1185802] using wordTrace_append hprefix tailTrace_1185802
  have hstable : (prefixWord ++ tailWord_1185802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185802).length < 2 ^ (prefixWord ++ tailWord_1185802).sum := by decide
  have hdescent : baseEnd_1185802 < baseStart_1185802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185804 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1185804 : Nat := 118140960795 + 1185804 * 2 ^ 59
def prefixEnd_1185804 : Nat := 4983230072969 + 3 ^ 40 * 1185804 * 2
def baseEnd_1185804 : Nat := 405924942682789180064395

theorem tailTrace_1185804 : CollatzResearch.WordTrace tailWord_1185804 prefixEnd_1185804 405924942682789180064395 := by
  unfold tailWord_1185804
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624912498021051022466233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28833216664028068029954977 21624912498021051022466233)
  ·
    refine ⟨16218684373515788266849675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21624912498021051022466233 16218684373515788266849675)
    ·
      refine ⟨24328026560273682400274513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16218684373515788266849675 24328026560273682400274513)
      ·
        refine ⟨18246019920205261800205885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24328026560273682400274513 18246019920205261800205885)
        ·
          refine ⟨6842257470076973175077207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18246019920205261800205885 6842257470076973175077207)
          ·
            refine ⟨10263386205115459762615811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842257470076973175077207 10263386205115459762615811)
            ·
              refine ⟨15395079307673189643923717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10263386205115459762615811 15395079307673189643923717)
              ·
                refine ⟨2886577370188723058235697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15395079307673189643923717 2886577370188723058235697)
                ·
                  refine ⟨2164933027641542293676773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886577370188723058235697 2164933027641542293676773)
                  ·
                    refine ⟨405924942682789180064395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2164933027641542293676773 405924942682789180064395)
                    ·
                      rfl

theorem cell22_1185804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1185804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185804 prefixEnd_1185804 := by exact prefixLift 1185804
  have htrace : WordTrace (prefixWord ++ tailWord_1185804) baseStart_1185804 baseEnd_1185804 := by
    simpa [prefixWord, tailWord_1185804, baseEnd_1185804] using wordTrace_append hprefix tailTrace_1185804
  have hstable : (prefixWord ++ tailWord_1185804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185804).length < 2 ^ (prefixWord ++ tailWord_1185804).sum := by decide
  have hdescent : baseEnd_1185804 < baseStart_1185804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185817 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1185817 : Nat := 118140960795 + 1185817 * 2 ^ 59
def prefixEnd_1185817 : Nat := 4983230072969 + 3 ^ 40 * 1185817 * 2
def baseEnd_1185817 : Nat := 405929392848461479489355

theorem tailTrace_1185817 : CollatzResearch.WordTrace tailWord_1185817 prefixEnd_1185817 405929392848461479489355 := by
  unfold tailWord_1185817
  simp only [CollatzResearch.WordTrace]
  refine ⟨43250299144995005265155705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28833532763330003510103803 43250299144995005265155705)
  ·
    refine ⟨32437724358746253948866779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43250299144995005265155705 32437724358746253948866779)
    ·
      refine ⟨48656586538119380923300169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32437724358746253948866779 48656586538119380923300169)
      ·
        refine ⟨36492439903589535692475127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48656586538119380923300169 36492439903589535692475127)
        ·
          refine ⟨54738659855384303538712691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36492439903589535692475127 54738659855384303538712691)
          ·
            refine ⟨82107989783076455308069037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54738659855384303538712691 82107989783076455308069037)
            ·
              refine ⟨30790496168653670740525889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82107989783076455308069037 30790496168653670740525889)
              ·
                refine ⟨23092872126490253055394417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30790496168653670740525889 23092872126490253055394417)
                ·
                  refine ⟨17319654094867689791545813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23092872126490253055394417 17319654094867689791545813)
                  ·
                    refine ⟨405929392848461479489355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17319654094867689791545813 405929392848461479489355)
                    ·
                      rfl

theorem cell22_1185817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1185817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185817 prefixEnd_1185817 := by exact prefixLift 1185817
  have htrace : WordTrace (prefixWord ++ tailWord_1185817) baseStart_1185817 baseEnd_1185817 := by
    simpa [prefixWord, tailWord_1185817, baseEnd_1185817] using wordTrace_append hprefix tailTrace_1185817
  have hstable : (prefixWord ++ tailWord_1185817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185817).length < 2 ^ (prefixWord ++ tailWord_1185817).sum := by decide
  have hdescent : baseEnd_1185817 < baseStart_1185817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185838 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1185838 : Nat := 118140960795 + 1185838 * 2 ^ 59
def prefixEnd_1185838 : Nat := 4983230072969 + 3 ^ 40 * 1185838 * 2
def baseEnd_1185838 : Nat := 405936581577624424714291

theorem tailTrace_1185838 : CollatzResearch.WordTrace tailWord_1185838 prefixEnd_1185838 405936581577624424714291 := by
  unfold tailWord_1185838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406383134739865731458771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28834043385279283901113445 5406383134739865731458771)
  ·
    refine ⟨8109574702109798597188157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406383134739865731458771 8109574702109798597188157)
    ·
      refine ⟨3041090513291174473945559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8109574702109798597188157 3041090513291174473945559)
      ·
        refine ⟨4561635769936761710918339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041090513291174473945559 4561635769936761710918339)
        ·
          refine ⟨6842453654905142566377509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561635769936761710918339 6842453654905142566377509)
          ·
            refine ⟨1282960060294714231195783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6842453654905142566377509 1282960060294714231195783)
            ·
              refine ⟨1924440090442071346793675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282960060294714231195783 1924440090442071346793675)
              ·
                refine ⟨2886660135663107020190513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924440090442071346793675 2886660135663107020190513)
                ·
                  refine ⟨2164995101747330265142885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886660135663107020190513 2164995101747330265142885)
                  ·
                    refine ⟨405936581577624424714291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2164995101747330265142885 405936581577624424714291)
                    ·
                      rfl

theorem cell22_1185838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1185838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185838 prefixEnd_1185838 := by exact prefixLift 1185838
  have htrace : WordTrace (prefixWord ++ tailWord_1185838) baseStart_1185838 baseEnd_1185838 := by
    simpa [prefixWord, tailWord_1185838, baseEnd_1185838] using wordTrace_append hprefix tailTrace_1185838
  have hstable : (prefixWord ++ tailWord_1185838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185838).length < 2 ^ (prefixWord ++ tailWord_1185838).sum := by decide
  have hdescent : baseEnd_1185838 < baseStart_1185838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185864 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_1185864 : Nat := 118140960795 + 1185864 * 2 ^ 59
def prefixEnd_1185864 : Nat := 4983230072969 + 3 ^ 40 * 1185864 * 2
def baseEnd_1185864 : Nat := 135315160636323007854737

theorem tailTrace_1185864 : CollatzResearch.WordTrace tailWord_1185864 prefixEnd_1185864 135315160636323007854737 := by
  unfold tailWord_1185864
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626006687912366146058323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28834675583883154861411097 21626006687912366146058323)
  ·
    refine ⟨32439010031868549219087485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21626006687912366146058323 32439010031868549219087485)
    ·
      refine ⟨12164628761950705957157807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32439010031868549219087485 12164628761950705957157807)
      ·
        refine ⟨18246943142926058935736711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12164628761950705957157807 18246943142926058935736711)
        ·
          refine ⟨27370414714389088403605067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18246943142926058935736711 27370414714389088403605067)
          ·
            refine ⟨41055622071583632605407601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27370414714389088403605067 41055622071583632605407601)
            ·
              refine ⟨30791716553687724454055701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41055622071583632605407601 30791716553687724454055701)
              ·
                refine ⟨1443361713454112083783861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30791716553687724454055701 1443361713454112083783861)
                ·
                  refine ⟨135315160636323007854737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1443361713454112083783861 135315160636323007854737)
                  ·
                    rfl

theorem cell22_1185864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_1185864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185864 prefixEnd_1185864 := by exact prefixLift 1185864
  have htrace : WordTrace (prefixWord ++ tailWord_1185864) baseStart_1185864 baseEnd_1185864 := by
    simpa [prefixWord, tailWord_1185864, baseEnd_1185864] using wordTrace_append hprefix tailTrace_1185864
  have hstable : (prefixWord ++ tailWord_1185864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185864).length < 2 ^ (prefixWord ++ tailWord_1185864).sum := by decide
  have hdescent : baseEnd_1185864 < baseStart_1185864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185868 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_1185868 : Nat := 118140960795 + 1185868 * 2 ^ 59
def prefixEnd_1185868 : Nat := 4983230072969 + 3 ^ 40 * 1185868 * 2
def baseEnd_1185868 : Nat := 405946851190714346464199

theorem tailTrace_1185868 : CollatzResearch.WordTrace tailWord_1185868 prefixEnd_1185868 405946851190714346464199 := by
  unfold tailWord_1185868
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626079633905120487631129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28834772845206827316841505 21626079633905120487631129)
  ·
    refine ⟨16219559725428840365723347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21626079633905120487631129 16219559725428840365723347)
    ·
      refine ⟨24329339588143260548585021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16219559725428840365723347 24329339588143260548585021)
      ·
        refine ⟨9123502345553722705719383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24329339588143260548585021 9123502345553722705719383)
        ·
          refine ⟨13685253518330584058579075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123502345553722705719383 13685253518330584058579075)
          ·
            refine ⟨20527880277495876087868613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685253518330584058579075 20527880277495876087868613)
            ·
              refine ⟨3848977552030476766475365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20527880277495876087868613 3848977552030476766475365)
              ·
                refine ⟨721683291005714393714131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3848977552030476766475365 721683291005714393714131)
                ·
                  refine ⟨1082524936508571590571197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721683291005714393714131 1082524936508571590571197)
                  ·
                    refine ⟨405946851190714346464199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082524936508571590571197 405946851190714346464199)
                    ·
                      rfl

theorem cell22_1185868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_1185868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185868 prefixEnd_1185868 := by exact prefixLift 1185868
  have htrace : WordTrace (prefixWord ++ tailWord_1185868) baseStart_1185868 baseEnd_1185868 := by
    simpa [prefixWord, tailWord_1185868, baseEnd_1185868] using wordTrace_append hprefix tailTrace_1185868
  have hstable : (prefixWord ++ tailWord_1185868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185868).length < 2 ^ (prefixWord ++ tailWord_1185868).sum := by decide
  have hdescent : baseEnd_1185868 < baseStart_1185868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185879 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_1185879 : Nat := 118140960795 + 1185879 * 2 ^ 59
def prefixEnd_1185879 : Nat := 4983230072969 + 3 ^ 40 * 1185879 * 2
def baseEnd_1185879 : Nat := 405950616715513984439165

theorem tailTrace_1185879 : CollatzResearch.WordTrace tailWord_1185879 prefixEnd_1185879 405950616715513984439165 := by
  unfold tailWord_1185879
  simp only [CollatzResearch.WordTrace]
  refine ⟨43252560470770389853912691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28835040313846926569275127 43252560470770389853912691)
  ·
    refine ⟨64878840706155584780869037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43252560470770389853912691 64878840706155584780869037)
    ·
      refine ⟨24329565264808344292825889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64878840706155584780869037 24329565264808344292825889)
      ·
        refine ⟨18247173948606258219619417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24329565264808344292825889 18247173948606258219619417)
        ·
          refine ⟨13685380461454693664714563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18247173948606258219619417 13685380461454693664714563)
          ·
            refine ⟨20528070692182040497071845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685380461454693664714563 20528070692182040497071845)
            ·
              refine ⟨3849013254784132593200971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20528070692182040497071845 3849013254784132593200971)
              ·
                refine ⟨5773519882176198889801457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849013254784132593200971 5773519882176198889801457)
                ·
                  refine ⟨4330139911632149167351093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773519882176198889801457 4330139911632149167351093)
                  ·
                    refine ⟨405950616715513984439165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4330139911632149167351093 405950616715513984439165)
                    ·
                      rfl

theorem cell22_1185879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_1185879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185879 prefixEnd_1185879 := by exact prefixLift 1185879
  have htrace : WordTrace (prefixWord ++ tailWord_1185879) baseStart_1185879 baseEnd_1185879 := by
    simpa [prefixWord, tailWord_1185879, baseEnd_1185879] using wordTrace_append hprefix tailTrace_1185879
  have hstable : (prefixWord ++ tailWord_1185879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185879).length < 2 ^ (prefixWord ++ tailWord_1185879).sum := by decide
  have hdescent : baseEnd_1185879 < baseStart_1185879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185881 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 5]
def baseStart_1185881 : Nat := 118140960795 + 1185881 * 2 ^ 59
def prefixEnd_1185881 : Nat := 4983230072969 + 3 ^ 40 * 1185881 * 2
def baseEnd_1185881 : Nat := 135317100452128881963053

theorem tailTrace_1185881 : CollatzResearch.WordTrace tailWord_1185881 prefixEnd_1185881 135317100452128881963053 := by
  unfold tailWord_1185881
  simp only [CollatzResearch.WordTrace]
  refine ⟨43252633416763144195485497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28835088944508762796990331 43252633416763144195485497)
  ·
    refine ⟨32439475062572358146614123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43252633416763144195485497 32439475062572358146614123)
    ·
      refine ⟨48659212593858537219921185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32439475062572358146614123 48659212593858537219921185)
      ·
        refine ⟨36494409445393902914940889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48659212593858537219921185 36494409445393902914940889)
        ·
          refine ⟨27370807084045427186205667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36494409445393902914940889 27370807084045427186205667)
          ·
            refine ⟨41056210626068140779308501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27370807084045427186205667 41056210626068140779308501)
            ·
              refine ⟨962254936548472049515043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41056210626068140779308501 962254936548472049515043)
              ·
                refine ⟨1443382404822708074272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962254936548472049515043 1443382404822708074272565)
                ·
                  refine ⟨135317100452128881963053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1443382404822708074272565 135317100452128881963053)
                  ·
                    rfl

theorem cell22_1185881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_1185881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185881 prefixEnd_1185881 := by exact prefixLift 1185881
  have htrace : WordTrace (prefixWord ++ tailWord_1185881) baseStart_1185881 baseEnd_1185881 := by
    simpa [prefixWord, tailWord_1185881, baseEnd_1185881] using wordTrace_append hprefix tailTrace_1185881
  have hstable : (prefixWord ++ tailWord_1185881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185881).length < 2 ^ (prefixWord ++ tailWord_1185881).sum := by decide
  have hdescent : baseEnd_1185881 < baseStart_1185881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185911 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 1, 4]
def baseStart_1185911 : Nat := 118140960795 + 1185911 * 2 ^ 59
def prefixEnd_1185911 : Nat := 4983230072969 + 3 ^ 40 * 1185911 * 2
def baseEnd_1185911 : Nat := 405961570969476567639067

theorem tailTrace_1185911 : CollatzResearch.WordTrace tailWord_1185911 prefixEnd_1185911 405961570969476567639067 := by
  unfold tailWord_1185911
  simp only [CollatzResearch.WordTrace]
  refine ⟨43253727606654459319077587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28835818404436306212718391 43253727606654459319077587)
  ·
    refine ⟨64880591409981688978616381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43253727606654459319077587 64880591409981688978616381)
    ·
      refine ⟨24330221778743133366981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64880591409981688978616381 24330221778743133366981143)
      ·
        refine ⟨36495332668114700050471715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24330221778743133366981143 36495332668114700050471715)
        ·
          refine ⟨54742999002172050075707573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36495332668114700050471715 54742999002172050075707573)
          ·
            refine ⟨5132156156453629694597585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54742999002172050075707573 5132156156453629694597585)
            ·
              refine ⟨3849117117340222270948189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132156156453629694597585 3849117117340222270948189)
              ·
                refine ⟨1443418919002583351605571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849117117340222270948189 1443418919002583351605571)
                ·
                  refine ⟨2165128378503875027408357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443418919002583351605571 2165128378503875027408357)
                  ·
                    refine ⟨405961570969476567639067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165128378503875027408357 405961570969476567639067)
                    ·
                      rfl

theorem cell22_1185911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_1185911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185911 prefixEnd_1185911 := by exact prefixLift 1185911
  have htrace : WordTrace (prefixWord ++ tailWord_1185911) baseStart_1185911 baseEnd_1185911 := by
    simpa [prefixWord, tailWord_1185911, baseEnd_1185911] using wordTrace_append hprefix tailTrace_1185911
  have hstable : (prefixWord ++ tailWord_1185911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185911).length < 2 ^ (prefixWord ++ tailWord_1185911).sum := by decide
  have hdescent : baseEnd_1185911 < baseStart_1185911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185939 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_1185939 : Nat := 118140960795 + 1185939 * 2 ^ 59
def prefixEnd_1185939 : Nat := 4983230072969 + 3 ^ 40 * 1185939 * 2
def baseEnd_1185939 : Nat := 405971155941693827938981

theorem tailTrace_1185939 : CollatzResearch.WordTrace tailWord_1185939 prefixEnd_1185939 405971155941693827938981 := by
  unfold tailWord_1185939
  simp only [CollatzResearch.WordTrace]
  refine ⟨43254748850553020101096871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28836499233702013400731247 43254748850553020101096871)
  ·
    refine ⟨64882123275829530151645307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43254748850553020101096871 64882123275829530151645307)
    ·
      refine ⟨97323184913744295227467961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64882123275829530151645307 97323184913744295227467961)
      ·
        refine ⟨72992388685308221420600971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97323184913744295227467961 72992388685308221420600971)
        ·
          refine ⟨109488583027962332130901457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72992388685308221420600971 109488583027962332130901457)
          ·
            refine ⟨82116437270971749098176093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109488583027962332130901457 82116437270971749098176093)
            ·
              refine ⟨30793663976614405911816035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82116437270971749098176093 30793663976614405911816035)
              ·
                refine ⟨46190495964921608867724053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30793663976614405911816035 46190495964921608867724053)
                ·
                  refine ⟨2165179498355700415674565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46190495964921608867724053 2165179498355700415674565)
                  ·
                    refine ⟨405971155941693827938981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165179498355700415674565 405971155941693827938981)
                    ·
                      rfl

theorem cell22_1185939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_1185939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185939 prefixEnd_1185939 := by exact prefixLift 1185939
  have htrace : WordTrace (prefixWord ++ tailWord_1185939) baseStart_1185939 baseEnd_1185939 := by
    simpa [prefixWord, tailWord_1185939, baseEnd_1185939] using wordTrace_append hprefix tailTrace_1185939
  have hstable : (prefixWord ++ tailWord_1185939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185939).length < 2 ^ (prefixWord ++ tailWord_1185939).sum := by decide
  have hdescent : baseEnd_1185939 < baseStart_1185939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185962 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1185962 : Nat := 118140960795 + 1185962 * 2 ^ 59
def prefixEnd_1185962 : Nat := 4983230072969 + 3 ^ 40 * 1185962 * 2
def baseEnd_1185962 : Nat := 405979029311729434613911

theorem tailTrace_1185962 : CollatzResearch.WordTrace tailWord_1185962 prefixEnd_1185962 405979029311729434613911 := by
  unfold tailWord_1185962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813896932367423757296035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28837058486313130019456093 10813896932367423757296035)
  ·
    refine ⟨16220845398551135635944053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10813896932367423757296035 16220845398551135635944053)
    ·
      refine ⟨1520704256114168965869755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16220845398551135635944053 1520704256114168965869755)
      ·
        refine ⟨2281056384171253448804633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520704256114168965869755 2281056384171253448804633)
        ·
          refine ⟨1710792288128440086603475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281056384171253448804633 1710792288128440086603475)
          ·
            refine ⟨2566188432192660129905213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710792288128440086603475 2566188432192660129905213)
            ·
              refine ⟨962320662072247548714455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2566188432192660129905213 962320662072247548714455)
              ·
                refine ⟨1443480993108371323071683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962320662072247548714455 1443480993108371323071683)
                ·
                  refine ⟨2165221489662556984607525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443480993108371323071683 2165221489662556984607525)
                  ·
                    refine ⟨405979029311729434613911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165221489662556984607525 405979029311729434613911)
                    ·
                      rfl

theorem cell22_1185962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1185962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185962 prefixEnd_1185962 := by exact prefixLift 1185962
  have htrace : WordTrace (prefixWord ++ tailWord_1185962) baseStart_1185962 baseEnd_1185962 := by
    simpa [prefixWord, tailWord_1185962, baseEnd_1185962] using wordTrace_append hprefix tailTrace_1185962
  have hstable : (prefixWord ++ tailWord_1185962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185962).length < 2 ^ (prefixWord ++ tailWord_1185962).sum := by decide
  have hdescent : baseEnd_1185962 < baseStart_1185962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185988 : List Nat := [2, 3, 3, 1, 2, 3, 1, 7]
def baseStart_1185988 : Nat := 118140960795 + 1185988 * 2 ^ 59
def prefixEnd_1185988 : Nat := 4983230072969 + 3 ^ 40 * 1185988 * 2
def baseEnd_1185988 : Nat := 45109769960341559273759

theorem tailTrace_1185988 : CollatzResearch.WordTrace tailWord_1185988 prefixEnd_1185988 45109769960341559273759 := by
  unfold tailWord_1185988
  simp only [CollatzResearch.WordTrace]
  refine ⟨21628268013687750734815309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28837690684917000979753745 21628268013687750734815309)
  ·
    refine ⟨8110600505132906525555741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21628268013687750734815309 8110600505132906525555741)
    ·
      refine ⟨3041475189424839947083403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8110600505132906525555741 3041475189424839947083403)
      ·
        refine ⟨4562212784137259920625105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041475189424839947083403 4562212784137259920625105)
        ·
          refine ⟨3421659588102944940468829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4562212784137259920625105 3421659588102944940468829)
          ·
            refine ⟨1283122345538604352675811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421659588102944940468829 1283122345538604352675811)
            ·
              refine ⟨1924683518307906529013717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283122345538604352675811 1924683518307906529013717)
              ·
                refine ⟨45109769960341559273759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1924683518307906529013717 45109769960341559273759)
                ·
                  rfl

theorem cell22_1185988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_1185988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1185988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1185988 prefixEnd_1185988 := by exact prefixLift 1185988
  have htrace : WordTrace (prefixWord ++ tailWord_1185988) baseStart_1185988 baseEnd_1185988 := by
    simpa [prefixWord, tailWord_1185988, baseEnd_1185988] using wordTrace_append hprefix tailTrace_1185988
  have hstable : (prefixWord ++ tailWord_1185988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185988).length < 2 ^ (prefixWord ++ tailWord_1185988).sum := by decide
  have hdescent : baseEnd_1185988 < baseStart_1185988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186031 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_1186031 : Nat := 118140960795 + 1186031 * 2 ^ 59
def prefixEnd_1186031 : Nat := 4983230072969 + 3 ^ 40 * 1186031 * 2
def baseEnd_1186031 : Nat := 406002649421836254638699

theorem tailTrace_1186031 : CollatzResearch.WordTrace tailWord_1186031 prefixEnd_1186031 406002649421836254638699 := by
  unfold tailWord_1186031
  simp only [CollatzResearch.WordTrace]
  refine ⟨43258104366219719813445947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28838736244146479875630631 43258104366219719813445947)
  ·
    refine ⟨64887156549329579720168921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43258104366219719813445947 64887156549329579720168921)
    ·
      refine ⟨48665367411997184790126691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64887156549329579720168921 48665367411997184790126691)
      ·
        refine ⟨72998051117995777185190037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48665367411997184790126691 72998051117995777185190037)
        ·
          refine ⟨3421783646156052055555783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72998051117995777185190037 3421783646156052055555783)
          ·
            refine ⟨5132675469234078083333675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421783646156052055555783 5132675469234078083333675)
            ·
              refine ⟨7699013203851117125000513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132675469234078083333675 7699013203851117125000513)
              ·
                refine ⟨5774259902888337843750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7699013203851117125000513 5774259902888337843750385)
                ·
                  refine ⟨4330694927166253382812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5774259902888337843750385 4330694927166253382812789)
                  ·
                    refine ⟨406002649421836254638699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4330694927166253382812789 406002649421836254638699)
                    ·
                      rfl

theorem cell22_1186031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_1186031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186031 prefixEnd_1186031 := by exact prefixLift 1186031
  have htrace : WordTrace (prefixWord ++ tailWord_1186031) baseStart_1186031 baseEnd_1186031 := by
    simpa [prefixWord, tailWord_1186031, baseEnd_1186031] using wordTrace_append hprefix tailTrace_1186031
  have hstable : (prefixWord ++ tailWord_1186031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186031).length < 2 ^ (prefixWord ++ tailWord_1186031).sum := by decide
  have hdescent : baseEnd_1186031 < baseStart_1186031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186076 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1186076 : Nat := 118140960795 + 1186076 * 2 ^ 59
def prefixEnd_1186076 : Nat := 4983230072969 + 3 ^ 40 * 1186076 * 2
def baseEnd_1186076 : Nat := 406018053841471137263561

theorem tailTrace_1186076 : CollatzResearch.WordTrace tailWord_1186076 prefixEnd_1186076 406018053841471137263561 := by
  unfold tailWord_1186076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21629872825528346249417041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28839830434037794999222721 21629872825528346249417041)
  ·
    refine ⟨16222404619146259687062781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21629872825528346249417041 16222404619146259687062781)
    ·
      refine ⟨6083401732179847382648543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16222404619146259687062781 6083401732179847382648543)
      ·
        refine ⟨9125102598269771073972815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083401732179847382648543 9125102598269771073972815)
        ·
          refine ⟨13687653897404656610959223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9125102598269771073972815 13687653897404656610959223)
          ·
            refine ⟨20531480846106984916438835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13687653897404656610959223 20531480846106984916438835)
            ·
              refine ⟨30797221269160477374658253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20531480846106984916438835 30797221269160477374658253)
              ·
                refine ⟨11548957975935179015496845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30797221269160477374658253 11548957975935179015496845)
                ·
                  refine ⟨4330859240975692130811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11548957975935179015496845 4330859240975692130811317)
                  ·
                    refine ⟨406018053841471137263561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4330859240975692130811317 406018053841471137263561)
                    ·
                      rfl

theorem cell22_1186076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1186076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186076 prefixEnd_1186076 := by exact prefixLift 1186076
  have htrace : WordTrace (prefixWord ++ tailWord_1186076) baseStart_1186076 baseEnd_1186076 := by
    simpa [prefixWord, tailWord_1186076, baseEnd_1186076] using wordTrace_append hprefix tailTrace_1186076
  have hstable : (prefixWord ++ tailWord_1186076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186076).length < 2 ^ (prefixWord ++ tailWord_1186076).sum := by decide
  have hdescent : baseEnd_1186076 < baseStart_1186076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186106 : List Nat := [3, 1, 1, 1, 4, 2, 1, 9]
def baseStart_1186106 : Nat := 118140960795 + 1186106 * 2 ^ 59
def prefixEnd_1186106 : Nat := 4983230072969 + 3 ^ 40 * 1186106 * 2
def baseEnd_1186106 : Nat := 45114258161617895445941

theorem tailTrace_1186106 : CollatzResearch.WordTrace tailWord_1186106 prefixEnd_1186106 45114258161617895445941 := by
  unfold tailWord_1186106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815209960237001905606543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28840559893965338414950781 10815209960237001905606543)
  ·
    refine ⟨16222814940355502858409815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10815209960237001905606543 16222814940355502858409815)
    ·
      refine ⟨24334222410533254287614723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222814940355502858409815 24334222410533254287614723)
      ·
        refine ⟨36501333615799881431422085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24334222410533254287614723 36501333615799881431422085)
        ·
          refine ⟨6844000052962477768391641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36501333615799881431422085 6844000052962477768391641)
          ·
            refine ⟨5133000039721858326293731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6844000052962477768391641 5133000039721858326293731)
            ·
              refine ⟨7699500059582787489440597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5133000039721858326293731 7699500059582787489440597)
              ·
                refine ⟨45114258161617895445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7699500059582787489440597 45114258161617895445941)
                ·
                  rfl

theorem cell22_1186106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_1186106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186106 prefixEnd_1186106 := by exact prefixLift 1186106
  have htrace : WordTrace (prefixWord ++ tailWord_1186106) baseStart_1186106 baseEnd_1186106 := by
    simpa [prefixWord, tailWord_1186106, baseEnd_1186106] using wordTrace_append hprefix tailTrace_1186106
  have hstable : (prefixWord ++ tailWord_1186106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186106).length < 2 ^ (prefixWord ++ tailWord_1186106).sum := by decide
  have hdescent : baseEnd_1186106 < baseStart_1186106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186140 : List Nat := [2, 2, 4, 3, 2, 9]
def baseStart_1186140 : Nat := 118140960795 + 1186140 * 2 ^ 59
def prefixEnd_1186140 : Nat := 4983230072969 + 3 ^ 40 * 1186140 * 2
def baseEnd_1186140 : Nat := 5012839041350571650165

theorem tailTrace_1186140 : CollatzResearch.WordTrace tailWord_1186140 prefixEnd_1186140 5012839041350571650165 := by
  unfold tailWord_1186140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21631039961412415714581937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28841386615216554286109249 21631039961412415714581937)
  ·
    refine ⟨16223279971059311785936453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21631039961412415714581937 16223279971059311785936453)
    ·
      refine ⟨3041864994573620959863085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16223279971059311785936453 3041864994573620959863085)
      ·
        refine ⟨1140699372965107859948657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3041864994573620959863085 1140699372965107859948657)
        ·
          refine ⟨855524529723830894961493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140699372965107859948657 855524529723830894961493)
          ·
            refine ⟨5012839041350571650165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 855524529723830894961493 5012839041350571650165)
            ·
              rfl

theorem cell22_1186140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 9].length) (baseStart_1186140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186140 prefixEnd_1186140 := by exact prefixLift 1186140
  have htrace : WordTrace (prefixWord ++ tailWord_1186140) baseStart_1186140 baseEnd_1186140 := by
    simpa [prefixWord, tailWord_1186140, baseEnd_1186140] using wordTrace_append hprefix tailTrace_1186140
  have hstable : (prefixWord ++ tailWord_1186140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186140).length < 2 ^ (prefixWord ++ tailWord_1186140).sum := by decide
  have hdescent : baseEnd_1186140 < baseStart_1186140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186155 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 1, 3]
def baseStart_1186155 : Nat := 118140960795 + 1186155 * 2 ^ 59
def prefixEnd_1186155 : Nat := 4983230072969 + 3 ^ 40 * 1186155 * 2
def baseEnd_1186155 : Nat := 406045097155941264538319

theorem tailTrace_1186155 : CollatzResearch.WordTrace tailWord_1186155 prefixEnd_1186155 406045097155941264538319 := by
  unfold tailWord_1186155
  simp only [CollatzResearch.WordTrace]
  refine ⟨43262627017770488990959919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28841751345180325993973279 43262627017770488990959919)
  ·
    refine ⟨64893940526655733486439879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43262627017770488990959919 64893940526655733486439879)
    ·
      refine ⟨97340910789983600229659819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64893940526655733486439879 97340910789983600229659819)
      ·
        refine ⟨146011366184975400344489729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97340910789983600229659819 146011366184975400344489729)
        ·
          refine ⟨109508524638731550258367297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146011366184975400344489729 109508524638731550258367297)
          ·
            refine ⟨82131393479048662693775473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109508524638731550258367297 82131393479048662693775473)
            ·
              refine ⟨61598545109286497020331605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82131393479048662693775473 61598545109286497020331605)
              ·
                refine ⟨721857950499451136957011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 61598545109286497020331605 721857950499451136957011)
                ·
                  refine ⟨1082786925749176705435517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721857950499451136957011 1082786925749176705435517)
                  ·
                    refine ⟨406045097155941264538319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082786925749176705435517 406045097155941264538319)
                    ·
                      rfl

theorem cell22_1186155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 3].length) (baseStart_1186155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186155 prefixEnd_1186155 := by exact prefixLift 1186155
  have htrace : WordTrace (prefixWord ++ tailWord_1186155) baseStart_1186155 baseEnd_1186155 := by
    simpa [prefixWord, tailWord_1186155, baseEnd_1186155] using wordTrace_append hprefix tailTrace_1186155
  have hstable : (prefixWord ++ tailWord_1186155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186155).length < 2 ^ (prefixWord ++ tailWord_1186155).sum := by decide
  have hdescent : baseEnd_1186155 < baseStart_1186155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186213 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 6]
def baseStart_1186213 : Nat := 118140960795 + 1186213 * 2 ^ 59
def prefixEnd_1186213 : Nat := 4983230072969 + 3 ^ 40 * 1186213 * 2
def baseEnd_1186213 : Nat := 135354983913749482196047

theorem tailTrace_1186213 : CollatzResearch.WordTrace tailWord_1186213 prefixEnd_1186213 135354983913749482196047 := by
  unfold tailWord_1186213
  simp only [CollatzResearch.WordTrace]
  refine ⟨43264742451560364896571293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28843161634373576597714195 43264742451560364896571293)
  ·
    refine ⟨16224278419335136836214235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43264742451560364896571293 16224278419335136836214235)
    ·
      refine ⟨24336417629002705254321353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16224278419335136836214235 24336417629002705254321353)
      ·
        refine ⟨18252313221752028940741015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24336417629002705254321353 18252313221752028940741015)
        ·
          refine ⟨27378469832628043411111523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18252313221752028940741015 27378469832628043411111523)
          ·
            refine ⟨41067704748942065116667285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27378469832628043411111523 41067704748942065116667285)
            ·
              refine ⟨1925048660106659302343779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41067704748942065116667285 1925048660106659302343779)
              ·
                refine ⟨2887572990159988953515669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925048660106659302343779 2887572990159988953515669)
                ·
                  refine ⟨135354983913749482196047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2887572990159988953515669 135354983913749482196047)
                  ·
                    rfl

theorem cell22_1186213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_1186213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186213 prefixEnd_1186213 := by exact prefixLift 1186213
  have htrace : WordTrace (prefixWord ++ tailWord_1186213) baseStart_1186213 baseEnd_1186213 := by
    simpa [prefixWord, tailWord_1186213, baseEnd_1186213] using wordTrace_append hprefix tailTrace_1186213
  have hstable : (prefixWord ++ tailWord_1186213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186213).length < 2 ^ (prefixWord ++ tailWord_1186213).sum := by decide
  have hdescent : baseEnd_1186213 < baseStart_1186213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186243 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_1186243 : Nat := 118140960795 + 1186243 * 2 ^ 59
def prefixEnd_1186243 : Nat := 4983230072969 + 3 ^ 40 * 1186243 * 2
def baseEnd_1186243 : Nat := 406075221354338368338049

theorem tailTrace_1186243 : CollatzResearch.WordTrace tailWord_1186243 prefixEnd_1186243 406075221354338368338049 := by
  unfold tailWord_1186243
  simp only [CollatzResearch.WordTrace]
  refine ⟨43265836641451680020163383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28843891094301120013442255 43265836641451680020163383)
  ·
    refine ⟨64898754962177520030245075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43265836641451680020163383 64898754962177520030245075)
    ·
      refine ⟨97348132443266280045367613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64898754962177520030245075 97348132443266280045367613)
      ·
        refine ⟨36505549666224855017012855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97348132443266280045367613 36505549666224855017012855)
        ·
          refine ⟨54758324499337282525519283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36505549666224855017012855 54758324499337282525519283)
          ·
            refine ⟨82137486749005923788278925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54758324499337282525519283 82137486749005923788278925)
            ·
              refine ⟨30801557530877221420604597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82137486749005923788278925 30801557530877221420604597)
              ·
                refine ⟨2887646018519739508181681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30801557530877221420604597 2887646018519739508181681)
                ·
                  refine ⟨2165734513889804631136261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887646018519739508181681 2165734513889804631136261)
                  ·
                    refine ⟨406075221354338368338049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165734513889804631136261 406075221354338368338049)
                    ·
                      rfl

theorem cell22_1186243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_1186243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186243 prefixEnd_1186243 := by exact prefixLift 1186243
  have htrace : WordTrace (prefixWord ++ tailWord_1186243) baseStart_1186243 baseEnd_1186243 := by
    simpa [prefixWord, tailWord_1186243, baseEnd_1186243] using wordTrace_append hprefix tailTrace_1186243
  have hstable : (prefixWord ++ tailWord_1186243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186243).length < 2 ^ (prefixWord ++ tailWord_1186243).sum := by decide
  have hdescent : baseEnd_1186243 < baseStart_1186243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186247 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 4]
def baseStart_1186247 : Nat := 118140960795 + 1186247 * 2 ^ 59
def prefixEnd_1186247 : Nat := 4983230072969 + 3 ^ 40 * 1186247 * 2
def baseEnd_1186247 : Nat := 135358863545361230412679

theorem tailTrace_1186247 : CollatzResearch.WordTrace tailWord_1186247 prefixEnd_1186247 135358863545361230412679 := by
  unfold tailWord_1186247
  simp only [CollatzResearch.WordTrace]
  refine ⟨43265982533437188703308995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28843988355624792468872663 43265982533437188703308995)
  ·
    refine ⟨64898973800155783054963493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43265982533437188703308995 64898973800155783054963493)
    ·
      refine ⟨12168557587529209322805655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64898973800155783054963493 12168557587529209322805655)
      ·
        refine ⟨18252836381293813984208483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12168557587529209322805655 18252836381293813984208483)
        ·
          refine ⟨27379254571940720976312725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18252836381293813984208483 27379254571940720976312725)
          ·
            refine ⟨1283402558059721295764659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27379254571940720976312725 1283402558059721295764659)
            ·
              refine ⟨1925103837089581943646989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283402558059721295764659 1925103837089581943646989)
              ·
                refine ⟨721913938908593228867621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1925103837089581943646989 721913938908593228867621)
                ·
                  refine ⟨135358863545361230412679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721913938908593228867621 135358863545361230412679)
                  ·
                    rfl

theorem cell22_1186247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 4].length) (baseStart_1186247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186247 prefixEnd_1186247 := by exact prefixLift 1186247
  have htrace : WordTrace (prefixWord ++ tailWord_1186247) baseStart_1186247 baseEnd_1186247 := by
    simpa [prefixWord, tailWord_1186247, baseEnd_1186247] using wordTrace_append hprefix tailTrace_1186247
  have hstable : (prefixWord ++ tailWord_1186247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186247).length < 2 ^ (prefixWord ++ tailWord_1186247).sum := by decide
  have hdescent : baseEnd_1186247 < baseStart_1186247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186260 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1186260 : Nat := 118140960795 + 1186260 * 2 ^ 59
def prefixEnd_1186260 : Nat := 4983230072969 + 3 ^ 40 * 1186260 * 2
def baseEnd_1186260 : Nat := 406081040801755990662997

theorem tailTrace_1186260 : CollatzResearch.WordTrace tailWord_1186260 prefixEnd_1186260 406081040801755990662997 := by
  unfold tailWord_1186260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21633228341195045961766117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28844304454926727949021489 21633228341195045961766117)
  ·
    refine ⟨4056230313974071117831147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21633228341195045961766117 4056230313974071117831147)
    ·
      refine ⟨6084345470961106676746721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4056230313974071117831147 6084345470961106676746721)
      ·
        refine ⟨4563259103220830007560041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6084345470961106676746721 4563259103220830007560041)
        ·
          refine ⟨3422444327415622505670031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4563259103220830007560041 3422444327415622505670031)
          ·
            refine ⟨5133666491123433758505047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422444327415622505670031 5133666491123433758505047)
            ·
              refine ⟨7700499736685150637757571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5133666491123433758505047 7700499736685150637757571)
              ·
                refine ⟨11550749605027725956636357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7700499736685150637757571 11550749605027725956636357)
                ·
                  refine ⟨2165765550942698616869317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11550749605027725956636357 2165765550942698616869317)
                  ·
                    refine ⟨406081040801755990662997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165765550942698616869317 406081040801755990662997)
                    ·
                      rfl

theorem cell22_1186260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1186260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186260 prefixEnd_1186260 := by exact prefixLift 1186260
  have htrace : WordTrace (prefixWord ++ tailWord_1186260) baseStart_1186260 baseEnd_1186260 := by
    simpa [prefixWord, tailWord_1186260, baseEnd_1186260] using wordTrace_append hprefix tailTrace_1186260
  have hstable : (prefixWord ++ tailWord_1186260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186260).length < 2 ^ (prefixWord ++ tailWord_1186260).sum := by decide
  have hdescent : baseEnd_1186260 < baseStart_1186260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186262 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1186262 : Nat := 118140960795 + 1186262 * 2 ^ 59
def prefixEnd_1186262 : Nat := 4983230072969 + 3 ^ 40 * 1186262 * 2
def baseEnd_1186262 : Nat := 406081725442628652112991

theorem tailTrace_1186262 : CollatzResearch.WordTrace tailWord_1186262 prefixEnd_1186262 406081725442628652112991 := by
  unfold tailWord_1186262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704158101773927891569065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28844353085588564176736693 2704158101773927891569065)
  ·
    refine ⟨2028118576330445918676799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2704158101773927891569065 2028118576330445918676799)
    ·
      refine ⟨3042177864495668878015199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2028118576330445918676799 3042177864495668878015199)
      ·
        refine ⟨4563266796743503317022799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042177864495668878015199 4563266796743503317022799)
        ·
          refine ⟨6844900195115254975534199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563266796743503317022799 6844900195115254975534199)
          ·
            refine ⟨10267350292672882463301299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844900195115254975534199 10267350292672882463301299)
            ·
              refine ⟨15401025439009323694951949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10267350292672882463301299 15401025439009323694951949)
              ·
                refine ⟨5775384539628496385606981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15401025439009323694951949 5775384539628496385606981)
                ·
                  refine ⟨1082884601180343072301309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5775384539628496385606981 1082884601180343072301309)
                  ·
                    refine ⟨406081725442628652112991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082884601180343072301309 406081725442628652112991)
                    ·
                      rfl

theorem cell22_1186262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1186262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186262 prefixEnd_1186262 := by exact prefixLift 1186262
  have htrace : WordTrace (prefixWord ++ tailWord_1186262) baseStart_1186262 baseEnd_1186262 := by
    simpa [prefixWord, tailWord_1186262, baseEnd_1186262] using wordTrace_append hprefix tailTrace_1186262
  have hstable : (prefixWord ++ tailWord_1186262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186262).length < 2 ^ (prefixWord ++ tailWord_1186262).sum := by decide
  have hdescent : baseEnd_1186262 < baseStart_1186262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186275 : List Nat := [1, 1, 1, 6, 3, 1, 2, 7]
def baseStart_1186275 : Nat := 118140960795 + 1186275 * 2 ^ 59
def prefixEnd_1186275 : Nat := 4983230072969 + 3 ^ 40 * 1186275 * 2
def baseEnd_1186275 : Nat := 45120686178700105726439

theorem tailTrace_1186275 : CollatzResearch.WordTrace tailWord_1186275 prefixEnd_1186275 45120686178700105726439 := by
  unfold tailWord_1186275
  simp only [CollatzResearch.WordTrace]
  refine ⟨43267003777335749485328279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28844669184890499656885519 43267003777335749485328279)
  ·
    refine ⟨64900505666003624227992419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43267003777335749485328279 64900505666003624227992419)
    ·
      refine ⟨97350758499005436341988629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64900505666003624227992419 97350758499005436341988629)
      ·
        refine ⟨4563316804640879828530717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97350758499005436341988629 4563316804640879828530717)
        ·
          refine ⟨1711243801740329935699019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4563316804640879828530717 1711243801740329935699019)
          ·
            refine ⟨2566865702610494903548529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711243801740329935699019 2566865702610494903548529)
            ·
              refine ⟨1925149276957871177661397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2566865702610494903548529 1925149276957871177661397)
              ·
                refine ⟨45120686178700105726439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1925149276957871177661397 45120686178700105726439)
                ·
                  rfl

theorem cell22_1186275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 7].length) (baseStart_1186275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186275 prefixEnd_1186275 := by exact prefixLift 1186275
  have htrace : WordTrace (prefixWord ++ tailWord_1186275) baseStart_1186275 baseEnd_1186275 := by
    simpa [prefixWord, tailWord_1186275, baseEnd_1186275] using wordTrace_append hprefix tailTrace_1186275
  have hstable : (prefixWord ++ tailWord_1186275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186275).length < 2 ^ (prefixWord ++ tailWord_1186275).sum := by decide
  have hdescent : baseEnd_1186275 < baseStart_1186275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186307 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 1, 3]
def baseStart_1186307 : Nat := 118140960795 + 1186307 * 2 ^ 59
def prefixEnd_1186307 : Nat := 4983230072969 + 3 ^ 40 * 1186307 * 2
def baseEnd_1186307 : Nat := 406097129862263534737853

theorem tailTrace_1186307 : CollatzResearch.WordTrace tailWord_1186307 prefixEnd_1186307 406097129862263534737853 := by
  unfold tailWord_1186307
  simp only [CollatzResearch.WordTrace]
  refine ⟨43268170913219818950493175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28845447275479879300328783 43268170913219818950493175)
  ·
    refine ⟨64902256369829728425739763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43268170913219818950493175 64902256369829728425739763)
    ·
      refine ⟨97353384554744592638609645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64902256369829728425739763 97353384554744592638609645)
      ·
        refine ⟨36507519208029222239478617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97353384554744592638609645 36507519208029222239478617)
        ·
          refine ⟨27380639406021916679608963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36507519208029222239478617 27380639406021916679608963)
          ·
            refine ⟨41070959109032875019413445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27380639406021916679608963 41070959109032875019413445)
            ·
              refine ⟨7700804832943664066140021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41070959109032875019413445 7700804832943664066140021)
              ·
                refine ⟨721950453088468506200627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7700804832943664066140021 721950453088468506200627)
                ·
                  refine ⟨1082925679632702759300941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721950453088468506200627 1082925679632702759300941)
                  ·
                    refine ⟨406097129862263534737853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082925679632702759300941 406097129862263534737853)
                    ·
                      rfl

theorem cell22_1186307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 3].length) (baseStart_1186307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186307 prefixEnd_1186307 := by exact prefixLift 1186307
  have htrace : WordTrace (prefixWord ++ tailWord_1186307) baseStart_1186307 baseEnd_1186307 := by
    simpa [prefixWord, tailWord_1186307, baseEnd_1186307] using wordTrace_append hprefix tailTrace_1186307
  have hstable : (prefixWord ++ tailWord_1186307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186307).length < 2 ^ (prefixWord ++ tailWord_1186307).sum := by decide
  have hdescent : baseEnd_1186307 < baseStart_1186307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186363 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_1186363 : Nat := 118140960795 + 1186363 * 2 ^ 59
def prefixEnd_1186363 : Nat := 4983230072969 + 3 ^ 40 * 1186363 * 2
def baseEnd_1186363 : Nat := 406116299806698055337681

theorem tailTrace_1186363 : CollatzResearch.WordTrace tailWord_1186363 prefixEnd_1186363 406116299806698055337681 := by
  unfold tailWord_1186363
  simp only [CollatzResearch.WordTrace]
  refine ⟨43270213401016940514531743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28846808934011293676354495 43270213401016940514531743)
  ·
    refine ⟨64905320101525410771797615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43270213401016940514531743 64905320101525410771797615)
    ·
      refine ⟨97357980152288116157696423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64905320101525410771797615 97357980152288116157696423)
      ·
        refine ⟨146036970228432174236544635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97357980152288116157696423 146036970228432174236544635)
        ·
          refine ⟨219055455342648261354816953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146036970228432174236544635 219055455342648261354816953)
          ·
            refine ⟨164291591506986196016112715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219055455342648261354816953 164291591506986196016112715)
            ·
              refine ⟨246437387260479294024169073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164291591506986196016112715 246437387260479294024169073)
              ·
                refine ⟨184828040445359470518126805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246437387260479294024169073 184828040445359470518126805)
                ·
                  refine ⟨4331907197938112590268597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184828040445359470518126805 4331907197938112590268597)
                  ·
                    refine ⟨406116299806698055337681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4331907197938112590268597 406116299806698055337681)
                    ·
                      rfl

theorem cell22_1186363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_1186363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186363 prefixEnd_1186363 := by exact prefixLift 1186363
  have htrace : WordTrace (prefixWord ++ tailWord_1186363) baseStart_1186363 baseEnd_1186363 := by
    simpa [prefixWord, tailWord_1186363, baseEnd_1186363] using wordTrace_append hprefix tailTrace_1186363
  have hstable : (prefixWord ++ tailWord_1186363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186363).length < 2 ^ (prefixWord ++ tailWord_1186363).sum := by decide
  have hdescent : baseEnd_1186363 < baseStart_1186363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186382 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1186382 : Nat := 118140960795 + 1186382 * 2 ^ 59
def prefixEnd_1186382 : Nat := 4983230072969 + 3 ^ 40 * 1186382 * 2
def baseEnd_1186382 : Nat := 135374267964996113037541

theorem tailTrace_1186382 : CollatzResearch.WordTrace tailWord_1186382 prefixEnd_1186382 135374267964996113037541 := by
  unfold tailWord_1186382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408863298493513344934175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28847270925298737839648933 5408863298493513344934175)
  ·
    refine ⟨8113294947740270017401263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5408863298493513344934175 8113294947740270017401263)
    ·
      refine ⟨12169942421610405026101895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8113294947740270017401263 12169942421610405026101895)
      ·
        refine ⟨18254913632415607539152843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169942421610405026101895 18254913632415607539152843)
        ·
          refine ⟨27382370448623411308729265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18254913632415607539152843 27382370448623411308729265)
          ·
            refine ⟨20536777836467558481546949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27382370448623411308729265 20536777836467558481546949)
            ·
              refine ⟨3850645844337667215290053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20536777836467558481546949 3850645844337667215290053)
              ·
                refine ⟨721996095813312602866885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3850645844337667215290053 721996095813312602866885)
                ·
                  refine ⟨135374267964996113037541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721996095813312602866885 135374267964996113037541)
                  ·
                    rfl

theorem cell22_1186382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1186382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186382 prefixEnd_1186382 := by exact prefixLift 1186382
  have htrace : WordTrace (prefixWord ++ tailWord_1186382) baseStart_1186382 baseEnd_1186382 := by
    simpa [prefixWord, tailWord_1186382, baseEnd_1186382] using wordTrace_append hprefix tailTrace_1186382
  have hstable : (prefixWord ++ tailWord_1186382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186382).length < 2 ^ (prefixWord ++ tailWord_1186382).sum := by decide
  have hdescent : baseEnd_1186382 < baseStart_1186382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186410 : List Nat := [3, 1, 3, 2, 1, 1, 3, 8]
def baseStart_1186410 : Nat := 118140960795 + 1186410 * 2 ^ 59
def prefixEnd_1186410 : Nat := 4983230072969 + 3 ^ 40 * 1186410 * 2
def baseEnd_1186410 : Nat := 45125820985245066601393

theorem tailTrace_1186410 : CollatzResearch.WordTrace tailWord_1186410 prefixEnd_1186410 45125820985245066601393 := by
  unfold tailWord_1186410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817981907961666885373171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28847951754564445027661789 10817981907961666885373171)
  ·
    refine ⟨16226972861942500328059757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10817981907961666885373171 16226972861942500328059757)
    ·
      refine ⟨6085114823228437623022409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16226972861942500328059757 6085114823228437623022409)
      ·
        refine ⟨4563836117421328217266807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6085114823228437623022409 4563836117421328217266807)
        ·
          refine ⟨6845754176131992325900211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563836117421328217266807 6845754176131992325900211)
          ·
            refine ⟨10268631264197988488850317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845754176131992325900211 10268631264197988488850317)
            ·
              refine ⟨3850736724074245683318869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10268631264197988488850317 3850736724074245683318869)
              ·
                refine ⟨45125820985245066601393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3850736724074245683318869 45125820985245066601393)
                ·
                  rfl

theorem cell22_1186410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_1186410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186410 prefixEnd_1186410 := by exact prefixLift 1186410
  have htrace : WordTrace (prefixWord ++ tailWord_1186410) baseStart_1186410 baseEnd_1186410 := by
    simpa [prefixWord, tailWord_1186410, baseEnd_1186410] using wordTrace_append hprefix tailTrace_1186410
  have hstable : (prefixWord ++ tailWord_1186410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186410).length < 2 ^ (prefixWord ++ tailWord_1186410).sum := by decide
  have hdescent : baseEnd_1186410 < baseStart_1186410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186416 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_1186416 : Nat := 118140960795 + 1186416 * 2 ^ 59
def prefixEnd_1186416 : Nat := 4983230072969 + 3 ^ 40 * 1186416 * 2
def baseEnd_1186416 : Nat := 135378147596607861254173

theorem tailTrace_1186416 : CollatzResearch.WordTrace tailWord_1186416 prefixEnd_1186416 135378147596607861254173 := by
  unfold tailWord_1186416
  simp only [CollatzResearch.WordTrace]
  refine ⟨21636073234912465283105551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28848097646549953710807401 21636073234912465283105551)
  ·
    refine ⟨32454109852368697924658327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21636073234912465283105551 32454109852368697924658327)
    ·
      refine ⟨48681164778553046886987491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32454109852368697924658327 48681164778553046886987491)
      ·
        refine ⟨73021747167829570330481237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48681164778553046886987491 73021747167829570330481237)
        ·
          refine ⟨855723599623002777310327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 73021747167829570330481237 855723599623002777310327)
          ·
            refine ⟨1283585399434504165965491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855723599623002777310327 1283585399434504165965491)
            ·
              refine ⟨1925378099151756248948237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283585399434504165965491 1925378099151756248948237)
              ·
                refine ⟨722016787181908593355589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1925378099151756248948237 722016787181908593355589)
                ·
                  refine ⟨135378147596607861254173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722016787181908593355589 135378147596607861254173)
                  ·
                    rfl

theorem cell22_1186416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_1186416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186416 prefixEnd_1186416 := by exact prefixLift 1186416
  have htrace : WordTrace (prefixWord ++ tailWord_1186416) baseStart_1186416 baseEnd_1186416 := by
    simpa [prefixWord, tailWord_1186416, baseEnd_1186416] using wordTrace_append hprefix tailTrace_1186416
  have hstable : (prefixWord ++ tailWord_1186416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186416).length < 2 ^ (prefixWord ++ tailWord_1186416).sum := by decide
  have hdescent : baseEnd_1186416 < baseStart_1186416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186493 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_1186493 : Nat := 118140960795 + 1186493 * 2 ^ 59
def prefixEnd_1186493 : Nat := 4983230072969 + 3 ^ 40 * 1186493 * 2
def baseEnd_1186493 : Nat := 406160801463421049587283

theorem tailTrace_1186493 : CollatzResearch.WordTrace tailWord_1186493 prefixEnd_1186493 406160801463421049587283 := by
  unfold tailWord_1186493
  simp only [CollatzResearch.WordTrace]
  refine ⟨43274954890545972716764133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28849969927030648477842755 43274954890545972716764133)
  ·
    refine ⟨8114054041977369884393275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43274954890545972716764133 8114054041977369884393275)
    ·
      refine ⟨12171081062966054826589913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8114054041977369884393275 12171081062966054826589913)
      ·
        refine ⟨9128310797224541119942435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12171081062966054826589913 9128310797224541119942435)
        ·
          refine ⟨13692466195836811679913653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9128310797224541119942435 13692466195836811679913653)
          ·
            refine ⟨1283668705859701094991905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13692466195836811679913653 1283668705859701094991905)
            ·
              refine ⟨962751529394775821243929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283668705859701094991905 962751529394775821243929)
              ·
                refine ⟨722063647046081865932947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962751529394775821243929 722063647046081865932947)
                ·
                  refine ⟨1083095470569122798899421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722063647046081865932947 1083095470569122798899421)
                  ·
                    refine ⟨406160801463421049587283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083095470569122798899421 406160801463421049587283)
                    ·
                      rfl

theorem cell22_1186493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_1186493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186493 prefixEnd_1186493 := by exact prefixLift 1186493
  have htrace : WordTrace (prefixWord ++ tailWord_1186493) baseStart_1186493 baseEnd_1186493 := by
    simpa [prefixWord, tailWord_1186493, baseEnd_1186493] using wordTrace_append hprefix tailTrace_1186493
  have hstable : (prefixWord ++ tailWord_1186493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186493).length < 2 ^ (prefixWord ++ tailWord_1186493).sum := by decide
  have hdescent : baseEnd_1186493 < baseStart_1186493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186532 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1186532 : Nat := 118140960795 + 1186532 * 2 ^ 59
def prefixEnd_1186532 : Nat := 4983230072969 + 3 ^ 40 * 1186532 * 2
def baseEnd_1186532 : Nat := 406174151960437947862163

theorem tailTrace_1186532 : CollatzResearch.WordTrace tailWord_1186532 prefixEnd_1186532 406174151960437947862163 := by
  unfold tailWord_1186532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638188668702341188716925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28850918224936454918289233 21638188668702341188716925)
  ·
    refine ⟨8114320750763377945768847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21638188668702341188716925 8114320750763377945768847)
    ·
      refine ⟨12171481126145066918653271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8114320750763377945768847 12171481126145066918653271)
      ·
        refine ⟨18257221689217600377979907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12171481126145066918653271 18257221689217600377979907)
        ·
          refine ⟨27385832533826400566969861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18257221689217600377979907 27385832533826400566969861)
          ·
            refine ⟨5134843600092450106306849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27385832533826400566969861 5134843600092450106306849)
            ·
              refine ⟨3851132700069337579730137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134843600092450106306849 3851132700069337579730137)
              ·
                refine ⟨2888349525052003184797603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3851132700069337579730137 2888349525052003184797603)
                ·
                  refine ⟨4332524287578004777196405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888349525052003184797603 4332524287578004777196405)
                  ·
                    refine ⟨406174151960437947862163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4332524287578004777196405 406174151960437947862163)
                    ·
                      rfl

theorem cell22_1186532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1186532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186532 prefixEnd_1186532 := by exact prefixLift 1186532
  have htrace : WordTrace (prefixWord ++ tailWord_1186532) baseStart_1186532 baseEnd_1186532 := by
    simpa [prefixWord, tailWord_1186532, baseEnd_1186532] using wordTrace_append hprefix tailTrace_1186532
  have hstable : (prefixWord ++ tailWord_1186532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186532).length < 2 ^ (prefixWord ++ tailWord_1186532).sum := by decide
  have hdescent : baseEnd_1186532 < baseStart_1186532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186545 : List Nat := [1, 2, 2, 2, 2, 2, 11]
def baseStart_1186545 : Nat := 118140960795 + 1186545 * 2 ^ 59
def prefixEnd_1186545 : Nat := 4983230072969 + 3 ^ 40 * 1186545 * 2
def baseEnd_1186545 : Nat := 15043651930596675825449

theorem tailTrace_1186545 : CollatzResearch.WordTrace tailWord_1186545 prefixEnd_1186545 15043651930596675825449 := by
  unfold tailWord_1186545
  simp only [CollatzResearch.WordTrace]
  refine ⟨43276851486357585597657089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28851234324238390398438059 43276851486357585597657089)
  ·
    refine ⟨32457638614768189198242817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43276851486357585597657089 32457638614768189198242817)
    ·
      refine ⟨24343228961076141898682113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32457638614768189198242817 24343228961076141898682113)
      ·
        refine ⟨18257421720807106424011585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24343228961076141898682113 18257421720807106424011585)
        ·
          refine ⟨13693066290605329818008689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18257421720807106424011585 13693066290605329818008689)
          ·
            refine ⟨10269799717953997363506517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13693066290605329818008689 10269799717953997363506517)
            ·
              refine ⟨15043651930596675825449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10269799717953997363506517 15043651930596675825449)
              ·
                rfl

theorem cell22_1186545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 11].length) (baseStart_1186545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186545 prefixEnd_1186545 := by exact prefixLift 1186545
  have htrace : WordTrace (prefixWord ++ tailWord_1186545) baseStart_1186545 baseEnd_1186545 := by
    simpa [prefixWord, tailWord_1186545, baseEnd_1186545] using wordTrace_append hprefix tailTrace_1186545
  have hstable : (prefixWord ++ tailWord_1186545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186545).length < 2 ^ (prefixWord ++ tailWord_1186545).sum := by decide
  have hdescent : baseEnd_1186545 < baseStart_1186545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186560 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1186560 : Nat := 118140960795 + 1186560 * 2 ^ 59
def prefixEnd_1186560 : Nat := 4983230072969 + 3 ^ 40 * 1186560 * 2
def baseEnd_1186560 : Nat := 406183736932655208162077

theorem tailTrace_1186560 : CollatzResearch.WordTrace tailWord_1186560 prefixEnd_1186560 406183736932655208162077 := by
  unfold tailWord_1186560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638699290651621579726567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28851599054202162106302089 21638699290651621579726567)
  ·
    refine ⟨32458048935977432369589851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21638699290651621579726567 32458048935977432369589851)
    ·
      refine ⟨48687073403966148554384777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32458048935977432369589851 48687073403966148554384777)
      ·
        refine ⟨36515305052974611415788583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48687073403966148554384777 36515305052974611415788583)
        ·
          refine ⟨54772957579461917123682875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36515305052974611415788583 54772957579461917123682875)
          ·
            refine ⟨82159436369192875685524313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54772957579461917123682875 82159436369192875685524313)
            ·
              refine ⟨61619577276894656764143235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82159436369192875685524313 61619577276894656764143235)
              ·
                refine ⟨92429365915341985146214853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61619577276894656764143235 92429365915341985146214853)
                ·
                  refine ⟨17330506109126622214915285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92429365915341985146214853 17330506109126622214915285)
                  ·
                    refine ⟨406183736932655208162077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17330506109126622214915285 406183736932655208162077)
                    ·
                      rfl

theorem cell22_1186560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1186560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186560 prefixEnd_1186560 := by exact prefixLift 1186560
  have htrace : WordTrace (prefixWord ++ tailWord_1186560) baseStart_1186560 baseEnd_1186560 := by
    simpa [prefixWord, tailWord_1186560, baseEnd_1186560] using wordTrace_append hprefix tailTrace_1186560
  have hstable : (prefixWord ++ tailWord_1186560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186560).length < 2 ^ (prefixWord ++ tailWord_1186560).sum := by decide
  have hdescent : baseEnd_1186560 < baseStart_1186560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186611 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 3, 3]
def baseStart_1186611 : Nat := 118140960795 + 1186611 * 2 ^ 59
def prefixEnd_1186611 : Nat := 4983230072969 + 3 ^ 40 * 1186611 * 2
def baseEnd_1186611 : Nat := 406201195274908075136921

theorem tailTrace_1186611 : CollatzResearch.WordTrace tailWord_1186611 prefixEnd_1186611 406201195274908075136921 := by
  unfold tailWord_1186611
  simp only [CollatzResearch.WordTrace]
  refine ⟨43279258704118478869559687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28852839136078985913039791 43279258704118478869559687)
  ·
    refine ⟨64918888056177718304339531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43279258704118478869559687 64918888056177718304339531)
    ·
      refine ⟨97378332084266577456509297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64918888056177718304339531 97378332084266577456509297)
      ·
        refine ⟨73033749063199933092381973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97378332084266577456509297 73033749063199933092381973)
        ·
          refine ⟨3423456987337496863705405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73033749063199933092381973 3423456987337496863705405)
          ·
            refine ⟨1283796370251561323889527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3423456987337496863705405 1283796370251561323889527)
            ·
              refine ⟨1925694555377341985834291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283796370251561323889527 1925694555377341985834291)
              ·
                refine ⟨2888541833066012978751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925694555377341985834291 2888541833066012978751437)
                ·
                  refine ⟨1083203187399754867031789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2888541833066012978751437 1083203187399754867031789)
                  ·
                    refine ⟨406201195274908075136921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083203187399754867031789 406201195274908075136921)
                    ·
                      rfl

theorem cell22_1186611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 3].length) (baseStart_1186611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186611 prefixEnd_1186611 := by exact prefixLift 1186611
  have htrace : WordTrace (prefixWord ++ tailWord_1186611) baseStart_1186611 baseEnd_1186611 := by
    simpa [prefixWord, tailWord_1186611, baseEnd_1186611] using wordTrace_append hprefix tailTrace_1186611
  have hstable : (prefixWord ++ tailWord_1186611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186611).length < 2 ^ (prefixWord ++ tailWord_1186611).sum := by decide
  have hdescent : baseEnd_1186611 < baseStart_1186611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186682 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_1186682 : Nat := 118140960795 + 1186682 * 2 ^ 59
def prefixEnd_1186682 : Nat := 4983230072969 + 3 ^ 40 * 1186682 * 2
def baseEnd_1186682 : Nat := 406225500025887556611703

theorem tailTrace_1186682 : CollatzResearch.WordTrace tailWord_1186682 prefixEnd_1186682 406225500025887556611703 := by
  unfold tailWord_1186682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820462071715314498848575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28854565524574171996929533 10820462071715314498848575)
  ·
    refine ⟨16230693107572971748272863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10820462071715314498848575 16230693107572971748272863)
    ·
      refine ⟨24346039661359457622409295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16230693107572971748272863 24346039661359457622409295)
      ·
        refine ⟨36519059492039186433613943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24346039661359457622409295 36519059492039186433613943)
        ·
          refine ⟨54778589238058779650420915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36519059492039186433613943 54778589238058779650420915)
          ·
            refine ⟨82167883857088169475631373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54778589238058779650420915 82167883857088169475631373)
            ·
              refine ⟨30812956446408063553361765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82167883857088169475631373 30812956446408063553361765)
              ·
                refine ⟨5777429333701511916255331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30812956446408063553361765 5777429333701511916255331)
                ·
                  refine ⟨8666144000552267874382997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777429333701511916255331 8666144000552267874382997)
                  ·
                    refine ⟨406225500025887556611703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8666144000552267874382997 406225500025887556611703)
                    ·
                      rfl

theorem cell22_1186682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_1186682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186682 prefixEnd_1186682 := by exact prefixLift 1186682
  have htrace : WordTrace (prefixWord ++ tailWord_1186682) baseStart_1186682 baseEnd_1186682 := by
    simpa [prefixWord, tailWord_1186682, baseEnd_1186682] using wordTrace_append hprefix tailTrace_1186682
  have hstable : (prefixWord ++ tailWord_1186682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186682).length < 2 ^ (prefixWord ++ tailWord_1186682).sum := by decide
  have hdescent : baseEnd_1186682 < baseStart_1186682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186699 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 2, 4]
def baseStart_1186699 : Nat := 118140960795 + 1186699 * 2 ^ 59
def prefixEnd_1186699 : Nat := 4983230072969 + 3 ^ 40 * 1186699 * 2
def baseEnd_1186699 : Nat := 406231319473305178936651

theorem tailTrace_1186699 : CollatzResearch.WordTrace tailWord_1186699 prefixEnd_1186699 406231319473305178936651 := by
  unfold tailWord_1186699
  simp only [CollatzResearch.WordTrace]
  refine ⟨43282468327799669898763151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28854978885199779932508767 43282468327799669898763151)
  ·
    refine ⟨64923702491699504848144727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43282468327799669898763151 64923702491699504848144727)
    ·
      refine ⟨97385553737549257272217091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64923702491699504848144727 97385553737549257272217091)
      ·
        refine ⟨146078330606323885908325637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97385553737549257272217091 146078330606323885908325637)
        ·
          refine ⟨27389686988685728607811057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146078330606323885908325637 27389686988685728607811057)
          ·
            refine ⟨20542265241514296455858293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27389686988685728607811057 20542265241514296455858293)
            ·
              refine ⟨1925837366391965292736715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20542265241514296455858293 1925837366391965292736715)
              ·
                refine ⟨2888756049587947939105073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925837366391965292736715 2888756049587947939105073)
                ·
                  refine ⟨2166567037190960954328805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2888756049587947939105073 2166567037190960954328805)
                  ·
                    refine ⟨406231319473305178936651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2166567037190960954328805 406231319473305178936651)
                    ·
                      rfl

theorem cell22_1186699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_1186699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186699 prefixEnd_1186699 := by exact prefixLift 1186699
  have htrace : WordTrace (prefixWord ++ tailWord_1186699) baseStart_1186699 baseEnd_1186699 := by
    simpa [prefixWord, tailWord_1186699, baseEnd_1186699] using wordTrace_append hprefix tailTrace_1186699
  have hstable : (prefixWord ++ tailWord_1186699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186699).length < 2 ^ (prefixWord ++ tailWord_1186699).sum := by decide
  have hdescent : baseEnd_1186699 < baseStart_1186699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186714 : List Nat := [3, 1, 1, 4, 3, 1, 9]
def baseStart_1186714 : Nat := 118140960795 + 1186714 * 2 ^ 59
def prefixEnd_1186714 : Nat := 4983230072969 + 3 ^ 40 * 1186714 * 2
def baseEnd_1186714 : Nat := 15045794602957412585615

theorem tailTrace_1186714 : CollatzResearch.WordTrace tailWord_1186714 prefixEnd_1186714 15045794602957412585615 := by
  unfold tailWord_1186714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820753855686331865139799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28855343615163551640372797 10820753855686331865139799)
  ·
    refine ⟨16231130783529497797709699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10820753855686331865139799 16231130783529497797709699)
    ·
      refine ⟨24346696175294246696564549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16231130783529497797709699 24346696175294246696564549)
      ·
        refine ⟨4565005532867671255605853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24346696175294246696564549 4565005532867671255605853)
        ·
          refine ⟨1711877074825376720852195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4565005532867671255605853 1711877074825376720852195)
          ·
            refine ⟨2567815612238065081278293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711877074825376720852195 2567815612238065081278293)
            ·
              refine ⟨15045794602957412585615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2567815612238065081278293 15045794602957412585615)
              ·
                rfl

theorem cell22_1186714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 9].length) (baseStart_1186714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186714 prefixEnd_1186714 := by exact prefixLift 1186714
  have htrace : WordTrace (prefixWord ++ tailWord_1186714) baseStart_1186714 baseEnd_1186714 := by
    simpa [prefixWord, tailWord_1186714, baseEnd_1186714] using wordTrace_append hprefix tailTrace_1186714
  have hstable : (prefixWord ++ tailWord_1186714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186714).length < 2 ^ (prefixWord ++ tailWord_1186714).sum := by decide
  have hdescent : baseEnd_1186714 < baseStart_1186714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186763 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 1, 3]
def baseStart_1186763 : Nat := 118140960795 + 1186763 * 2 ^ 59
def prefixEnd_1186763 : Nat := 4983230072969 + 3 ^ 40 * 1186763 * 2
def baseEnd_1186763 : Nat := 406253227981230345336455

theorem tailTrace_1186763 : CollatzResearch.WordTrace tailWord_1186763 prefixEnd_1186763 406253227981230345336455 := by
  unfold tailWord_1186763
  simp only [CollatzResearch.WordTrace]
  refine ⟨43284802599567808829092943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28856535066378539219395295 43284802599567808829092943)
  ·
    refine ⟨64927203899351713243639415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43284802599567808829092943 64927203899351713243639415)
    ·
      refine ⟨97390805849027569865459123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64927203899351713243639415 97390805849027569865459123)
      ·
        refine ⟨146086208773541354798188685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97390805849027569865459123 146086208773541354798188685)
        ·
          refine ⟨54782328290078008049320757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146086208773541354798188685 54782328290078008049320757)
          ·
            refine ⟨5135843277194813254623821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54782328290078008049320757 5135843277194813254623821)
            ·
              refine ⟨1925941228948054970483933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5135843277194813254623821 1925941228948054970483933)
              ·
                refine ⟨722227960855520613931475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1925941228948054970483933 722227960855520613931475)
                ·
                  refine ⟨1083341941283280920897213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722227960855520613931475 1083341941283280920897213)
                  ·
                    refine ⟨406253227981230345336455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083341941283280920897213 406253227981230345336455)
                    ·
                      rfl

theorem cell22_1186763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 3].length) (baseStart_1186763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186763 prefixEnd_1186763 := by exact prefixLift 1186763
  have htrace : WordTrace (prefixWord ++ tailWord_1186763) baseStart_1186763 baseEnd_1186763 := by
    simpa [prefixWord, tailWord_1186763, baseEnd_1186763] using wordTrace_append hprefix tailTrace_1186763
  have hstable : (prefixWord ++ tailWord_1186763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186763).length < 2 ^ (prefixWord ++ tailWord_1186763).sum := by decide
  have hdescent : baseEnd_1186763 < baseStart_1186763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186765 : List Nat := [1, 6, 3, 1, 1, 2, 8]
def baseStart_1186765 : Nat := 118140960795 + 1186765 * 2 ^ 59
def prefixEnd_1186765 : Nat := 4983230072969 + 3 ^ 40 * 1186765 * 2
def baseEnd_1186765 : Nat := 15046441208226037288387

theorem tailTrace_1186765 : CollatzResearch.WordTrace tailWord_1186765 prefixEnd_1186765 15046441208226037288387 := by
  unfold tailWord_1186765
  simp only [CollatzResearch.WordTrace]
  refine ⟨43284875545560563170665749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28856583697040375447110499 43284875545560563170665749)
  ·
    refine ⟨2028978541198151398624957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43284875545560563170665749 2028978541198151398624957)
    ·
      refine ⟨760866952949306774484359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2028978541198151398624957 760866952949306774484359)
      ·
        refine ⟨1141300429423960161726539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760866952949306774484359 1141300429423960161726539)
        ·
          refine ⟨1711950644135940242589809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141300429423960161726539 1711950644135940242589809)
          ·
            refine ⟨1283962983101955181942357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711950644135940242589809 1283962983101955181942357)
            ·
              refine ⟨15046441208226037288387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1283962983101955181942357 15046441208226037288387)
              ·
                rfl

theorem cell22_1186765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 8].length) (baseStart_1186765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186765 prefixEnd_1186765 := by exact prefixLift 1186765
  have htrace : WordTrace (prefixWord ++ tailWord_1186765) baseStart_1186765 baseEnd_1186765 := by
    simpa [prefixWord, tailWord_1186765, baseEnd_1186765] using wordTrace_append hprefix tailTrace_1186765
  have hstable : (prefixWord ++ tailWord_1186765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186765).length < 2 ^ (prefixWord ++ tailWord_1186765).sum := by decide
  have hdescent : baseEnd_1186765 < baseStart_1186765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186821 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 4]
def baseStart_1186821 : Nat := 118140960795 + 1186821 * 2 ^ 59
def prefixEnd_1186821 : Nat := 4983230072969 + 3 ^ 40 * 1186821 * 2
def baseEnd_1186821 : Nat := 135424360855512509128759

theorem tailTrace_1186821 : CollatzResearch.WordTrace tailWord_1186821 prefixEnd_1186821 135424360855512509128759 := by
  unfold tailWord_1186821
  simp only [CollatzResearch.WordTrace]
  refine ⟨43286918033357684734704317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28857945355571789823136211 43286918033357684734704317)
  ·
    refine ⟨16232594262509131775514119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43286918033357684734704317 16232594262509131775514119)
    ·
      refine ⟨24348891393763697663271179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16232594262509131775514119 24348891393763697663271179)
      ·
        refine ⟨36523337090645546494906769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24348891393763697663271179 36523337090645546494906769)
        ·
          refine ⟨27392502817984159871180077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36523337090645546494906769 27392502817984159871180077)
          ·
            refine ⟨10272188556744059951692529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27392502817984159871180077 10272188556744059951692529)
            ·
              refine ⟨7704141417558044963769397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10272188556744059951692529 7704141417558044963769397)
              ·
                refine ⟨722263257896066715353381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7704141417558044963769397 722263257896066715353381)
                ·
                  refine ⟨135424360855512509128759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722263257896066715353381 135424360855512509128759)
                  ·
                    rfl

theorem cell22_1186821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_1186821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186821 prefixEnd_1186821 := by exact prefixLift 1186821
  have htrace : WordTrace (prefixWord ++ tailWord_1186821) baseStart_1186821 baseEnd_1186821 := by
    simpa [prefixWord, tailWord_1186821, baseEnd_1186821] using wordTrace_append hprefix tailTrace_1186821
  have hstable : (prefixWord ++ tailWord_1186821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186821).length < 2 ^ (prefixWord ++ tailWord_1186821).sum := by decide
  have hdescent : baseEnd_1186821 < baseStart_1186821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186823 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 1, 4]
def baseStart_1186823 : Nat := 118140960795 + 1186823 * 2 ^ 59
def prefixEnd_1186823 : Nat := 4983230072969 + 3 ^ 40 * 1186823 * 2
def baseEnd_1186823 : Nat := 406273767207410188836271

theorem tailTrace_1186823 : CollatzResearch.WordTrace tailWord_1186823 prefixEnd_1186823 406273767207410188836271 := by
  unfold tailWord_1186823
  simp only [CollatzResearch.WordTrace]
  refine ⟨43286990979350439076277123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28857993986233626050851415 43286990979350439076277123)
  ·
    refine ⟨64930486469025658614415685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43286990979350439076277123 64930486469025658614415685)
    ·
      refine ⟨12174466212942310990202941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64930486469025658614415685 12174466212942310990202941)
      ·
        refine ⟨4565424829853366621326103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12174466212942310990202941 4565424829853366621326103)
        ·
          refine ⟨6848137244780049931989155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565424829853366621326103 6848137244780049931989155)
          ·
            refine ⟨10272205867170074897983733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848137244780049931989155 10272205867170074897983733)
            ·
              refine ⟨963019300047194521685975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10272205867170074897983733 963019300047194521685975)
              ·
                refine ⟨1444528950070791782528963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963019300047194521685975 1444528950070791782528963)
                ·
                  refine ⟨2166793425106187673793445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444528950070791782528963 2166793425106187673793445)
                  ·
                    refine ⟨406273767207410188836271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2166793425106187673793445 406273767207410188836271)
                    ·
                      rfl

theorem cell22_1186823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_1186823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186823 prefixEnd_1186823 := by exact prefixLift 1186823
  have htrace : WordTrace (prefixWord ++ tailWord_1186823) baseStart_1186823 baseEnd_1186823 := by
    simpa [prefixWord, tailWord_1186823, baseEnd_1186823] using wordTrace_append hprefix tailTrace_1186823
  have hstable : (prefixWord ++ tailWord_1186823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186823).length < 2 ^ (prefixWord ++ tailWord_1186823).sum := by decide
  have hdescent : baseEnd_1186823 < baseStart_1186823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186866 : List Nat := [3, 2, 1, 1, 2, 2, 5, 6]
def baseStart_1186866 : Nat := 118140960795 + 1186866 * 2 ^ 59
def prefixEnd_1186866 : Nat := 4983230072969 + 3 ^ 40 * 1186866 * 2
def baseEnd_1186866 : Nat := 45143165220685823334571

theorem tailTrace_1186866 : CollatzResearch.WordTrace tailWord_1186866 prefixEnd_1186866 45143165220685823334571 := by
  unfold tailWord_1186866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822139829548664355023113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28859039545463104946728301 10822139829548664355023113)
  ·
    refine ⟨8116604872161498266267335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10822139829548664355023113 8116604872161498266267335)
    ·
      refine ⟨12174907308242247399401003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116604872161498266267335 12174907308242247399401003)
      ·
        refine ⟨18262360962363371099101505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174907308242247399401003 18262360962363371099101505)
        ·
          refine ⟨13696770721772528324326129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18262360962363371099101505 13696770721772528324326129)
          ·
            refine ⟨10272578041329396243244597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13696770721772528324326129 10272578041329396243244597)
            ·
              refine ⟨963054191374630897804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10272578041329396243244597 963054191374630897804181)
              ·
                refine ⟨45143165220685823334571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 963054191374630897804181 45143165220685823334571)
                ·
                  rfl

theorem cell22_1186866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_1186866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186866 prefixEnd_1186866 := by exact prefixLift 1186866
  have htrace : WordTrace (prefixWord ++ tailWord_1186866) baseStart_1186866 baseEnd_1186866 := by
    simpa [prefixWord, tailWord_1186866, baseEnd_1186866] using wordTrace_append hprefix tailTrace_1186866
  have hstable : (prefixWord ++ tailWord_1186866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186866).length < 2 ^ (prefixWord ++ tailWord_1186866).sum := by decide
  have hdescent : baseEnd_1186866 < baseStart_1186866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186868 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1186868 : Nat := 118140960795 + 1186868 * 2 ^ 59
def prefixEnd_1186868 : Nat := 4983230072969 + 3 ^ 40 * 1186868 * 2
def baseEnd_1186868 : Nat := 406289171627045071461133

theorem tailTrace_1186868 : CollatzResearch.WordTrace tailWord_1186868 prefixEnd_1186868 406289171627045071461133 := by
  unfold tailWord_1186868
  simp only [CollatzResearch.WordTrace]
  refine ⟨21644316132093705880832629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28859088176124941174443505 21644316132093705880832629)
  ·
    refine ⟨2029154637383784926328059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21644316132093705880832629 2029154637383784926328059)
    ·
      refine ⟨3043731956075677389492089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029154637383784926328059 3043731956075677389492089)
      ·
        refine ⟨2282798967056758042119067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043731956075677389492089 2282798967056758042119067)
        ·
          refine ⟨3424198450585137063178601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282798967056758042119067 3424198450585137063178601)
          ·
            refine ⟨2568148837938852797383951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3424198450585137063178601 2568148837938852797383951)
            ·
              refine ⟨3852223256908279196075927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568148837938852797383951 3852223256908279196075927)
              ·
                refine ⟨5778334885362418794113891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852223256908279196075927 5778334885362418794113891)
                ·
                  refine ⟨8667502328043628191170837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5778334885362418794113891 8667502328043628191170837)
                  ·
                    refine ⟨406289171627045071461133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8667502328043628191170837 406289171627045071461133)
                    ·
                      rfl

theorem cell22_1186868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1186868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186868 prefixEnd_1186868 := by exact prefixLift 1186868
  have htrace : WordTrace (prefixWord ++ tailWord_1186868) baseStart_1186868 baseEnd_1186868 := by
    simpa [prefixWord, tailWord_1186868, baseEnd_1186868] using wordTrace_append hprefix tailTrace_1186868
  have hstable : (prefixWord ++ tailWord_1186868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186868).length < 2 ^ (prefixWord ++ tailWord_1186868).sum := by decide
  have hdescent : baseEnd_1186868 < baseStart_1186868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186898 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1186898 : Nat := 118140960795 + 1186898 * 2 ^ 59
def prefixEnd_1186898 : Nat := 4983230072969 + 3 ^ 40 * 1186898 * 2
def baseEnd_1186898 : Nat := 406299441240134993211041

theorem tailTrace_1186898 : CollatzResearch.WordTrace tailWord_1186898 prefixEnd_1186898 406299441240134993211041 := by
  unfold tailWord_1186898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822431613519681721314337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28859817636052484590171565 10822431613519681721314337)
  ·
    refine ⟨8116823710139761290985753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10822431613519681721314337 8116823710139761290985753)
    ·
      refine ⟨6087617782604820968239315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8116823710139761290985753 6087617782604820968239315)
      ·
        refine ⟨9131426673907231452358973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6087617782604820968239315 9131426673907231452358973)
        ·
          refine ⟨3424285002715211794634615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9131426673907231452358973 3424285002715211794634615)
          ·
            refine ⟨5136427504072817691951923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424285002715211794634615 5136427504072817691951923)
            ·
              refine ⟨7704641256109226537927885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136427504072817691951923 7704641256109226537927885)
              ·
                refine ⟨2889240471040959951722957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7704641256109226537927885 2889240471040959951722957)
                ·
                  refine ⟨1083465176640359981896109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2889240471040959951722957 1083465176640359981896109)
                  ·
                    refine ⟨406299441240134993211041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083465176640359981896109 406299441240134993211041)
                    ·
                      rfl

theorem cell22_1186898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1186898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186898 prefixEnd_1186898 := by exact prefixLift 1186898
  have htrace : WordTrace (prefixWord ++ tailWord_1186898) baseStart_1186898 baseEnd_1186898 := by
    simpa [prefixWord, tailWord_1186898, baseEnd_1186898] using wordTrace_append hprefix tailTrace_1186898
  have hstable : (prefixWord ++ tailWord_1186898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186898).length < 2 ^ (prefixWord ++ tailWord_1186898).sum := by decide
  have hdescent : baseEnd_1186898 < baseStart_1186898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186939 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 8]
def baseStart_1186939 : Nat := 118140960795 + 1186939 * 2 ^ 59
def prefixEnd_1186939 : Nat := 4983230072969 + 3 ^ 40 * 1186939 * 2
def baseEnd_1186939 : Nat := 135437825459341517645305

theorem tailTrace_1186939 : CollatzResearch.WordTrace tailWord_1186939 prefixEnd_1186939 135437825459341517645305 := by
  unfold tailWord_1186939
  simp only [CollatzResearch.WordTrace]
  refine ⟨43291221846930190887499871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28860814564620127258333247 43291221846930190887499871)
  ·
    refine ⟨64936832770395286331249807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43291221846930190887499871 64936832770395286331249807)
    ·
      refine ⟨97405249155592929496874711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64936832770395286331249807 97405249155592929496874711)
      ·
        refine ⟨146107873733389394245312067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97405249155592929496874711 146107873733389394245312067)
        ·
          refine ⟨219161810600084091367968101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146107873733389394245312067 219161810600084091367968101)
          ·
            refine ⟨41092839487515767131494019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219161810600084091367968101 41092839487515767131494019)
            ·
              refine ⟨61639259231273650697241029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41092839487515767131494019 61639259231273650697241029)
              ·
                refine ⟨11557361105863809505732693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61639259231273650697241029 11557361105863809505732693)
                ·
                  refine ⟨135437825459341517645305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11557361105863809505732693 135437825459341517645305)
                  ·
                    rfl

theorem cell22_1186939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_1186939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186939 prefixEnd_1186939 := by exact prefixLift 1186939
  have htrace : WordTrace (prefixWord ++ tailWord_1186939) baseStart_1186939 baseEnd_1186939 := by
    simpa [prefixWord, tailWord_1186939, baseEnd_1186939] using wordTrace_append hprefix tailTrace_1186939
  have hstable : (prefixWord ++ tailWord_1186939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186939).length < 2 ^ (prefixWord ++ tailWord_1186939).sum := by decide
  have hdescent : baseEnd_1186939 < baseStart_1186939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186971 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 8, 3]
def baseStart_1186971 : Nat := 118140960795 + 1186971 * 2 ^ 59
def prefixEnd_1186971 : Nat := 4983230072969 + 3 ^ 40 * 1186971 * 2
def baseEnd_1186971 : Nat := 406324430631987136135817

theorem tailTrace_1186971 : CollatzResearch.WordTrace tailWord_1186971 prefixEnd_1186971 406324430631987136135817 := by
  unfold tailWord_1186971
  simp only [CollatzResearch.WordTrace]
  refine ⟨43292388982814260352664767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28861592655209506901776511 43292388982814260352664767)
  ·
    refine ⟨64938583474221390528997151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43292388982814260352664767 64938583474221390528997151)
    ·
      refine ⟨97407875211332085793495727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64938583474221390528997151 97407875211332085793495727)
      ·
        refine ⟨146111812816998128690243591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97407875211332085793495727 146111812816998128690243591)
        ·
          refine ⟨219167719225497193035365387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146111812816998128690243591 219167719225497193035365387)
          ·
            refine ⟨328751578838245789553048081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219167719225497193035365387 328751578838245789553048081)
            ·
              refine ⟨246563684128684342164786061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328751578838245789553048081 246563684128684342164786061)
              ·
                refine ⟨92461381548256628311794773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246563684128684342164786061 92461381548256628311794773)
                ·
                  refine ⟨1083531815018632363028845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 92461381548256628311794773 1083531815018632363028845)
                  ·
                    refine ⟨406324430631987136135817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083531815018632363028845 406324430631987136135817)
                    ·
                      rfl

theorem cell22_1186971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 3].length) (baseStart_1186971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1186971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1186971 prefixEnd_1186971 := by exact prefixLift 1186971
  have htrace : WordTrace (prefixWord ++ tailWord_1186971) baseStart_1186971 baseEnd_1186971 := by
    simpa [prefixWord, tailWord_1186971, baseEnd_1186971] using wordTrace_append hprefix tailTrace_1186971
  have hstable : (prefixWord ++ tailWord_1186971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186971).length < 2 ^ (prefixWord ++ tailWord_1186971).sum := by decide
  have hdescent : baseEnd_1186971 < baseStart_1186971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187018 : List Nat := [3, 1, 2, 1, 3, 4, 1, 7]
def baseStart_1187018 : Nat := 118140960795 + 1187018 * 2 ^ 59
def prefixEnd_1187018 : Nat := 4983230072969 + 3 ^ 40 * 1187018 * 2
def baseEnd_1187018 : Nat := 45148946632499408912297

theorem tailTrace_1187018 : CollatzResearch.WordTrace tailWord_1187018 prefixEnd_1187018 45148946632499408912297 := by
  unfold tailWord_1187018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823525803410996844906427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28862735475762658253083805 10823525803410996844906427)
  ·
    refine ⟨16235288705116495267359641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10823525803410996844906427 16235288705116495267359641)
    ·
      refine ⟨12176466528837371450519731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16235288705116495267359641 12176466528837371450519731)
      ·
        refine ⟨18264699793256057175779597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12176466528837371450519731 18264699793256057175779597)
        ·
          refine ⟨6849262422471021440917349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18264699793256057175779597 6849262422471021440917349)
          ·
            refine ⟨1284236704213316520172003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6849262422471021440917349 1284236704213316520172003)
            ·
              refine ⟨1926355056319974780258005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284236704213316520172003 1926355056319974780258005)
              ·
                refine ⟨45148946632499408912297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1926355056319974780258005 45148946632499408912297)
                ·
                  rfl

theorem cell22_1187018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_1187018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187018 prefixEnd_1187018 := by exact prefixLift 1187018
  have htrace : WordTrace (prefixWord ++ tailWord_1187018) baseStart_1187018 baseEnd_1187018 := by
    simpa [prefixWord, tailWord_1187018, baseEnd_1187018] using wordTrace_append hprefix tailTrace_1187018
  have hstable : (prefixWord ++ tailWord_1187018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187018).length < 2 ^ (prefixWord ++ tailWord_1187018).sum := by decide
  have hdescent : baseEnd_1187018 < baseStart_1187018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187037 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1187037 : Nat := 118140960795 + 1187037 * 2 ^ 59
def prefixEnd_1187037 : Nat := 4983230072969 + 3 ^ 40 * 1187037 * 2
def baseEnd_1187037 : Nat := 406347023780784963985615

theorem tailTrace_1187037 : CollatzResearch.WordTrace tailWord_1187037 prefixEnd_1187037 406347023780784963985615 := by
  unfold tailWord_1187037
  simp only [CollatzResearch.WordTrace]
  refine ⟨43294796200575153624567365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28863197467050102416378243 43294796200575153624567365)
  ·
    refine ⟨8117774287607841304606381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43294796200575153624567365 8117774287607841304606381)
    ·
      refine ⟨3044165357852940489227393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8117774287607841304606381 3044165357852940489227393)
      ·
        refine ⟨2283124018389705366920545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044165357852940489227393 2283124018389705366920545)
        ·
          refine ⟨1712343013792279025190409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283124018389705366920545 1712343013792279025190409)
          ·
            refine ⟨1284257260344209268892807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712343013792279025190409 1284257260344209268892807)
            ·
              refine ⟨1926385890516313903339211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284257260344209268892807 1926385890516313903339211)
              ·
                refine ⟨2889578835774470855008817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926385890516313903339211 2889578835774470855008817)
                ·
                  refine ⟨2167184126830853141256613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889578835774470855008817 2167184126830853141256613)
                  ·
                    refine ⟨406347023780784963985615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2167184126830853141256613 406347023780784963985615)
                    ·
                      rfl

theorem cell22_1187037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1187037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187037 prefixEnd_1187037 := by exact prefixLift 1187037
  have htrace : WordTrace (prefixWord ++ tailWord_1187037) baseStart_1187037 baseEnd_1187037 := by
    simpa [prefixWord, tailWord_1187037, baseEnd_1187037] using wordTrace_append hprefix tailTrace_1187037
  have hstable : (prefixWord ++ tailWord_1187037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187037).length < 2 ^ (prefixWord ++ tailWord_1187037).sum := by decide
  have hdescent : baseEnd_1187037 < baseStart_1187037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187125 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 6]
def baseStart_1187125 : Nat := 118140960795 + 1187125 * 2 ^ 59
def prefixEnd_1187125 : Nat := 4983230072969 + 3 ^ 40 * 1187125 * 2
def baseEnd_1187125 : Nat := 135459049326394022595115

theorem tailTrace_1187125 : CollatzResearch.WordTrace tailWord_1187125 prefixEnd_1187125 135459049326394022595115 := by
  unfold tailWord_1187125
  simp only [CollatzResearch.WordTrace]
  refine ⟨43298005824256344653770829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28865337216170896435847219 43298005824256344653770829)
  ·
    refine ⟨16236752184096129245164061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43298005824256344653770829 16236752184096129245164061)
    ·
      refine ⟨6088782069036048466936523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16236752184096129245164061 6088782069036048466936523)
      ·
        refine ⟨9133173103554072700404785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088782069036048466936523 9133173103554072700404785)
        ·
          refine ⟨6849879827665554525303589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9133173103554072700404785 6849879827665554525303589)
          ·
            refine ⟨1284352467687291473494423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6849879827665554525303589 1284352467687291473494423)
            ·
              refine ⟨1926528701530937210241635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284352467687291473494423 1926528701530937210241635)
              ·
                refine ⟨2889793052296405815362453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926528701530937210241635 2889793052296405815362453)
                ·
                  refine ⟨135459049326394022595115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2889793052296405815362453 135459049326394022595115)
                  ·
                    rfl

theorem cell22_1187125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_1187125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187125 prefixEnd_1187125 := by exact prefixLift 1187125
  have htrace : WordTrace (prefixWord ++ tailWord_1187125) baseStart_1187125 baseEnd_1187125 := by
    simpa [prefixWord, tailWord_1187125, baseEnd_1187125] using wordTrace_append hprefix tailTrace_1187125
  have hstable : (prefixWord ++ tailWord_1187125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187125).length < 2 ^ (prefixWord ++ tailWord_1187125).sum := by decide
  have hdescent : baseEnd_1187125 < baseStart_1187125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187176 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_1187176 : Nat := 118140960795 + 1187176 * 2 ^ 59
def prefixEnd_1187176 : Nat := 4983230072969 + 3 ^ 40 * 1187176 * 2
def baseEnd_1187176 : Nat := 135464868773811644920063

theorem tailTrace_1187176 : CollatzResearch.WordTrace tailWord_1187176 prefixEnd_1187176 135464868773811644920063 := by
  unfold tailWord_1187176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649932973535790181938691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28866577298047720242584921 21649932973535790181938691)
  ·
    refine ⟨32474899460303685272908037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21649932973535790181938691 32474899460303685272908037)
    ·
      refine ⟨6089043648806940988670257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32474899460303685272908037 6089043648806940988670257)
      ·
        refine ⟨4566782736605205741502693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089043648806940988670257 4566782736605205741502693)
        ·
          refine ⟨856271763113476076531755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4566782736605205741502693 856271763113476076531755)
          ·
            refine ⟨1284407644670214114797633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856271763113476076531755 1284407644670214114797633)
            ·
              refine ⟨963305733502660586098225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284407644670214114797633 963305733502660586098225)
              ·
                refine ⟨722479300126995439573669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963305733502660586098225 722479300126995439573669)
                ·
                  refine ⟨135464868773811644920063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722479300126995439573669 135464868773811644920063)
                  ·
                    rfl

theorem cell22_1187176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_1187176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187176 prefixEnd_1187176 := by exact prefixLift 1187176
  have htrace : WordTrace (prefixWord ++ tailWord_1187176) baseStart_1187176 baseEnd_1187176 := by
    simpa [prefixWord, tailWord_1187176, baseEnd_1187176] using wordTrace_append hprefix tailTrace_1187176
  have hstable : (prefixWord ++ tailWord_1187176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187176).length < 2 ^ (prefixWord ++ tailWord_1187176).sum := by decide
  have hdescent : baseEnd_1187176 < baseStart_1187176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187275 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 4, 3]
def baseStart_1187275 : Nat := 118140960795 + 1187275 * 2 ^ 59
def prefixEnd_1187275 : Nat := 4983230072969 + 3 ^ 40 * 1187275 * 2
def baseEnd_1187275 : Nat := 406428496044631676534885

theorem tailTrace_1187275 : CollatzResearch.WordTrace tailWord_1187275 prefixEnd_1187275 406428496044631676534885 := by
  unfold tailWord_1187275
  simp only [CollatzResearch.WordTrace]
  refine ⟨43303476773712920271731279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28868984515808613514487519 43303476773712920271731279)
  ·
    refine ⟨64955215160569380407596919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43303476773712920271731279 64955215160569380407596919)
    ·
      refine ⟨97432822740854070611395379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64955215160569380407596919 97432822740854070611395379)
      ·
        refine ⟨146149234111281105917093069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97432822740854070611395379 146149234111281105917093069)
        ·
          refine ⟨54805962791730414718909901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146149234111281105917093069 54805962791730414718909901)
          ·
            refine ⟨20552236046898905519591213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54805962791730414718909901 20552236046898905519591213)
            ·
              refine ⟨7707088517587089569846705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20552236046898905519591213 7707088517587089569846705)
              ·
                refine ⟨5780316388190317177385029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7707088517587089569846705 5780316388190317177385029)
                ·
                  refine ⟨1083809322785684470759693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5780316388190317177385029 1083809322785684470759693)
                  ·
                    refine ⟨406428496044631676534885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083809322785684470759693 406428496044631676534885)
                    ·
                      rfl

theorem cell22_1187275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 3].length) (baseStart_1187275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187275 prefixEnd_1187275 := by exact prefixLift 1187275
  have htrace : WordTrace (prefixWord ++ tailWord_1187275) baseStart_1187275 baseEnd_1187275 := by
    simpa [prefixWord, tailWord_1187275, baseEnd_1187275] using wordTrace_append hprefix tailTrace_1187275
  have hstable : (prefixWord ++ tailWord_1187275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187275).length < 2 ^ (prefixWord ++ tailWord_1187275).sum := by decide
  have hdescent : baseEnd_1187275 < baseStart_1187275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187288 : List Nat := [2, 1, 2, 2, 2, 1, 12]
def baseStart_1187288 : Nat := 118140960795 + 1187288 * 2 ^ 59
def prefixEnd_1187288 : Nat := 4983230072969 + 3 ^ 40 * 1187288 * 2
def baseEnd_1187288 : Nat := 15053072081863110220735

theorem tailTrace_1187288 : CollatzResearch.WordTrace tailWord_1187288 prefixEnd_1187288 15053072081863110220735 := by
  unfold tailWord_1187288
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651975461332911745977259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28869300615110548994636345 21651975461332911745977259)
  ·
    refine ⟨32477963191999367618965889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21651975461332911745977259 32477963191999367618965889)
    ·
      refine ⟨24358472393999525714224417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32477963191999367618965889 24358472393999525714224417)
      ·
        refine ⟨18268854295499644285668313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24358472393999525714224417 18268854295499644285668313)
        ·
          refine ⟨13701640721624733214251235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18268854295499644285668313 13701640721624733214251235)
          ·
            refine ⟨20552461082437099821376853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13701640721624733214251235 20552461082437099821376853)
            ·
              refine ⟨15053072081863110220735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20552461082437099821376853 15053072081863110220735)
              ·
                rfl

theorem cell22_1187288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 12].length) (baseStart_1187288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187288 prefixEnd_1187288 := by exact prefixLift 1187288
  have htrace : WordTrace (prefixWord ++ tailWord_1187288) baseStart_1187288 baseEnd_1187288 := by
    simpa [prefixWord, tailWord_1187288, baseEnd_1187288] using wordTrace_append hprefix tailTrace_1187288
  have hstable : (prefixWord ++ tailWord_1187288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187288).length < 2 ^ (prefixWord ++ tailWord_1187288).sum := by decide
  have hdescent : baseEnd_1187288 < baseStart_1187288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187290 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_1187290 : Nat := 118140960795 + 1187290 * 2 ^ 59
def prefixEnd_1187290 : Nat := 4983230072969 + 3 ^ 40 * 1187290 * 2
def baseEnd_1187290 : Nat := 406433630851176637409839

theorem tailTrace_1187290 : CollatzResearch.WordTrace tailWord_1187290 prefixEnd_1187290 406433630851176637409839 := by
  unfold tailWord_1187290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826005967164644458381831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28869349245772385222351549 10826005967164644458381831)
  ·
    refine ⟨16239008950746966687572747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10826005967164644458381831 16239008950746966687572747)
    ·
      refine ⟨24358513426120450031359121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16239008950746966687572747 24358513426120450031359121)
      ·
        refine ⟨18268885069590337523519341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24358513426120450031359121 18268885069590337523519341)
        ·
          refine ⟨6850831901096376571319753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18268885069590337523519341 6850831901096376571319753)
          ·
            refine ⟨5138123925822282428489815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6850831901096376571319753 5138123925822282428489815)
            ·
              refine ⟨7707185888733423642734723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138123925822282428489815 7707185888733423642734723)
              ·
                refine ⟨11560778833100135464102085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707185888733423642734723 11560778833100135464102085)
                ·
                  refine ⟨2167646031206275399519141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11560778833100135464102085 2167646031206275399519141)
                  ·
                    refine ⟨406433630851176637409839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2167646031206275399519141 406433630851176637409839)
                    ·
                      rfl

theorem cell22_1187290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_1187290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187290 prefixEnd_1187290 := by exact prefixLift 1187290
  have htrace : WordTrace (prefixWord ++ tailWord_1187290) baseStart_1187290 baseEnd_1187290 := by
    simpa [prefixWord, tailWord_1187290, baseEnd_1187290] using wordTrace_append hprefix tailTrace_1187290
  have hstable : (prefixWord ++ tailWord_1187290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187290).length < 2 ^ (prefixWord ++ tailWord_1187290).sum := by decide
  have hdescent : baseEnd_1187290 < baseStart_1187290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187397 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_1187397 : Nat := 118140960795 + 1187397 * 2 ^ 59
def prefixEnd_1187397 : Nat := 4983230072969 + 3 ^ 40 * 1187397 * 2
def baseEnd_1187397 : Nat := 406470259137864024984511

theorem tailTrace_1187397 : CollatzResearch.WordTrace tailWord_1187397 prefixEnd_1187397 406470259137864024984511 := by
  unfold tailWord_1187397
  simp only [CollatzResearch.WordTrace]
  refine ⟨43307926479270935107672445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28871950986180623405114963 43307926479270935107672445)
  ·
    refine ⟨16240472429726600665377167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43307926479270935107672445 16240472429726600665377167)
    ·
      refine ⟨24360708644589900998065751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16240472429726600665377167 24360708644589900998065751)
      ·
        refine ⟨36541062966884851497098627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24360708644589900998065751 36541062966884851497098627)
        ·
          refine ⟨54811594450327277245647941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36541062966884851497098627 54811594450327277245647941)
          ·
            refine ⟨10277173959436364483558989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54811594450327277245647941 10277173959436364483558989)
            ·
              refine ⟨3853940234788636681334621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10277173959436364483558989 3853940234788636681334621)
              ·
                refine ⟨1445227588045738755500483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3853940234788636681334621 1445227588045738755500483)
                ·
                  refine ⟨2167841382068608133250725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445227588045738755500483 2167841382068608133250725)
                  ·
                    refine ⟨406470259137864024984511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2167841382068608133250725 406470259137864024984511)
                    ·
                      rfl

theorem cell22_1187397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_1187397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187397 prefixEnd_1187397 := by exact prefixLift 1187397
  have htrace : WordTrace (prefixWord ++ tailWord_1187397) baseStart_1187397 baseEnd_1187397 := by
    simpa [prefixWord, tailWord_1187397, baseEnd_1187397] using wordTrace_append hprefix tailTrace_1187397
  have hstable : (prefixWord ++ tailWord_1187397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187397).length < 2 ^ (prefixWord ++ tailWord_1187397).sum := by decide
  have hdescent : baseEnd_1187397 < baseStart_1187397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187412 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1187412 : Nat := 118140960795 + 1187412 * 2 ^ 59
def prefixEnd_1187412 : Nat := 4983230072969 + 3 ^ 40 * 1187412 * 2
def baseEnd_1187412 : Nat := 135491797981469661953155

theorem tailTrace_1187412 : CollatzResearch.WordTrace tailWord_1187412 prefixEnd_1187412 135491797981469661953155 := by
  unfold tailWord_1187412
  simp only [CollatzResearch.WordTrace]
  refine ⟨21654236787108296334734245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28872315716144395112978993 21654236787108296334734245)
  ·
    refine ⟨4060169397582805562762671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21654236787108296334734245 4060169397582805562762671)
    ·
      refine ⟨6090254096374208344144007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060169397582805562762671 6090254096374208344144007)
      ·
        refine ⟨9135381144561312516216011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6090254096374208344144007 9135381144561312516216011)
        ·
          refine ⟨13703071716841968774324017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9135381144561312516216011 13703071716841968774324017)
          ·
            refine ⟨10277303787631476580743013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13703071716841968774324017 10277303787631476580743013)
            ·
              refine ⟨1926994460180901858889315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10277303787631476580743013 1926994460180901858889315)
              ·
                refine ⟨2890491690271352788333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926994460180901858889315 2890491690271352788333973)
                ·
                  refine ⟨135491797981469661953155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2890491690271352788333973 135491797981469661953155)
                  ·
                    rfl

theorem cell22_1187412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1187412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187412 prefixEnd_1187412 := by exact prefixLift 1187412
  have htrace : WordTrace (prefixWord ++ tailWord_1187412) baseStart_1187412 baseEnd_1187412 := by
    simpa [prefixWord, tailWord_1187412, baseEnd_1187412] using wordTrace_append hprefix tailTrace_1187412
  have hstable : (prefixWord ++ tailWord_1187412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187412).length < 2 ^ (prefixWord ++ tailWord_1187412).sum := by decide
  have hdescent : baseEnd_1187412 < baseStart_1187412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187425 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1187425 : Nat := 118140960795 + 1187425 * 2 ^ 59
def prefixEnd_1187425 : Nat := 4983230072969 + 3 ^ 40 * 1187425 * 2
def baseEnd_1187425 : Nat := 406479844110081285284425

theorem tailTrace_1187425 : CollatzResearch.WordTrace tailWord_1187425 prefixEnd_1187425 406479844110081285284425 := by
  unfold tailWord_1187425
  simp only [CollatzResearch.WordTrace]
  refine ⟨43308947723169495889691729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28872631815446330593127819 43308947723169495889691729)
  ·
    refine ⟨32481710792377121917268797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43308947723169495889691729 32481710792377121917268797)
    ·
      refine ⟨12180641547141420718975799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32481710792377121917268797 12180641547141420718975799)
      ·
        refine ⟨18270962320712131078463699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12180641547141420718975799 18270962320712131078463699)
        ·
          refine ⟨27406443481068196617695549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18270962320712131078463699 27406443481068196617695549)
          ·
            refine ⟨10277416305400573731635831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27406443481068196617695549 10277416305400573731635831)
            ·
              refine ⟨15416124458100860597453747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10277416305400573731635831 15416124458100860597453747)
              ·
                refine ⟨23124186687151290896180621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15416124458100860597453747 23124186687151290896180621)
                ·
                  refine ⟨8671570007681734086067733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23124186687151290896180621 8671570007681734086067733)
                  ·
                    refine ⟨406479844110081285284425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8671570007681734086067733 406479844110081285284425)
                    ·
                      rfl

theorem cell22_1187425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1187425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187425 prefixEnd_1187425 := by exact prefixLift 1187425
  have htrace : WordTrace (prefixWord ++ tailWord_1187425) baseStart_1187425 baseEnd_1187425 := by
    simpa [prefixWord, tailWord_1187425, baseEnd_1187425] using wordTrace_append hprefix tailTrace_1187425
  have hstable : (prefixWord ++ tailWord_1187425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187425).length < 2 ^ (prefixWord ++ tailWord_1187425).sum := by decide
  have hdescent : baseEnd_1187425 < baseStart_1187425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187427 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 1, 5]
def baseStart_1187427 : Nat := 118140960795 + 1187427 * 2 ^ 59
def prefixEnd_1187427 : Nat := 4983230072969 + 3 ^ 40 * 1187427 * 2
def baseEnd_1187427 : Nat := 406480528750953946734419

theorem tailTrace_1187427 : CollatzResearch.WordTrace tailWord_1187427 prefixEnd_1187427 406480528750953946734419 := by
  unfold tailWord_1187427
  simp only [CollatzResearch.WordTrace]
  refine ⟨43309020669162250231264535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28872680446108166820843023 43309020669162250231264535)
  ·
    refine ⟨64963531003743375346896803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43309020669162250231264535 64963531003743375346896803)
    ·
      refine ⟨97445296505615063020345205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64963531003743375346896803 97445296505615063020345205)
      ·
        refine ⟨9135496547401412158157363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97445296505615063020345205 9135496547401412158157363)
        ·
          refine ⟨13703244821102118237236045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9135496547401412158157363 13703244821102118237236045)
          ·
            refine ⟨5138716807913294338963517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13703244821102118237236045 5138716807913294338963517)
            ·
              refine ⟨1927018802967485377111319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5138716807913294338963517 1927018802967485377111319)
              ·
                refine ⟨2890528204451228065666979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927018802967485377111319 2890528204451228065666979)
                ·
                  refine ⟨4335792306676842098500469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890528204451228065666979 4335792306676842098500469)
                  ·
                    refine ⟨406480528750953946734419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4335792306676842098500469 406480528750953946734419)
                    ·
                      rfl

theorem cell22_1187427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_1187427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187427 prefixEnd_1187427 := by exact prefixLift 1187427
  have htrace : WordTrace (prefixWord ++ tailWord_1187427) baseStart_1187427 baseEnd_1187427 := by
    simpa [prefixWord, tailWord_1187427, baseEnd_1187427] using wordTrace_append hprefix tailTrace_1187427
  have hstable : (prefixWord ++ tailWord_1187427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187427).length < 2 ^ (prefixWord ++ tailWord_1187427).sum := by decide
  have hdescent : baseEnd_1187427 < baseStart_1187427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187442 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1187442 : Nat := 118140960795 + 1187442 * 2 ^ 59
def prefixEnd_1187442 : Nat := 4983230072969 + 3 ^ 40 * 1187442 * 2
def baseEnd_1187442 : Nat := 406485663557498907609373

theorem tailTrace_1187442 : CollatzResearch.WordTrace tailWord_1187442 prefixEnd_1187442 406485663557498907609373 := by
  unfold tailWord_1187442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827391941026976948265145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28873045176071938528707053 10827391941026976948265145)
  ·
    refine ⟨8120543955770232711198859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10827391941026976948265145 8120543955770232711198859)
    ·
      refine ⟨12180815933655349066798289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8120543955770232711198859 12180815933655349066798289)
      ·
        refine ⟨9135611950241511800098717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12180815933655349066798289 9135611950241511800098717)
        ·
          refine ⟨3425854481340566925037019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9135611950241511800098717 3425854481340566925037019)
          ·
            refine ⟨5138781722010850387555529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425854481340566925037019 5138781722010850387555529)
            ·
              refine ⟨3854086291508137790666647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138781722010850387555529 3854086291508137790666647)
              ·
                refine ⟨5781129437262206685999971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854086291508137790666647 5781129437262206685999971)
                ·
                  refine ⟨8671694155893310028999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5781129437262206685999971 8671694155893310028999957)
                  ·
                    refine ⟨406485663557498907609373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8671694155893310028999957 406485663557498907609373)
                    ·
                      rfl

theorem cell22_1187442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1187442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187442 prefixEnd_1187442 := by exact prefixLift 1187442
  have htrace : WordTrace (prefixWord ++ tailWord_1187442) baseStart_1187442 baseEnd_1187442 := by
    simpa [prefixWord, tailWord_1187442, baseEnd_1187442] using wordTrace_append hprefix tailTrace_1187442
  have hstable : (prefixWord ++ tailWord_1187442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187442).length < 2 ^ (prefixWord ++ tailWord_1187442).sum := by decide
  have hdescent : baseEnd_1187442 < baseStart_1187442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187446 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1187446 : Nat := 118140960795 + 1187446 * 2 ^ 59
def prefixEnd_1187446 : Nat := 4983230072969 + 3 ^ 40 * 1187446 * 2
def baseEnd_1187446 : Nat := 135495677613081410169787

theorem tailTrace_1187446 : CollatzResearch.WordTrace tailWord_1187446 prefixEnd_1187446 135495677613081410169787 := by
  unfold tailWord_1187446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706857103505838529762887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28873142437395610984137461 2706857103505838529762887)
  ·
    refine ⟨4060285655258757794644331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2706857103505838529762887 4060285655258757794644331)
    ·
      refine ⟨6090428482888136691966497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060285655258757794644331 6090428482888136691966497)
      ·
        refine ⟨4567821362166102518974873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6090428482888136691966497 4567821362166102518974873)
        ·
          refine ⟨3425866021624576889231155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567821362166102518974873 3425866021624576889231155)
          ·
            refine ⟨5138799032436865333846733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425866021624576889231155 5138799032436865333846733)
            ·
              refine ⟨1927049637163824500192525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5138799032436865333846733 1927049637163824500192525)
              ·
                refine ⟨722643613936434187572197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1927049637163824500192525 722643613936434187572197)
                ·
                  refine ⟨135495677613081410169787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722643613936434187572197 135495677613081410169787)
                  ·
                    rfl

theorem cell22_1187446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1187446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187446 prefixEnd_1187446 := by exact prefixLift 1187446
  have htrace : WordTrace (prefixWord ++ tailWord_1187446) baseStart_1187446 baseEnd_1187446 := by
    simpa [prefixWord, tailWord_1187446, baseEnd_1187446] using wordTrace_append hprefix tailTrace_1187446
  have hstable : (prefixWord ++ tailWord_1187446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187446).length < 2 ^ (prefixWord ++ tailWord_1187446).sum := by decide
  have hdescent : baseEnd_1187446 < baseStart_1187446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187457 : List Nat := [1, 2, 4, 2, 1, 4, 8]
def baseStart_1187457 : Nat := 118140960795 + 1187457 * 2 ^ 59
def prefixEnd_1187457 : Nat := 4983230072969 + 3 ^ 40 * 1187457 * 2
def baseEnd_1187457 : Nat := 15055214754223846980901

theorem tailTrace_1187457 : CollatzResearch.WordTrace tailWord_1187457 prefixEnd_1187457 15055214754223846980901 := by
  unfold tailWord_1187457
  simp only [CollatzResearch.WordTrace]
  refine ⟨43310114859053565354856625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28873409906035710236571083 43310114859053565354856625)
  ·
    refine ⟨32482586144290174016142469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43310114859053565354856625 32482586144290174016142469)
    ·
      refine ⟨6090484902054407628026713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32482586144290174016142469 6090484902054407628026713)
      ·
        refine ⟨4567863676540805721020035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6090484902054407628026713 4567863676540805721020035)
        ·
          refine ⟨6851795514811208581530053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567863676540805721020035 6851795514811208581530053)
          ·
            refine ⟨1284711659027101609036885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6851795514811208581530053 1284711659027101609036885)
            ·
              refine ⟨15055214754223846980901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1284711659027101609036885 15055214754223846980901)
              ·
                rfl

theorem cell22_1187457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 8].length) (baseStart_1187457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187457 prefixEnd_1187457 := by exact prefixLift 1187457
  have htrace : WordTrace (prefixWord ++ tailWord_1187457) baseStart_1187457 baseEnd_1187457 := by
    simpa [prefixWord, tailWord_1187457, baseEnd_1187457] using wordTrace_append hprefix tailTrace_1187457
  have hstable : (prefixWord ++ tailWord_1187457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187457).length < 2 ^ (prefixWord ++ tailWord_1187457).sum := by decide
  have hdescent : baseEnd_1187457 < baseStart_1187457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187474 : List Nat := [3, 2, 3, 1, 3, 1, 2, 7]
def baseStart_1187474 : Nat := 118140960795 + 1187474 * 2 ^ 59
def prefixEnd_1187474 : Nat := 4983230072969 + 3 ^ 40 * 1187474 * 2
def baseEnd_1187474 : Nat := 45166290867940165645475

theorem tailTrace_1187474 : CollatzResearch.WordTrace tailWord_1187474 prefixEnd_1187474 45166290867940165645475 := by
  unfold tailWord_1187474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827683724997994314556369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28873823266661318172150317 10827683724997994314556369)
  ·
    refine ⟨8120762793748495735917277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10827683724997994314556369 8120762793748495735917277)
    ·
      refine ⟨3045286047655685900968979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8120762793748495735917277 3045286047655685900968979)
      ·
        refine ⟨4567929071483528851453469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045286047655685900968979 4567929071483528851453469)
        ·
          refine ⟨1712973401806323319295051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4567929071483528851453469 1712973401806323319295051)
          ·
            refine ⟨2569460102709484978942577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712973401806323319295051 2569460102709484978942577)
            ·
              refine ⟨1927095077032113734206933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569460102709484978942577 1927095077032113734206933)
              ·
                refine ⟨45166290867940165645475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1927095077032113734206933 45166290867940165645475)
                ·
                  rfl

theorem cell22_1187474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_1187474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187474 prefixEnd_1187474 := by exact prefixLift 1187474
  have htrace : WordTrace (prefixWord ++ tailWord_1187474) baseStart_1187474 baseEnd_1187474 := by
    simpa [prefixWord, tailWord_1187474, baseEnd_1187474] using wordTrace_append hprefix tailTrace_1187474
  have hstable : (prefixWord ++ tailWord_1187474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187474).length < 2 ^ (prefixWord ++ tailWord_1187474).sum := by decide
  have hdescent : baseEnd_1187474 < baseStart_1187474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187517 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1187517 : Nat := 118140960795 + 1187517 * 2 ^ 59
def prefixEnd_1187517 : Nat := 4983230072969 + 3 ^ 40 * 1187517 * 2
def baseEnd_1187517 : Nat := 406511337590223711984143

theorem tailTrace_1187517 : CollatzResearch.WordTrace tailWord_1187517 prefixEnd_1187517 406511337590223711984143 := by
  unfold tailWord_1187517
  simp only [CollatzResearch.WordTrace]
  refine ⟨43312303238836195602040805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28874868825890797068027203 43312303238836195602040805)
  ·
    refine ⟨8121056857281786675382651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43312303238836195602040805 8121056857281786675382651)
    ·
      refine ⟨12181585285922680013073977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8121056857281786675382651 12181585285922680013073977)
      ·
        refine ⟨9136188964442010009805483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12181585285922680013073977 9136188964442010009805483)
        ·
          refine ⟨13704283446663015014708225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136188964442010009805483 13704283446663015014708225)
          ·
            refine ⟨10278212584997261261031169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13704283446663015014708225 10278212584997261261031169)
            ·
              refine ⟨7708659438747945945773377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10278212584997261261031169 7708659438747945945773377)
              ·
                refine ⟨5781494579060959459330033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7708659438747945945773377 5781494579060959459330033)
                ·
                  refine ⟨4336120934295719594497525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781494579060959459330033 4336120934295719594497525)
                  ·
                    refine ⟨406511337590223711984143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4336120934295719594497525 406511337590223711984143)
                    ·
                      rfl

theorem cell22_1187517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1187517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187517 prefixEnd_1187517 := by exact prefixLift 1187517
  have htrace : WordTrace (prefixWord ++ tailWord_1187517) baseStart_1187517 baseEnd_1187517 := by
    simpa [prefixWord, tailWord_1187517, baseEnd_1187517] using wordTrace_append hprefix tailTrace_1187517
  have hstable : (prefixWord ++ tailWord_1187517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187517).length < 2 ^ (prefixWord ++ tailWord_1187517).sum := by decide
  have hdescent : baseEnd_1187517 < baseStart_1187517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187564 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_1187564 : Nat := 118140960795 + 1187564 * 2 ^ 59
def prefixEnd_1187564 : Nat := 4983230072969 + 3 ^ 40 * 1187564 * 2
def baseEnd_1187564 : Nat := 135509142216910418686333

theorem tailTrace_1187564 : CollatzResearch.WordTrace tailWord_1187564 prefixEnd_1187564 135509142216910418686333 := by
  unfold tailWord_1187564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21657008734832961314500873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28876011646443948419334497 21657008734832961314500873)
  ·
    refine ⟨16242756551124720985875655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21657008734832961314500873 16242756551124720985875655)
    ·
      refine ⟨24364134826687081478813483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16242756551124720985875655 24364134826687081478813483)
      ·
        refine ⟨36546202240030622218220225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24364134826687081478813483 36546202240030622218220225)
        ·
          refine ⟨27409651680022966663665169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36546202240030622218220225 27409651680022966663665169)
          ·
            refine ⟨20557238760017224997748877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27409651680022966663665169 20557238760017224997748877)
            ·
              refine ⟨7708964535006459374155829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20557238760017224997748877 7708964535006459374155829)
              ·
                refine ⟨722715425156855566327109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7708964535006459374155829 722715425156855566327109)
                ·
                  refine ⟨135509142216910418686333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722715425156855566327109 135509142216910418686333)
                  ·
                    rfl

theorem cell22_1187564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_1187564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187564 prefixEnd_1187564 := by exact prefixLift 1187564
  have htrace : WordTrace (prefixWord ++ tailWord_1187564) baseStart_1187564 baseEnd_1187564 := by
    simpa [prefixWord, tailWord_1187564, baseEnd_1187564] using wordTrace_append hprefix tailTrace_1187564
  have hstable : (prefixWord ++ tailWord_1187564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187564).length < 2 ^ (prefixWord ++ tailWord_1187564).sum := by decide
  have hdescent : baseEnd_1187564 < baseStart_1187564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187579 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 2, 3]
def baseStart_1187579 : Nat := 118140960795 + 1187579 * 2 ^ 59
def prefixEnd_1187579 : Nat := 4983230072969 + 3 ^ 40 * 1187579 * 2
def baseEnd_1187579 : Nat := 406532561457276216933953

theorem tailTrace_1187579 : CollatzResearch.WordTrace tailWord_1187579 prefixEnd_1187579 406532561457276216933953 := by
  unfold tailWord_1187579
  simp only [CollatzResearch.WordTrace]
  refine ⟨43314564564611580190797791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28876376376407720127198527 43314564564611580190797791)
  ·
    refine ⟨64971846846917370286196687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43314564564611580190797791 64971846846917370286196687)
    ·
      refine ⟨97457770270376055429295031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64971846846917370286196687 97457770270376055429295031)
      ·
        refine ⟨146186655405564083143942547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97457770270376055429295031 146186655405564083143942547)
        ·
          refine ⟨219279983108346124715913821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146186655405564083143942547 219279983108346124715913821)
          ·
            refine ⟨82229993665629796768467683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219279983108346124715913821 82229993665629796768467683)
            ·
              refine ⟨123344990498444695152701525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82229993665629796768467683 123344990498444695152701525)
              ·
                refine ⟨1445449107403648771320721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 123344990498444695152701525 1445449107403648771320721)
                ·
                  refine ⟨1084086830552736578490541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445449107403648771320721 1084086830552736578490541)
                  ·
                    refine ⟨406532561457276216933953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084086830552736578490541 406532561457276216933953)
                    ·
                      rfl

theorem cell22_1187579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3].length) (baseStart_1187579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187579 prefixEnd_1187579 := by exact prefixLift 1187579
  have htrace : WordTrace (prefixWord ++ tailWord_1187579) baseStart_1187579 baseEnd_1187579 := by
    simpa [prefixWord, tailWord_1187579, baseEnd_1187579] using wordTrace_append hprefix tailTrace_1187579
  have hstable : (prefixWord ++ tailWord_1187579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187579).length < 2 ^ (prefixWord ++ tailWord_1187579).sum := by decide
  have hdescent : baseEnd_1187579 < baseStart_1187579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187592 : List Nat := [2, 1, 3, 2, 2, 1, 2, 9]
def baseStart_1187592 : Nat := 118140960795 + 1187592 * 2 ^ 59
def prefixEnd_1187592 : Nat := 4983230072969 + 3 ^ 40 * 1187592 * 2
def baseEnd_1187592 : Nat := 45170779069216501817657

theorem tailTrace_1187592 : CollatzResearch.WordTrace tailWord_1187592 prefixEnd_1187592 45170779069216501817657 := by
  unfold tailWord_1187592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21657519356782241705510515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28876692475709655607347353 21657519356782241705510515)
  ·
    refine ⟨32486279035173362558265773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21657519356782241705510515 32486279035173362558265773)
    ·
      refine ⟨12182354638190010959349665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32486279035173362558265773 12182354638190010959349665)
      ·
        refine ⟨9136765978642508219512249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12182354638190010959349665 9136765978642508219512249)
        ·
          refine ⟨6852574483981881164634187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9136765978642508219512249 6852574483981881164634187)
          ·
            refine ⟨10278861725972821746951281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852574483981881164634187 10278861725972821746951281)
            ·
              refine ⟨7709146294479616310213461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10278861725972821746951281 7709146294479616310213461)
              ·
                refine ⟨45170779069216501817657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7709146294479616310213461 45170779069216501817657)
                ·
                  rfl

theorem cell22_1187592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_1187592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187592 prefixEnd_1187592 := by exact prefixLift 1187592
  have htrace : WordTrace (prefixWord ++ tailWord_1187592) baseStart_1187592 baseEnd_1187592 := by
    simpa [prefixWord, tailWord_1187592, baseEnd_1187592] using wordTrace_append hprefix tailTrace_1187592
  have hstable : (prefixWord ++ tailWord_1187592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187592).length < 2 ^ (prefixWord ++ tailWord_1187592).sum := by decide
  have hdescent : baseEnd_1187592 < baseStart_1187592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187748 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1187748 : Nat := 118140960795 + 1187748 * 2 ^ 59
def prefixEnd_1187748 : Nat := 4983230072969 + 3 ^ 40 * 1187748 * 2
def baseEnd_1187748 : Nat := 406590413611016109458435

theorem tailTrace_1187748 : CollatzResearch.WordTrace tailWord_1187748 prefixEnd_1187748 406590413611016109458435 := by
  unfold tailWord_1187748
  simp only [CollatzResearch.WordTrace]
  refine ⟨21660364250499661026849949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28880485667332881369133265 21660364250499661026849949)
  ·
    refine ⟨8122636593937372885068731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21660364250499661026849949 8122636593937372885068731)
    ·
      refine ⟨12183954890906059327603097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122636593937372885068731 12183954890906059327603097)
      ·
        refine ⟨9137966168179544495702323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12183954890906059327603097 9137966168179544495702323)
        ·
          refine ⟨13706949252269316743553485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9137966168179544495702323 13706949252269316743553485)
          ·
            refine ⟨5140105969600993778832557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13706949252269316743553485 5140105969600993778832557)
            ·
              refine ⟨1927539738600372667062209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5140105969600993778832557 1927539738600372667062209)
              ·
                refine ⟨1445654803950279500296657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927539738600372667062209 1445654803950279500296657)
                ·
                  refine ⟨1084241102962709625222493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445654803950279500296657 1084241102962709625222493)
                  ·
                    refine ⟨406590413611016109458435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084241102962709625222493 406590413611016109458435)
                    ·
                      rfl

theorem cell22_1187748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1187748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1187748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1187748 prefixEnd_1187748 := by exact prefixLift 1187748
  have htrace : WordTrace (prefixWord ++ tailWord_1187748) baseStart_1187748 baseEnd_1187748 := by
    simpa [prefixWord, tailWord_1187748, baseEnd_1187748] using wordTrace_append hprefix tailTrace_1187748
  have hstable : (prefixWord ++ tailWord_1187748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187748).length < 2 ^ (prefixWord ++ tailWord_1187748).sum := by decide
  have hdescent : baseEnd_1187748 < baseStart_1187748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
