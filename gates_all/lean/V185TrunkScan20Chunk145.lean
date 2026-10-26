import V185TrunkScan20Chunk144

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_882777 : List Nat := [1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_882777 : Nat := 118140960795 + 882777 * 2 ^ 59
def prefixEnd_882777 : Nat := 4983230072969 + 3 ^ 40 * 882777 * 2
def baseEnd_882777 : Nat := 134307825699021589519315

theorem tailTrace_882777 : CollatzResearch.WordTrace tailWord_882777 prefixEnd_882777 134307825699021589519315 := by
  unfold tailWord_882777
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197522322857170153590585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21465014881904780102393723 32197522322857170153590585)
  ·
    refine ⟨24148141742142877615192939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32197522322857170153590585 24148141742142877615192939)
    ·
      refine ⟨36222212613214316422789409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24148141742142877615192939 36222212613214316422789409)
      ·
        refine ⟨27166659459910737317092057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36222212613214316422789409 27166659459910737317092057)
        ·
          refine ⟨20374994594933052987819043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27166659459910737317092057 20374994594933052987819043)
          ·
            refine ⟨30562491892399579481728565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374994594933052987819043 30562491892399579481728565)
            ·
              refine ⟨2865233614912460576412053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30562491892399579481728565 2865233614912460576412053)
              ·
                refine ⟨134307825699021589519315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2865233614912460576412053 134307825699021589519315)
                ·
                  rfl

theorem cell20_882777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_882777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882777 prefixEnd_882777 := by exact prefixLift 882777
  have htrace : WordTrace (prefixWord ++ tailWord_882777) baseStart_882777 baseEnd_882777 := by
    simpa [prefixWord, tailWord_882777, baseEnd_882777] using wordTrace_append hprefix tailTrace_882777
  have hstable : (prefixWord ++ tailWord_882777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882777).length < 2 ^ (prefixWord ++ tailWord_882777).sum := by decide
  have hdescent : baseEnd_882777 < baseStart_882777 := by decide
  rcases family_descends (prefixWord ++ tailWord_882777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882801 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_882801 : Nat := 118140960795 + 882801 * 2 ^ 59
def prefixEnd_882801 : Nat := 4983230072969 + 3 ^ 40 * 882801 * 2
def baseEnd_882801 : Nat := 402934431351027351757847

theorem tailTrace_882801 : CollatzResearch.WordTrace tailWord_882801 prefixEnd_882801 402934431351027351757847 := by
  unfold tailWord_882801
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198397674770222252464257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21465598449846814834976171 32198397674770222252464257)
  ·
    refine ⟨24148798256077666689348193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32198397674770222252464257 24148798256077666689348193)
    ·
      refine ⟨18111598692058250017011145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24148798256077666689348193 18111598692058250017011145)
      ·
        refine ⟨13583699019043687512758359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18111598692058250017011145 13583699019043687512758359)
        ·
          refine ⟨20375548528565531269137539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13583699019043687512758359 20375548528565531269137539)
          ·
            refine ⟨30563322792848296903706309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20375548528565531269137539 30563322792848296903706309)
            ·
              refine ⟨5730623023659055669444933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30563322792848296903706309 5730623023659055669444933)
              ·
                refine ⟨1074491816936072938020925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5730623023659055669444933 1074491816936072938020925)
                ·
                  refine ⟨402934431351027351757847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074491816936072938020925 402934431351027351757847)
                  ·
                    rfl

theorem cell20_882801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_882801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882801 prefixEnd_882801 := by exact prefixLift 882801
  have htrace : WordTrace (prefixWord ++ tailWord_882801) baseStart_882801 baseEnd_882801 := by
    simpa [prefixWord, tailWord_882801, baseEnd_882801] using wordTrace_append hprefix tailTrace_882801
  have hstable : (prefixWord ++ tailWord_882801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882801).length < 2 ^ (prefixWord ++ tailWord_882801).sum := by decide
  have hdescent : baseEnd_882801 < baseStart_882801 := by decide
  rcases family_descends (prefixWord ++ tailWord_882801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882855 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 2]
def baseStart_882855 : Nat := 118140960795 + 882855 * 2 ^ 59
def prefixEnd_882855 : Nat := 4983230072969 + 3 ^ 40 * 882855 * 2
def baseEnd_882855 : Nat := 402959078422443163957627

theorem tailTrace_882855 : CollatzResearch.WordTrace tailWord_882855 prefixEnd_882855 402959078422443163957627 := by
  unfold tailWord_882855
  simp only [CollatzResearch.WordTrace]
  refine ⟨32200367216574589474930019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21466911477716392983286679 32200367216574589474930019)
  ·
    refine ⟨48300550824861884212395029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32200367216574589474930019 48300550824861884212395029)
    ·
      refine ⟨2264088319915400822456017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48300550824861884212395029 2264088319915400822456017)
      ·
        refine ⟨1698066239936550616842013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2264088319915400822456017 1698066239936550616842013)
        ·
          refine ⟨636774839976206481315755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1698066239936550616842013 636774839976206481315755)
          ·
            refine ⟨955162259964309721973633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636774839976206481315755 955162259964309721973633)
            ·
              refine ⟨716371694973232291480225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955162259964309721973633 716371694973232291480225)
              ·
                refine ⟨537278771229924218610169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716371694973232291480225 537278771229924218610169)
                ·
                  refine ⟨402959078422443163957627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537278771229924218610169 402959078422443163957627)
                  ·
                    rfl

theorem cell20_882855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2].length) (baseStart_882855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882855 prefixEnd_882855 := by exact prefixLift 882855
  have htrace : WordTrace (prefixWord ++ tailWord_882855) baseStart_882855 baseEnd_882855 := by
    simpa [prefixWord, tailWord_882855, baseEnd_882855] using wordTrace_append hprefix tailTrace_882855
  have hstable : (prefixWord ++ tailWord_882855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882855).length < 2 ^ (prefixWord ++ tailWord_882855).sum := by decide
  have hdescent : baseEnd_882855 < baseStart_882855 := by decide
  rcases family_descends (prefixWord ++ tailWord_882855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882860 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_882860 : Nat := 118140960795 + 882860 * 2 ^ 59
def prefixEnd_882860 : Nat := 4983230072969 + 3 ^ 40 * 882860 * 2
def baseEnd_882860 : Nat := 402961360558685368790939

theorem tailTrace_882860 : CollatzResearch.WordTrace tailWord_882860 prefixEnd_882860 402961360558685368790939 := by
  unfold tailWord_882860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16100274790778237664431017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21467033054370983552574689 16100274790778237664431017)
  ·
    refine ⟨12075206093083678248323263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16100274790778237664431017 12075206093083678248323263)
    ·
      refine ⟨18112809139625517372484895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12075206093083678248323263 18112809139625517372484895)
      ·
        refine ⟨27169213709438276058727343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18112809139625517372484895 27169213709438276058727343)
        ·
          refine ⟨40753820564157414088091015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27169213709438276058727343 40753820564157414088091015)
          ·
            refine ⟨61130730846236121132136523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40753820564157414088091015 61130730846236121132136523)
            ·
              refine ⟨91696096269354181698204785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61130730846236121132136523 91696096269354181698204785)
              ·
                refine ⟨68772072202015636273653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91696096269354181698204785 68772072202015636273653589)
                ·
                  refine ⟨402961360558685368790939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68772072202015636273653589 402961360558685368790939)
                  ·
                    rfl

theorem cell20_882860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_882860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882860 prefixEnd_882860 := by exact prefixLift 882860
  have htrace : WordTrace (prefixWord ++ tailWord_882860) baseStart_882860 baseEnd_882860 := by
    simpa [prefixWord, tailWord_882860, baseEnd_882860] using wordTrace_append hprefix tailTrace_882860
  have hstable : (prefixWord ++ tailWord_882860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882860).length < 2 ^ (prefixWord ++ tailWord_882860).sum := by decide
  have hdescent : baseEnd_882860 < baseStart_882860 := by decide
  rcases family_descends (prefixWord ++ tailWord_882860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882914 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_882914 : Nat := 118140960795 + 882914 * 2 ^ 59
def prefixEnd_882914 : Nat := 4983230072969 + 3 ^ 40 * 882914 * 2
def baseEnd_882914 : Nat := 402986007630101180990719

theorem tailTrace_882914 : CollatzResearch.WordTrace tailWord_882914 prefixEnd_882914 402986007630101180990719 := by
  unfold tailWord_882914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050629780840210637831949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21468346082240561700885197 8050629780840210637831949)
  ·
    refine ⟨3018986167815078989186981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8050629780840210637831949 3018986167815078989186981)
    ·
      refine ⟨566059906465327310472559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3018986167815078989186981 566059906465327310472559)
      ·
        refine ⟨849089859697990965708839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566059906465327310472559 849089859697990965708839)
        ·
          refine ⟨1273634789546986448563259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849089859697990965708839 1273634789546986448563259)
          ·
            refine ⟨1910452184320479672844889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273634789546986448563259 1910452184320479672844889)
            ·
              refine ⟨1432839138240359754633667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910452184320479672844889 1432839138240359754633667)
              ·
                refine ⟨2149258707360539631950501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432839138240359754633667 2149258707360539631950501)
                ·
                  refine ⟨402986007630101180990719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149258707360539631950501 402986007630101180990719)
                  ·
                    rfl

theorem cell20_882914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_882914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882914 prefixEnd_882914 := by exact prefixLift 882914
  have htrace : WordTrace (prefixWord ++ tailWord_882914) baseStart_882914 baseEnd_882914 := by
    simpa [prefixWord, tailWord_882914, baseEnd_882914] using wordTrace_append hprefix tailTrace_882914
  have hstable : (prefixWord ++ tailWord_882914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882914).length < 2 ^ (prefixWord ++ tailWord_882914).sum := by decide
  have hdescent : baseEnd_882914 < baseStart_882914 := by decide
  rcases family_descends (prefixWord ++ tailWord_882914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882967 : List Nat := [1, 1, 3, 4, 1, 2, 8]
def baseStart_882967 : Nat := 118140960795 + 882967 * 2 ^ 59
def prefixEnd_882967 : Nat := 4983230072969 + 3 ^ 40 * 882967 * 2
def baseEnd_882967 : Nat := 44778910919363172469315

theorem tailTrace_882967 : CollatzResearch.WordTrace tailWord_882967 prefixEnd_882967 44778910919363172469315 := by
  unfold tailWord_882967
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204452192168832603007155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21469634794779221735338103 32204452192168832603007155)
  ·
    refine ⟨48306678288253248904510733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32204452192168832603007155 48306678288253248904510733)
    ·
      refine ⟨18115004358094968339191525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48306678288253248904510733 18115004358094968339191525)
      ·
        refine ⟨3396563317142806563598411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18115004358094968339191525 3396563317142806563598411)
        ·
          refine ⟨5094844975714209845397617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396563317142806563598411 5094844975714209845397617)
          ·
            refine ⟨3821133731785657384048213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5094844975714209845397617 3821133731785657384048213)
            ·
              refine ⟨44778910919363172469315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3821133731785657384048213 44778910919363172469315)
              ·
                rfl

theorem cell20_882967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_882967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882967 prefixEnd_882967 := by exact prefixLift 882967
  have htrace : WordTrace (prefixWord ++ tailWord_882967) baseStart_882967 baseEnd_882967 := by
    simpa [prefixWord, tailWord_882967, baseEnd_882967] using wordTrace_append hprefix tailTrace_882967
  have hstable : (prefixWord ++ tailWord_882967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882967).length < 2 ^ (prefixWord ++ tailWord_882967).sum := by decide
  have hdescent : baseEnd_882967 < baseStart_882967 := by decide
  rcases family_descends (prefixWord ++ tailWord_882967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882973 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 4]
def baseStart_882973 : Nat := 118140960795 + 882973 * 2 ^ 59
def prefixEnd_882973 : Nat := 4983230072969 + 3 ^ 40 * 882973 * 2
def baseEnd_882973 : Nat := 403012936837759198023811

theorem tailTrace_882973 : CollatzResearch.WordTrace tailWord_882973 prefixEnd_882973 403012936837759198023811 := by
  unfold tailWord_882973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204671030147095627725573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21469780686764730418483715 32204671030147095627725573)
  ·
    refine ⟨6038375818152580430198545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32204671030147095627725573 6038375818152580430198545)
    ·
      refine ⟨4528781863614435322648909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6038375818152580430198545 4528781863614435322648909)
      ·
        refine ⟨1698293198855413245993341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4528781863614435322648909 1698293198855413245993341)
        ·
          refine ⟨636859949570779967247503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1698293198855413245993341 636859949570779967247503)
          ·
            refine ⟨955289924356169950871255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636859949570779967247503 955289924356169950871255)
            ·
              refine ⟨1432934886534254926306883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955289924356169950871255 1432934886534254926306883)
              ·
                refine ⟨2149402329801382389460325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432934886534254926306883 2149402329801382389460325)
                ·
                  refine ⟨403012936837759198023811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149402329801382389460325 403012936837759198023811)
                  ·
                    rfl

theorem cell20_882973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_882973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882973 prefixEnd_882973 := by exact prefixLift 882973
  have htrace : WordTrace (prefixWord ++ tailWord_882973) baseStart_882973 baseEnd_882973 := by
    simpa [prefixWord, tailWord_882973, baseEnd_882973] using wordTrace_append hprefix tailTrace_882973
  have hstable : (prefixWord ++ tailWord_882973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882973).length < 2 ^ (prefixWord ++ tailWord_882973).sum := by decide
  have hdescent : baseEnd_882973 < baseStart_882973 := by decide
  rcases family_descends (prefixWord ++ tailWord_882973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882977 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 2]
def baseStart_882977 : Nat := 118140960795 + 882977 * 2 ^ 59
def prefixEnd_882977 : Nat := 4983230072969 + 3 ^ 40 * 882977 * 2
def baseEnd_882977 : Nat := 403014762546752961890461

theorem tailTrace_882977 : CollatzResearch.WordTrace tailWord_882977 prefixEnd_882977 403014762546752961890461 := by
  unfold tailWord_882977
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204816922132604310871185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21469877948088402873914123 32204816922132604310871185)
  ·
    refine ⟨24153612691599453233153389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32204816922132604310871185 24153612691599453233153389)
    ·
      refine ⟨9057604759349794962432521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24153612691599453233153389 9057604759349794962432521)
      ·
        refine ⟨6793203569512346221824391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9057604759349794962432521 6793203569512346221824391)
        ·
          refine ⟨10189805354268519332736587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793203569512346221824391 10189805354268519332736587)
          ·
            refine ⟨15284708031402778999104881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189805354268519332736587 15284708031402778999104881)
            ·
              refine ⟨11463531023552084249328661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15284708031402778999104881 11463531023552084249328661)
              ·
                refine ⟨537353016729003949187281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11463531023552084249328661 537353016729003949187281)
                ·
                  refine ⟨403014762546752961890461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537353016729003949187281 403014762546752961890461)
                  ·
                    rfl

theorem cell20_882977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_882977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882977 prefixEnd_882977 := by exact prefixLift 882977
  have htrace : WordTrace (prefixWord ++ tailWord_882977) baseStart_882977 baseEnd_882977 := by
    simpa [prefixWord, tailWord_882977, baseEnd_882977] using wordTrace_append hprefix tailTrace_882977
  have hstable : (prefixWord ++ tailWord_882977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882977).length < 2 ^ (prefixWord ++ tailWord_882977).sum := by decide
  have hdescent : baseEnd_882977 < baseStart_882977 := by decide
  rcases family_descends (prefixWord ++ tailWord_882977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883015 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 2]
def baseStart_883015 : Nat := 118140960795 + 883015 * 2 ^ 59
def prefixEnd_883015 : Nat := 4983230072969 + 3 ^ 40 * 883015 * 2
def baseEnd_883015 : Nat := 403032106782193718623639

theorem tailTrace_883015 : CollatzResearch.WordTrace tailWord_883015 prefixEnd_883015 403032106782193718623639 := by
  unfold tailWord_883015
  simp only [CollatzResearch.WordTrace]
  refine ⟨32206202895994936800754499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21470801930663291200502999 32206202895994936800754499)
  ·
    refine ⟨48309304343992405201131749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32206202895994936800754499 48309304343992405201131749)
    ·
      refine ⟨9057994564498575975212203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48309304343992405201131749 9057994564498575975212203)
      ·
        refine ⟨13586991846747863962818305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9057994564498575975212203 13586991846747863962818305)
        ·
          refine ⟨10190243885060897972113729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13586991846747863962818305 10190243885060897972113729)
          ·
            refine ⟨7642682913795673479085297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10190243885060897972113729 7642682913795673479085297)
            ·
              refine ⟨5732012185346755109313973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7642682913795673479085297 5732012185346755109313973)
              ·
                refine ⟨537376142376258291498185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5732012185346755109313973 537376142376258291498185)
                ·
                  refine ⟨403032106782193718623639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537376142376258291498185 403032106782193718623639)
                  ·
                    rfl

theorem cell20_883015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2].length) (baseStart_883015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883015 prefixEnd_883015 := by exact prefixLift 883015
  have htrace : WordTrace (prefixWord ++ tailWord_883015) baseStart_883015 baseEnd_883015 := by
    simpa [prefixWord, tailWord_883015, baseEnd_883015] using wordTrace_append hprefix tailTrace_883015
  have hstable : (prefixWord ++ tailWord_883015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883015).length < 2 ^ (prefixWord ++ tailWord_883015).sum := by decide
  have hdescent : baseEnd_883015 < baseStart_883015 := by decide
  rcases family_descends (prefixWord ++ tailWord_883015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883019 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_883019 : Nat := 118140960795 + 883019 * 2 ^ 59
def prefixEnd_883019 : Nat := 4983230072969 + 3 ^ 40 * 883019 * 2
def baseEnd_883019 : Nat := 403033932491187482490289

theorem tailTrace_883019 : CollatzResearch.WordTrace tailWord_883019 prefixEnd_883019 403033932491187482490289 := by
  unfold tailWord_883019
  simp only [CollatzResearch.WordTrace]
  refine ⟨32206348787980445483900111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21470899191986963655933407 32206348787980445483900111)
  ·
    refine ⟨48309523181970668225850167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32206348787980445483900111 48309523181970668225850167)
    ·
      refine ⟨72464284772956002338775251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48309523181970668225850167 72464284772956002338775251)
      ·
        refine ⟨108696427159434003508162877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72464284772956002338775251 108696427159434003508162877)
        ·
          refine ⟨40761160184787751315561079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108696427159434003508162877 40761160184787751315561079)
          ·
            refine ⟨61141740277181626973341619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40761160184787751315561079 61141740277181626973341619)
            ·
              refine ⟨91712610415772440460012429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61141740277181626973341619 91712610415772440460012429)
              ·
                refine ⟨34392228905914665172504661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91712610415772440460012429 34392228905914665172504661)
                ·
                  refine ⟨403033932491187482490289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34392228905914665172504661 403033932491187482490289)
                  ·
                    rfl

theorem cell20_883019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_883019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883019 prefixEnd_883019 := by exact prefixLift 883019
  have htrace : WordTrace (prefixWord ++ tailWord_883019) baseStart_883019 baseEnd_883019 := by
    simpa [prefixWord, tailWord_883019, baseEnd_883019] using wordTrace_append hprefix tailTrace_883019
  have hstable : (prefixWord ++ tailWord_883019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883019).length < 2 ^ (prefixWord ++ tailWord_883019).sum := by decide
  have hdescent : baseEnd_883019 < baseStart_883019 := by decide
  rcases family_descends (prefixWord ++ tailWord_883019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883081 : List Nat := [1, 2, 1, 1, 6, 2, 7]
def baseStart_883081 : Nat := 118140960795 + 883081 * 2 ^ 59
def prefixEnd_883081 : Nat := 4983230072969 + 3 ^ 40 * 883081 * 2
def baseEnd_883081 : Nat := 44784692331176758047041

theorem tailTrace_883081 : CollatzResearch.WordTrace tailWord_883081 prefixEnd_883081 44784692331176758047041 := by
  unfold tailWord_883081
  simp only [CollatzResearch.WordTrace]
  refine ⟨32208610113755830072657097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21472406742503886715104731 32208610113755830072657097)
  ·
    refine ⟨24156457585316872554492823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32208610113755830072657097 24156457585316872554492823)
    ·
      refine ⟨36234686377975308831739235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24156457585316872554492823 36234686377975308831739235)
      ·
        refine ⟨54352029566962963247608853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36234686377975308831739235 54352029566962963247608853)
        ·
          refine ⟨2547751385951388902231665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54352029566962963247608853 2547751385951388902231665)
          ·
            refine ⟨1910813539463541676673749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547751385951388902231665 1910813539463541676673749)
            ·
              refine ⟨44784692331176758047041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1910813539463541676673749 44784692331176758047041)
              ·
                rfl

theorem cell20_883081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_883081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883081 prefixEnd_883081 := by exact prefixLift 883081
  have htrace : WordTrace (prefixWord ++ tailWord_883081) baseStart_883081 baseEnd_883081 := by
    simpa [prefixWord, tailWord_883081, baseEnd_883081] using wordTrace_append hprefix tailTrace_883081
  have hstable : (prefixWord ++ tailWord_883081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883081).length < 2 ^ (prefixWord ++ tailWord_883081).sum := by decide
  have hdescent : baseEnd_883081 < baseStart_883081 := by decide
  rcases family_descends (prefixWord ++ tailWord_883081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883084 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_883084 : Nat := 118140960795 + 883084 * 2 ^ 59
def prefixEnd_883084 : Nat := 4983230072969 + 3 ^ 40 * 883084 * 2
def baseEnd_883084 : Nat := 403063600262336145323357

theorem tailTrace_883084 : CollatzResearch.WordTrace tailWord_883084 prefixEnd_883084 403063600262336145323357 := by
  unfold tailWord_883084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104359766372480792508153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21472479688496641056677537 16104359766372480792508153)
  ·
    refine ⟨12078269824779360594381115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16104359766372480792508153 12078269824779360594381115)
    ·
      refine ⟨18117404737169040891571673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12078269824779360594381115 18117404737169040891571673)
      ·
        refine ⟨13588053552876780668678755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18117404737169040891571673 13588053552876780668678755)
        ·
          refine ⟨20382080329315171003018133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13588053552876780668678755 20382080329315171003018133)
          ·
            refine ⟨955410015436648640766475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20382080329315171003018133 955410015436648640766475)
            ·
              refine ⟨1433115023154972961149713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955410015436648640766475 1433115023154972961149713)
              ·
                refine ⟨1074836267366229720862285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433115023154972961149713 1074836267366229720862285)
                ·
                  refine ⟨403063600262336145323357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074836267366229720862285 403063600262336145323357)
                  ·
                    rfl

theorem cell20_883084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_883084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883084 prefixEnd_883084 := by exact prefixLift 883084
  have htrace : WordTrace (prefixWord ++ tailWord_883084) baseStart_883084 baseEnd_883084 := by
    simpa [prefixWord, tailWord_883084, baseEnd_883084] using wordTrace_append hprefix tailTrace_883084
  have hstable : (prefixWord ++ tailWord_883084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883084).length < 2 ^ (prefixWord ++ tailWord_883084).sum := by decide
  have hdescent : baseEnd_883084 < baseStart_883084 := by decide
  rcases family_descends (prefixWord ++ tailWord_883084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883101 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 3]
def baseStart_883101 : Nat := 118140960795 + 883101 * 2 ^ 59
def prefixEnd_883101 : Nat := 4983230072969 + 3 ^ 40 * 883101 * 2
def baseEnd_883101 : Nat := 403071359525559641756621

theorem tailTrace_883101 : CollatzResearch.WordTrace tailWord_883101 prefixEnd_883101 403071359525559641756621 := by
  unfold tailWord_883101
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209339573683373488385157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21472893049122248992256771 32209339573683373488385157)
  ·
    refine ⟨6039251170065632529072217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32209339573683373488385157 6039251170065632529072217)
    ·
      refine ⟨4529438377549224396804163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6039251170065632529072217 4529438377549224396804163)
      ·
        refine ⟨6794157566323836595206245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529438377549224396804163 6794157566323836595206245)
        ·
          refine ⟨1273904543685719361601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6794157566323836595206245 1273904543685719361601171)
          ·
            refine ⟨1910856815528579042401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273904543685719361601171 1910856815528579042401757)
            ·
              refine ⟨716571305823217140900659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1910856815528579042401757 716571305823217140900659)
              ·
                refine ⟨1074856958734825711350989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716571305823217140900659 1074856958734825711350989)
                ·
                  refine ⟨403071359525559641756621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074856958734825711350989 403071359525559641756621)
                  ·
                    rfl

theorem cell20_883101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_883101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883101 prefixEnd_883101 := by exact prefixLift 883101
  have htrace : WordTrace (prefixWord ++ tailWord_883101) baseStart_883101 baseEnd_883101 := by
    simpa [prefixWord, tailWord_883101, baseEnd_883101] using wordTrace_append hprefix tailTrace_883101
  have hstable : (prefixWord ++ tailWord_883101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883101).length < 2 ^ (prefixWord ++ tailWord_883101).sum := by decide
  have hdescent : baseEnd_883101 < baseStart_883101 := by decide
  rcases family_descends (prefixWord ++ tailWord_883101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883125 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 2]
def baseStart_883125 : Nat := 118140960795 + 883125 * 2 ^ 59
def prefixEnd_883125 : Nat := 4983230072969 + 3 ^ 40 * 883125 * 2
def baseEnd_883125 : Nat := 403082313779522224956523

theorem tailTrace_883125 : CollatzResearch.WordTrace tailWord_883125 prefixEnd_883125 403082313779522224956523 := by
  unfold tailWord_883125
  simp only [CollatzResearch.WordTrace]
  refine ⟨32210214925596425587258829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21473476617064283724839219 32210214925596425587258829)
  ·
    refine ⟨12078830597098659595222061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32210214925596425587258829 12078830597098659595222061)
    ·
      refine ⟨4529561473911997348208273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12078830597098659595222061 4529561473911997348208273)
      ·
        refine ⟨3397171105433998011156205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4529561473911997348208273 3397171105433998011156205)
        ·
          refine ⟨1273939164537749254183577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3397171105433998011156205 1273939164537749254183577)
          ·
            refine ⟨955454373403311940637683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273939164537749254183577 955454373403311940637683)
            ·
              refine ⟨1433181560104967910956525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955454373403311940637683 1433181560104967910956525)
              ·
                refine ⟨537443085039362966608697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1433181560104967910956525 537443085039362966608697)
                ·
                  refine ⟨403082313779522224956523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537443085039362966608697 403082313779522224956523)
                  ·
                    rfl

theorem cell20_883125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_883125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883125 prefixEnd_883125 := by exact prefixLift 883125
  have htrace : WordTrace (prefixWord ++ tailWord_883125) baseStart_883125 baseEnd_883125 := by
    simpa [prefixWord, tailWord_883125, baseEnd_883125] using wordTrace_append hprefix tailTrace_883125
  have hstable : (prefixWord ++ tailWord_883125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883125).length < 2 ^ (prefixWord ++ tailWord_883125).sum := by decide
  have hdescent : baseEnd_883125 < baseStart_883125 := by decide
  rcases family_descends (prefixWord ++ tailWord_883125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883146 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_883146 : Nat := 118140960795 + 883146 * 2 ^ 59
def prefixEnd_883146 : Nat := 4983230072969 + 3 ^ 40 * 883146 * 2
def baseEnd_883146 : Nat := 403091898751739485256437

theorem tailTrace_883146 : CollatzResearch.WordTrace tailWord_883146 prefixEnd_883146 403091898751739485256437 := by
  unfold tailWord_883146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052745214630086543443323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21473987239013564115848861 8052745214630086543443323)
  ·
    refine ⟨12079117821945129815164985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8052745214630086543443323 12079117821945129815164985)
    ·
      refine ⟨9059338366458847361373739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12079117821945129815164985 9059338366458847361373739)
      ·
        refine ⟨13589007549688271042060609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059338366458847361373739 13589007549688271042060609)
        ·
          refine ⟨10191755662266203281545457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13589007549688271042060609 10191755662266203281545457)
          ·
            refine ⟨7643816746699652461159093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10191755662266203281545457 7643816746699652461159093)
            ·
              refine ⟨716607820003092418233665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7643816746699652461159093 716607820003092418233665)
              ·
                refine ⟨537455865002319313675249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716607820003092418233665 537455865002319313675249)
                ·
                  refine ⟨403091898751739485256437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537455865002319313675249 403091898751739485256437)
                  ·
                    rfl

theorem cell20_883146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_883146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883146 prefixEnd_883146 := by exact prefixLift 883146
  have htrace : WordTrace (prefixWord ++ tailWord_883146) baseStart_883146 baseEnd_883146 := by
    simpa [prefixWord, tailWord_883146, baseEnd_883146] using wordTrace_append hprefix tailTrace_883146
  have hstable : (prefixWord ++ tailWord_883146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883146).length < 2 ^ (prefixWord ++ tailWord_883146).sum := by decide
  have hdescent : baseEnd_883146 < baseStart_883146 := by decide
  rcases family_descends (prefixWord ++ tailWord_883146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883157 : List Nat := [1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_883157 : Nat := 118140960795 + 883157 * 2 ^ 59
def prefixEnd_883157 : Nat := 4983230072969 + 3 ^ 40 * 883157 * 2
def baseEnd_883157 : Nat := 134365639817157445296575

theorem tailTrace_883157 : CollatzResearch.WordTrace tailWord_883157 prefixEnd_883157 134365639817157445296575 := by
  unfold tailWord_883157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32211382061480495052423725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21474254707653663368282483 32211382061480495052423725)
  ·
    refine ⟨12079268273055185644658897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32211382061480495052423725 12079268273055185644658897)
    ·
      refine ⟨9059451204791389233494173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12079268273055185644658897 9059451204791389233494173)
      ·
        refine ⟨3397294201796770962560315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9059451204791389233494173 3397294201796770962560315)
        ·
          refine ⟨5095941302695156443840473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397294201796770962560315 5095941302695156443840473)
          ·
            refine ⟨3821955977021367332880355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095941302695156443840473 3821955977021367332880355)
            ·
              refine ⟨5732933965532050999320533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821955977021367332880355 5732933965532050999320533)
              ·
                refine ⟨134365639817157445296575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5732933965532050999320533 134365639817157445296575)
                ·
                  rfl

theorem cell20_883157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_883157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883157 prefixEnd_883157 := by exact prefixLift 883157
  have htrace : WordTrace (prefixWord ++ tailWord_883157) baseStart_883157 baseEnd_883157 := by
    simpa [prefixWord, tailWord_883157, baseEnd_883157] using wordTrace_append hprefix tailTrace_883157
  have hstable : (prefixWord ++ tailWord_883157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883157).length < 2 ^ (prefixWord ++ tailWord_883157).sum := by decide
  have hdescent : baseEnd_883157 < baseStart_883157 := by decide
  rcases family_descends (prefixWord ++ tailWord_883157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883201 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 2]
def baseStart_883201 : Nat := 118140960795 + 883201 * 2 ^ 59
def prefixEnd_883201 : Nat := 4983230072969 + 3 ^ 40 * 883201 * 2
def baseEnd_883201 : Nat := 403117002250403738422879

theorem tailTrace_883201 : CollatzResearch.WordTrace tailWord_883201 prefixEnd_883201 403117002250403738422879 := by
  unfold tailWord_883201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32212986873321090567025457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21475324582214060378016971 32212986873321090567025457)
  ·
    refine ⟨24159740154990817925269093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32212986873321090567025457 24159740154990817925269093)
    ·
      refine ⟨4529951279060778360987955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24159740154990817925269093 4529951279060778360987955)
      ·
        refine ⟨6794926918591167541481933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529951279060778360987955 6794926918591167541481933)
        ·
          refine ⟨2548097594471687828055725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6794926918591167541481933 2548097594471687828055725)
          ·
            refine ⟨955536597926882935520897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2548097594471687828055725 955536597926882935520897)
            ·
              refine ⟨716652448445162201640673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955536597926882935520897 716652448445162201640673)
              ·
                refine ⟨537489336333871651230505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716652448445162201640673 537489336333871651230505)
                ·
                  refine ⟨403117002250403738422879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537489336333871651230505 403117002250403738422879)
                  ·
                    rfl

theorem cell20_883201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_883201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883201 prefixEnd_883201 := by exact prefixLift 883201
  have htrace : WordTrace (prefixWord ++ tailWord_883201) baseStart_883201 baseEnd_883201 := by
    simpa [prefixWord, tailWord_883201, baseEnd_883201] using wordTrace_append hprefix tailTrace_883201
  have hstable : (prefixWord ++ tailWord_883201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883201).length < 2 ^ (prefixWord ++ tailWord_883201).sum := by decide
  have hdescent : baseEnd_883201 < baseStart_883201 := by decide
  rcases family_descends (prefixWord ++ tailWord_883201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883212 : List Nat := [2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_883212 : Nat := 118140960795 + 883212 * 2 ^ 59
def prefixEnd_883212 : Nat := 4983230072969 + 3 ^ 40 * 883212 * 2
def baseEnd_883212 : Nat := 134374007650045529685389

theorem tailTrace_883212 : CollatzResearch.WordTrace tailWord_883212 prefixEnd_883212 134374007650045529685389 := by
  unfold tailWord_883212
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106694038140619722837945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21475592050854159630450593 16106694038140619722837945)
  ·
    refine ⟨12080020528605464792128459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16106694038140619722837945 12080020528605464792128459)
    ·
      refine ⟨18120030792908197188192689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080020528605464792128459 18120030792908197188192689)
      ·
        refine ⟨13590023094681147891144517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18120030792908197188192689 13590023094681147891144517)
        ·
          refine ⟨2548129330252715229589597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13590023094681147891144517 2548129330252715229589597)
          ·
            refine ⟨955548498844768211096099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2548129330252715229589597 955548498844768211096099)
            ·
              refine ⟨1433322748267152316644149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955548498844768211096099 1433322748267152316644149)
              ·
                refine ⟨134374007650045529685389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1433322748267152316644149 134374007650045529685389)
                ·
                  rfl

theorem cell20_883212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_883212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883212 prefixEnd_883212 := by exact prefixLift 883212
  have htrace : WordTrace (prefixWord ++ tailWord_883212) baseStart_883212 baseEnd_883212 := by
    simpa [prefixWord, tailWord_883212, baseEnd_883212] using wordTrace_append hprefix tailTrace_883212
  have hstable : (prefixWord ++ tailWord_883212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883212).length < 2 ^ (prefixWord ++ tailWord_883212).sum := by decide
  have hdescent : baseEnd_883212 < baseStart_883212 := by decide
  rcases family_descends (prefixWord ++ tailWord_883212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883270 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_883270 : Nat := 118140960795 + 883270 * 2 ^ 59
def prefixEnd_883270 : Nat := 4983230072969 + 3 ^ 40 * 883270 * 2
def baseEnd_883270 : Nat := 403148495730546165122597

theorem tailTrace_883270 : CollatzResearch.WordTrace tailWord_883270 prefixEnd_883270 403148495730546165122597 := by
  unfold tailWord_883270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006734484689722354727727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21477002340047410234191509 1006734484689722354727727)
  ·
    refine ⟨1510101727034583532091591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1006734484689722354727727 1510101727034583532091591)
    ·
      refine ⟨2265152590551875298137387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510101727034583532091591 2265152590551875298137387)
      ·
        refine ⟨3397728885827812947206081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265152590551875298137387 3397728885827812947206081)
        ·
          refine ⟨2548296664370859710404561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397728885827812947206081 2548296664370859710404561)
          ·
            refine ⟨1911222498278144782803421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548296664370859710404561 1911222498278144782803421)
            ·
              refine ⟨716708436854304293551283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911222498278144782803421 716708436854304293551283)
              ·
                refine ⟨1075062655281456440326925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716708436854304293551283 1075062655281456440326925)
                ·
                  refine ⟨403148495730546165122597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075062655281456440326925 403148495730546165122597)
                  ·
                    rfl

theorem cell20_883270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_883270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883270 prefixEnd_883270 := by exact prefixLift 883270
  have htrace : WordTrace (prefixWord ++ tailWord_883270) baseStart_883270 baseEnd_883270 := by
    simpa [prefixWord, tailWord_883270, baseEnd_883270] using wordTrace_append hprefix tailTrace_883270
  have hstable : (prefixWord ++ tailWord_883270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883270).length < 2 ^ (prefixWord ++ tailWord_883270).sum := by decide
  have hdescent : baseEnd_883270 < baseStart_883270 := by decide
  rcases family_descends (prefixWord ++ tailWord_883270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883274 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_883274 : Nat := 118140960795 + 883274 * 2 ^ 59
def prefixEnd_883274 : Nat := 4983230072969 + 3 ^ 40 * 883274 * 2
def baseEnd_883274 : Nat := 403150321439539928989247

theorem tailTrace_883274 : CollatzResearch.WordTrace tailWord_883274 prefixEnd_883274 403150321439539928989247 := by
  unfold tailWord_883274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053912350514156008608219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21477099601371082689621917 8053912350514156008608219)
  ·
    refine ⟨12080868525771234012912329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8053912350514156008608219 12080868525771234012912329)
    ·
      refine ⟨9060651394328425509684247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12080868525771234012912329 9060651394328425509684247)
      ·
        refine ⟨13590977091492638264526371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060651394328425509684247 13590977091492638264526371)
        ·
          refine ⟨20386465637238957396789557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13590977091492638264526371 20386465637238957396789557)
          ·
            refine ⟨1911231153491152255949021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20386465637238957396789557 1911231153491152255949021)
            ·
              refine ⟨716711682559182095980883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911231153491152255949021 716711682559182095980883)
              ·
                refine ⟨1075067523838773143971325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716711682559182095980883 1075067523838773143971325)
                ·
                  refine ⟨403150321439539928989247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075067523838773143971325 403150321439539928989247)
                  ·
                    rfl

theorem cell20_883274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_883274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883274 prefixEnd_883274 := by exact prefixLift 883274
  have htrace : WordTrace (prefixWord ++ tailWord_883274) baseStart_883274 baseEnd_883274 := by
    simpa [prefixWord, tailWord_883274, baseEnd_883274] using wordTrace_append hprefix tailTrace_883274
  have hstable : (prefixWord ++ tailWord_883274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883274).length < 2 ^ (prefixWord ++ tailWord_883274).sum := by decide
  have hdescent : baseEnd_883274 < baseStart_883274 := by decide
  rcases family_descends (prefixWord ++ tailWord_883274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883309 : List Nat := [1, 5, 1, 1, 3, 1, 8]
def baseStart_883309 : Nat := 118140960795 + 883309 * 2 ^ 59
def prefixEnd_883309 : Nat := 4983230072969 + 3 ^ 40 * 883309 * 2
def baseEnd_883309 : Nat := 44796255154803929202493

theorem tailTrace_883309 : CollatzResearch.WordTrace tailWord_883309 prefixEnd_883309 44796255154803929202493 := by
  unfold tailWord_883309
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216925956929825011956981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21477950637953216674637987 32216925956929825011956981)
  ·
    refine ⟨3020336808462171094870967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32216925956929825011956981 3020336808462171094870967)
    ·
      refine ⟨4530505212693256642306451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020336808462171094870967 4530505212693256642306451)
      ·
        refine ⟨6795757819039884963459677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530505212693256642306451 6795757819039884963459677)
        ·
          refine ⟨2548409182139956861297379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6795757819039884963459677 2548409182139956861297379)
          ·
            refine ⟨3822613773209935291946069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548409182139956861297379 3822613773209935291946069)
            ·
              refine ⟨44796255154803929202493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3822613773209935291946069 44796255154803929202493)
              ·
                rfl

theorem cell20_883309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_883309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883309 prefixEnd_883309 := by exact prefixLift 883309
  have htrace : WordTrace (prefixWord ++ tailWord_883309) baseStart_883309 baseEnd_883309 := by
    simpa [prefixWord, tailWord_883309, baseEnd_883309] using wordTrace_append hprefix tailTrace_883309
  have hstable : (prefixWord ++ tailWord_883309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883309).length < 2 ^ (prefixWord ++ tailWord_883309).sum := by decide
  have hdescent : baseEnd_883309 < baseStart_883309 := by decide
  rcases family_descends (prefixWord ++ tailWord_883309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883323 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_883323 : Nat := 118140960795 + 883323 * 2 ^ 59
def prefixEnd_883323 : Nat := 4983230072969 + 3 ^ 40 * 883323 * 2
def baseEnd_883323 : Nat := 403172686374713536355713

theorem tailTrace_883323 : CollatzResearch.WordTrace tailWord_883323 prefixEnd_883323 403172686374713536355713 := by
  unfold tailWord_883323
  simp only [CollatzResearch.WordTrace]
  refine ⟨32217436578879105402966623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21478291052586070268644415 32217436578879105402966623)
  ·
    refine ⟨48326154868318658104449935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32217436578879105402966623 48326154868318658104449935)
    ·
      refine ⟨72489232302477987156674903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48326154868318658104449935 72489232302477987156674903)
      ·
        refine ⟨108733848453716980735012355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72489232302477987156674903 108733848453716980735012355)
        ·
          refine ⟨163100772680575471102518533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108733848453716980735012355 163100772680575471102518533)
          ·
            refine ⟨30581394877607900831722225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163100772680575471102518533 30581394877607900831722225)
            ·
              refine ⟨22936046158205925623791669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30581394877607900831722225 22936046158205925623791669)
              ·
                refine ⟨2150254327331805527230469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22936046158205925623791669 2150254327331805527230469)
                ·
                  refine ⟨403172686374713536355713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150254327331805527230469 403172686374713536355713)
                  ·
                    rfl

theorem cell20_883323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_883323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883323 prefixEnd_883323 := by exact prefixLift 883323
  have htrace : WordTrace (prefixWord ++ tailWord_883323) baseStart_883323 baseEnd_883323 := by
    simpa [prefixWord, tailWord_883323, baseEnd_883323] using wordTrace_append hprefix tailTrace_883323
  have hstable : (prefixWord ++ tailWord_883323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883323).length < 2 ^ (prefixWord ++ tailWord_883323).sum := by decide
  have hdescent : baseEnd_883323 < baseStart_883323 := by decide
  rcases family_descends (prefixWord ++ tailWord_883323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883333 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_883333 : Nat := 118140960795 + 883333 * 2 ^ 59
def prefixEnd_883333 : Nat := 4983230072969 + 3 ^ 40 * 883333 * 2
def baseEnd_883333 : Nat := 403177250647197946022339

theorem tailTrace_883333 : CollatzResearch.WordTrace tailWord_883333 prefixEnd_883333 403177250647197946022339 := by
  unfold tailWord_883333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32217801308842877110830653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21478534205895251407220435 32217801308842877110830653)
  ·
    refine ⟨12081675490816078916561495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32217801308842877110830653 12081675490816078916561495)
    ·
      refine ⟨18122513236224118374842243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12081675490816078916561495 18122513236224118374842243)
      ·
        refine ⟨27183769854336177562263365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18122513236224118374842243 27183769854336177562263365)
        ·
          refine ⟨5096956847688033292924381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27183769854336177562263365 5096956847688033292924381)
          ·
            refine ⟨1911358817883012484846643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5096956847688033292924381 1911358817883012484846643)
            ·
              refine ⟨2867038226824518727269965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911358817883012484846643 2867038226824518727269965)
              ·
                refine ⟨1075139335059194522726237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867038226824518727269965 1075139335059194522726237)
                ·
                  refine ⟨403177250647197946022339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075139335059194522726237 403177250647197946022339)
                  ·
                    rfl

theorem cell20_883333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_883333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883333 prefixEnd_883333 := by exact prefixLift 883333
  have htrace : WordTrace (prefixWord ++ tailWord_883333) baseStart_883333 baseEnd_883333 := by
    simpa [prefixWord, tailWord_883333, baseEnd_883333] using wordTrace_append hprefix tailTrace_883333
  have hstable : (prefixWord ++ tailWord_883333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883333).length < 2 ^ (prefixWord ++ tailWord_883333).sum := by decide
  have hdescent : baseEnd_883333 < baseStart_883333 := by decide
  rcases family_descends (prefixWord ++ tailWord_883333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883367 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_883367 : Nat := 118140960795 + 883367 * 2 ^ 59
def prefixEnd_883367 : Nat := 4983230072969 + 3 ^ 40 * 883367 * 2
def baseEnd_883367 : Nat := 403192769173644938888867

theorem tailTrace_883367 : CollatzResearch.WordTrace tailWord_883367 prefixEnd_883367 403192769173644938888867 := by
  unfold tailWord_883367
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219041390719700917568355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21479360927146467278378903 32219041390719700917568355)
  ·
    refine ⟨48328562086079551376352533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32219041390719700917568355 48328562086079551376352533)
    ·
      refine ⟨2265401347784978970766525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48328562086079551376352533 2265401347784978970766525)
      ·
        refine ⟨849525505419367114037447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2265401347784978970766525 849525505419367114037447)
        ·
          refine ⟨1274288258129050671056171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849525505419367114037447 1274288258129050671056171)
          ·
            refine ⟨1911432387193576006584257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274288258129050671056171 1911432387193576006584257)
            ·
              refine ⟨1433574290395182004938193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911432387193576006584257 1433574290395182004938193)
              ·
                refine ⟨1075180717796386503703645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433574290395182004938193 1075180717796386503703645)
                ·
                  refine ⟨403192769173644938888867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075180717796386503703645 403192769173644938888867)
                  ·
                    rfl

theorem cell20_883367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_883367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883367 prefixEnd_883367 := by exact prefixLift 883367
  have htrace : WordTrace (prefixWord ++ tailWord_883367) baseStart_883367 baseEnd_883367 := by
    simpa [prefixWord, tailWord_883367, baseEnd_883367] using wordTrace_append hprefix tailTrace_883367
  have hstable : (prefixWord ++ tailWord_883367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883367).length < 2 ^ (prefixWord ++ tailWord_883367).sum := by decide
  have hdescent : baseEnd_883367 < baseStart_883367 := by decide
  rcases family_descends (prefixWord ++ tailWord_883367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883402 : List Nat := [3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_883402 : Nat := 118140960795 + 883402 * 2 ^ 59
def prefixEnd_883402 : Nat := 4983230072969 + 3 ^ 40 * 883402 * 2
def baseEnd_883402 : Nat := 134402914709113457574019

theorem tailTrace_883402 : CollatzResearch.WordTrace tailWord_883402 prefixEnd_883402 134402914709113457574019 := by
  unfold tailWord_883402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055079486398225473773115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21480211963728601263394973 8055079486398225473773115)
  ·
    refine ⟨12082619229597338210659673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055079486398225473773115 12082619229597338210659673)
    ·
      refine ⟨9061964422198003657994755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12082619229597338210659673 9061964422198003657994755)
      ·
        refine ⟨13592946633297005486992133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9061964422198003657994755 13592946633297005486992133)
        ·
          refine ⟨2548677493743188528811025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13592946633297005486992133 2548677493743188528811025)
          ·
            refine ⟨1911508120307391396608269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548677493743188528811025 1911508120307391396608269)
            ·
              refine ⟨716815545115271773728101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911508120307391396608269 716815545115271773728101)
              ·
                refine ⟨134402914709113457574019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716815545115271773728101 134402914709113457574019)
                ·
                  rfl

theorem cell20_883402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_883402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883402 prefixEnd_883402 := by exact prefixLift 883402
  have htrace : WordTrace (prefixWord ++ tailWord_883402) baseStart_883402 baseEnd_883402 := by
    simpa [prefixWord, tailWord_883402, baseEnd_883402] using wordTrace_append hprefix tailTrace_883402
  have hstable : (prefixWord ++ tailWord_883402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883402).length < 2 ^ (prefixWord ++ tailWord_883402).sum := by decide
  have hdescent : baseEnd_883402 < baseStart_883402 := by decide
  rcases family_descends (prefixWord ++ tailWord_883402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883488 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_883488 : Nat := 118140960795 + 883488 * 2 ^ 59
def prefixEnd_883488 : Nat := 4983230072969 + 3 ^ 40 * 883488 * 2
def baseEnd_883488 : Nat := 403247996870706295855039

theorem tailTrace_883488 : CollatzResearch.WordTrace tailWord_883488 prefixEnd_883488 403247996870706295855039 := by
  unfold tailWord_883488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111727311640669291361559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21482303082187559055148745 16111727311640669291361559)
  ·
    refine ⟨24167590967461003937042339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16111727311640669291361559 24167590967461003937042339)
    ·
      refine ⟨36251386451191505905563509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24167590967461003937042339 36251386451191505905563509)
      ·
        refine ⟨3398567479799203678646579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36251386451191505905563509 3398567479799203678646579)
        ·
          refine ⟨5097851219698805517969869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398567479799203678646579 5097851219698805517969869)
          ·
            refine ⟨1911694207387052069238701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5097851219698805517969869 1911694207387052069238701)
            ·
              refine ⟨716885327770144525964513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911694207387052069238701 716885327770144525964513)
              ·
                refine ⟨537663995827608394473385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716885327770144525964513 537663995827608394473385)
                ·
                  refine ⟨403247996870706295855039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537663995827608394473385 403247996870706295855039)
                  ·
                    rfl

theorem cell20_883488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_883488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883488 prefixEnd_883488 := by exact prefixLift 883488
  have htrace : WordTrace (prefixWord ++ tailWord_883488) baseStart_883488 baseEnd_883488 := by
    simpa [prefixWord, tailWord_883488, baseEnd_883488] using wordTrace_append hprefix tailTrace_883488
  have hstable : (prefixWord ++ tailWord_883488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883488).length < 2 ^ (prefixWord ++ tailWord_883488).sum := by decide
  have hdescent : baseEnd_883488 < baseStart_883488 := by decide
  rcases family_descends (prefixWord ++ tailWord_883488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883498 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_883498 : Nat := 118140960795 + 883498 * 2 ^ 59
def prefixEnd_883498 : Nat := 4983230072969 + 3 ^ 40 * 883498 * 2
def baseEnd_883498 : Nat := 403252561143190705521665

theorem tailTrace_883498 : CollatzResearch.WordTrace tailWord_883498 prefixEnd_883498 403252561143190705521665 := by
  unfold tailWord_883498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055954838311277572646787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21482546235496740193724765 8055954838311277572646787)
  ·
    refine ⟨12083932257466916358970181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055954838311277572646787 12083932257466916358970181)
    ·
      refine ⟨2265737298275046817306909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12083932257466916358970181 2265737298275046817306909)
      ·
        refine ⟨849651486853142556490091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2265737298275046817306909 849651486853142556490091)
        ·
          refine ⟨1274477230279713834735137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849651486853142556490091 1274477230279713834735137)
          ·
            refine ⟨955857922709785376051353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1274477230279713834735137 955857922709785376051353)
            ·
              refine ⟨716893442032339032038515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955857922709785376051353 716893442032339032038515)
              ·
                refine ⟨1075340163048508548057773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716893442032339032038515 1075340163048508548057773)
                ·
                  refine ⟨403252561143190705521665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075340163048508548057773 403252561143190705521665)
                  ·
                    rfl

theorem cell20_883498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_883498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883498 prefixEnd_883498 := by exact prefixLift 883498
  have htrace : WordTrace (prefixWord ++ tailWord_883498) baseStart_883498 baseEnd_883498 := by
    simpa [prefixWord, tailWord_883498, baseEnd_883498] using wordTrace_append hprefix tailTrace_883498
  have hstable : (prefixWord ++ tailWord_883498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883498).length < 2 ^ (prefixWord ++ tailWord_883498).sum := by decide
  have hdescent : baseEnd_883498 < baseStart_883498 := by decide
  rcases family_descends (prefixWord ++ tailWord_883498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883502 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_883502 : Nat := 118140960795 + 883502 * 2 ^ 59
def prefixEnd_883502 : Nat := 4983230072969 + 3 ^ 40 * 883502 * 2
def baseEnd_883502 : Nat := 403254386852184469388315

theorem tailTrace_883502 : CollatzResearch.WordTrace tailWord_883502 prefixEnd_883502 403254386852184469388315 := by
  unfold tailWord_883502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027995655653827371716595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21482643496820412649155173 4027995655653827371716595)
  ·
    refine ⟨6041993483480741057574893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4027995655653827371716595 6041993483480741057574893)
    ·
      refine ⟨2265747556305277896590585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6041993483480741057574893 2265747556305277896590585)
      ·
        refine ⟨1699310667228958422442939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2265747556305277896590585 1699310667228958422442939)
        ·
          refine ⟨2548966000843437633664409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699310667228958422442939 2548966000843437633664409)
          ·
            refine ⟨1911724500632578225248307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548966000843437633664409 1911724500632578225248307)
            ·
              refine ⟨2867586750948867337872461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911724500632578225248307 2867586750948867337872461)
              ·
                refine ⟨1075345031605825251702173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867586750948867337872461 1075345031605825251702173)
                ·
                  refine ⟨403254386852184469388315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075345031605825251702173 403254386852184469388315)
                  ·
                    rfl

theorem cell20_883502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_883502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883502 prefixEnd_883502 := by exact prefixLift 883502
  have htrace : WordTrace (prefixWord ++ tailWord_883502) baseStart_883502 baseEnd_883502 := by
    simpa [prefixWord, tailWord_883502, baseEnd_883502] using wordTrace_append hprefix tailTrace_883502
  have hstable : (prefixWord ++ tailWord_883502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883502).length < 2 ^ (prefixWord ++ tailWord_883502).sum := by decide
  have hdescent : baseEnd_883502 < baseStart_883502 := by decide
  rcases family_descends (prefixWord ++ tailWord_883502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883537 : List Nat := [1, 2, 2, 1, 7, 7]
def baseStart_883537 : Nat := 118140960795 + 883537 * 2 ^ 59
def prefixEnd_883537 : Nat := 4983230072969 + 3 ^ 40 * 883537 * 2
def baseEnd_883537 : Nat := 14935939326143700119315

theorem tailTrace_883537 : CollatzResearch.WordTrace tailWord_883537 prefixEnd_883537 14935939326143700119315 := by
  unfold tailWord_883537
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225241800103819951256865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21483494533402546634171243 32225241800103819951256865)
  ·
    refine ⟨24168931350077864963442649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32225241800103819951256865 24168931350077864963442649)
    ·
      refine ⟨18126698512558398722581987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24168931350077864963442649 18126698512558398722581987)
      ·
        refine ⟨27190047768837598083872981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18126698512558398722581987 27190047768837598083872981)
        ·
          refine ⟨637266744582131205090773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27190047768837598083872981 637266744582131205090773)
          ·
            refine ⟨14935939326143700119315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 637266744582131205090773 14935939326143700119315)
            ·
              rfl

theorem cell20_883537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 7].length) (baseStart_883537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883537 prefixEnd_883537 := by exact prefixLift 883537
  have htrace : WordTrace (prefixWord ++ tailWord_883537) baseStart_883537 baseEnd_883537 := by
    simpa [prefixWord, tailWord_883537, baseEnd_883537] using wordTrace_append hprefix tailTrace_883537
  have hstable : (prefixWord ++ tailWord_883537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883537).length < 2 ^ (prefixWord ++ tailWord_883537).sum := by decide
  have hdescent : baseEnd_883537 < baseStart_883537 := by decide
  rcases family_descends (prefixWord ++ tailWord_883537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883540 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_883540 : Nat := 118140960795 + 883540 * 2 ^ 59
def prefixEnd_883540 : Nat := 4983230072969 + 3 ^ 40 * 883540 * 2
def baseEnd_883540 : Nat := 403271731087625226121493

theorem tailTrace_883540 : CollatzResearch.WordTrace tailWord_883540 prefixEnd_883540 403271731087625226121493 := by
  unfold tailWord_883540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112675609546475731808037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21483567479395300975744049 16112675609546475731808037)
  ·
    refine ⟨3021126676789964199714007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16112675609546475731808037 3021126676789964199714007)
    ·
      refine ⟨4531690015184946299571011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021126676789964199714007 4531690015184946299571011)
      ·
        refine ⟨6797535022777419449356517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531690015184946299571011 6797535022777419449356517)
        ·
          refine ⟨1274537816770766146754347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6797535022777419449356517 1274537816770766146754347)
          ·
            refine ⟨1911806725156149220131521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274537816770766146754347 1911806725156149220131521)
            ·
              refine ⟨1433855043867111915098641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911806725156149220131521 1433855043867111915098641)
              ·
                refine ⟨1075391282900333936323981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433855043867111915098641 1075391282900333936323981)
                ·
                  refine ⟨403271731087625226121493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075391282900333936323981 403271731087625226121493)
                  ·
                    rfl

theorem cell20_883540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_883540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883540 prefixEnd_883540 := by exact prefixLift 883540
  have htrace : WordTrace (prefixWord ++ tailWord_883540) baseStart_883540 baseEnd_883540 := by
    simpa [prefixWord, tailWord_883540, baseEnd_883540] using wordTrace_append hprefix tailTrace_883540
  have hstable : (prefixWord ++ tailWord_883540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883540).length < 2 ^ (prefixWord ++ tailWord_883540).sum := by decide
  have hdescent : baseEnd_883540 < baseStart_883540 := by decide
  rcases family_descends (prefixWord ++ tailWord_883540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883551 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_883551 : Nat := 118140960795 + 883551 * 2 ^ 59
def prefixEnd_883551 : Nat := 4983230072969 + 3 ^ 40 * 883551 * 2
def baseEnd_883551 : Nat := 403276751787358076754781

theorem tailTrace_883551 : CollatzResearch.WordTrace tailWord_883551 prefixEnd_883551 403276751787358076754781 := by
  unfold tailWord_883551
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225752422053100342266507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21483834948035400228177671 32225752422053100342266507)
  ·
    refine ⟨48338628633079650513399761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32225752422053100342266507 48338628633079650513399761)
    ·
      refine ⟨36253971474809737885049821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48338628633079650513399761 36253971474809737885049821)
      ·
        refine ⟨13595239303053651706893683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36253971474809737885049821 13595239303053651706893683)
        ·
          refine ⟨20392858954580477560340525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13595239303053651706893683 20392858954580477560340525)
          ·
            refine ⟨7647322107967679085127697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20392858954580477560340525 7647322107967679085127697)
            ·
              refine ⟨5735491580975759313845773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647322107967679085127697 5735491580975759313845773)
              ·
                refine ⟨2150809342865909742692165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735491580975759313845773 2150809342865909742692165)
                ·
                  refine ⟨403276751787358076754781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150809342865909742692165 403276751787358076754781)
                  ·
                    rfl

theorem cell20_883551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_883551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883551 prefixEnd_883551 := by exact prefixLift 883551
  have htrace : WordTrace (prefixWord ++ tailWord_883551) baseStart_883551 baseEnd_883551 := by
    simpa [prefixWord, tailWord_883551, baseEnd_883551] using wordTrace_append hprefix tailTrace_883551
  have hstable : (prefixWord ++ tailWord_883551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883551).length < 2 ^ (prefixWord ++ tailWord_883551).sum := by decide
  have hdescent : baseEnd_883551 < baseStart_883551 := by decide
  rcases family_descends (prefixWord ++ tailWord_883551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883658 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_883658 : Nat := 118140960795 + 883658 * 2 ^ 59
def prefixEnd_883658 : Nat := 4983230072969 + 3 ^ 40 * 883658 * 2
def baseEnd_883658 : Nat := 403325589502941260187677

theorem tailTrace_883658 : CollatzResearch.WordTrace tailWord_883658 prefixEnd_883658 403325589502941260187677 := by
  unfold tailWord_883658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057413758166364404102907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21486436688443638410941085 8057413758166364404102907)
  ·
    refine ⟨12086120637249546606154361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8057413758166364404102907 12086120637249546606154361)
    ·
      refine ⟨9064590477937159954615771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12086120637249546606154361 9064590477937159954615771)
      ·
        refine ⟨13596885716905739931923657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064590477937159954615771 13596885716905739931923657)
        ·
          refine ⟨10197664287679304948942743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13596885716905739931923657 10197664287679304948942743)
          ·
            refine ⟨15296496431518957423414115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197664287679304948942743 15296496431518957423414115)
            ·
              refine ⟨22944744647278436135121173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296496431518957423414115 22944744647278436135121173)
              ·
                refine ⟨1075534905341176693833805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22944744647278436135121173 1075534905341176693833805)
                ·
                  refine ⟨403325589502941260187677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075534905341176693833805 403325589502941260187677)
                  ·
                    rfl

theorem cell20_883658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_883658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883658 prefixEnd_883658 := by exact prefixLift 883658
  have htrace : WordTrace (prefixWord ++ tailWord_883658) baseStart_883658 baseEnd_883658 := by
    simpa [prefixWord, tailWord_883658, baseEnd_883658] using wordTrace_append hprefix tailTrace_883658
  have hstable : (prefixWord ++ tailWord_883658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883658).length < 2 ^ (prefixWord ++ tailWord_883658).sum := by decide
  have hdescent : baseEnd_883658 < baseStart_883658 := by decide
  rcases family_descends (prefixWord ++ tailWord_883658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883672 : List Nat := [2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_883672 : Nat := 118140960795 + 883672 * 2 ^ 59
def prefixEnd_883672 : Nat := 4983230072969 + 3 ^ 40 * 883672 * 2
def baseEnd_883672 : Nat := 134443993161473144573651

theorem tailTrace_883672 : CollatzResearch.WordTrace tailWord_883672 prefixEnd_883672 134443993161473144573651 := by
  unfold tailWord_883672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16115082827307369003710635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21486777103076492004947513 16115082827307369003710635)
  ·
    refine ⟨24172624240961053505565953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16115082827307369003710635 24172624240961053505565953)
    ·
      refine ⟨18129468180720790129174465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24172624240961053505565953 18129468180720790129174465)
      ·
        refine ⟨13597101135540592596880849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18129468180720790129174465 13597101135540592596880849)
        ·
          refine ⟨10197825851655444447660637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597101135540592596880849 10197825851655444447660637)
          ·
            refine ⟨3824184694370791667872739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10197825851655444447660637 3824184694370791667872739)
            ·
              refine ⟨5736277041556187501809109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824184694370791667872739 5736277041556187501809109)
              ·
                refine ⟨134443993161473144573651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5736277041556187501809109 134443993161473144573651)
                ·
                  rfl

theorem cell20_883672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_883672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883672 prefixEnd_883672 := by exact prefixLift 883672
  have htrace : WordTrace (prefixWord ++ tailWord_883672) baseStart_883672 baseEnd_883672 := by
    simpa [prefixWord, tailWord_883672, baseEnd_883672] using wordTrace_append hprefix tailTrace_883672
  have hstable : (prefixWord ++ tailWord_883672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883672).length < 2 ^ (prefixWord ++ tailWord_883672).sum := by decide
  have hdescent : baseEnd_883672 < baseStart_883672 := by decide
  rcases family_descends (prefixWord ++ tailWord_883672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883713 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_883713 : Nat := 118140960795 + 883713 * 2 ^ 59
def prefixEnd_883713 : Nat := 4983230072969 + 3 ^ 40 * 883713 * 2
def baseEnd_883713 : Nat := 403350693001605513354119

theorem tailTrace_883713 : CollatzResearch.WordTrace tailWord_883713 prefixEnd_883713 403350693001605513354119 := by
  unfold tailWord_883713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32231661047466202009663793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21487774031644134673109195 32231661047466202009663793)
  ·
    refine ⟨24173745785599651507247845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32231661047466202009663793 24173745785599651507247845)
    ·
      refine ⟨4532577334799934657608971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24173745785599651507247845 4532577334799934657608971)
      ·
        refine ⟨6798866002199901986413457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4532577334799934657608971 6798866002199901986413457)
        ·
          refine ⟨5099149501649926489810093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798866002199901986413457 5099149501649926489810093)
          ·
            refine ⟨1912181063118722433678785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5099149501649926489810093 1912181063118722433678785)
            ·
              refine ⟨1434135797339041825259089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912181063118722433678785 1434135797339041825259089)
              ·
                refine ⟨1075601848004281368944317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434135797339041825259089 1075601848004281368944317)
                ·
                  refine ⟨403350693001605513354119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075601848004281368944317 403350693001605513354119)
                  ·
                    rfl

theorem cell20_883713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_883713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883713 prefixEnd_883713 := by exact prefixLift 883713
  have htrace : WordTrace (prefixWord ++ tailWord_883713) baseStart_883713 baseEnd_883713 := by
    simpa [prefixWord, tailWord_883713, baseEnd_883713] using wordTrace_append hprefix tailTrace_883713
  have hstable : (prefixWord ++ tailWord_883713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883713).length < 2 ^ (prefixWord ++ tailWord_883713).sum := by decide
  have hdescent : baseEnd_883713 < baseStart_883713 := by decide
  rcases family_descends (prefixWord ++ tailWord_883713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883754 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_883754 : Nat := 118140960795 + 883754 * 2 ^ 59
def prefixEnd_883754 : Nat := 4983230072969 + 3 ^ 40 * 883754 * 2
def baseEnd_883754 : Nat := 403369406518791592987285

theorem tailTrace_883754 : CollatzResearch.WordTrace tailWord_883754 prefixEnd_883754 403369406518791592987285 := by
  unfold tailWord_883754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058289110079416502976579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21488770960211777341270877 8058289110079416502976579)
  ·
    refine ⟨12087433665119124754464869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8058289110079416502976579 12087433665119124754464869)
    ·
      refine ⟨2266393812209835891462163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12087433665119124754464869 2266393812209835891462163)
      ·
        refine ⟨3399590718314753837193245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266393812209835891462163 3399590718314753837193245)
        ·
          refine ⟨1274846519368032688947467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3399590718314753837193245 1274846519368032688947467)
          ·
            refine ⟨1912269779052049033421201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274846519368032688947467 1912269779052049033421201)
            ·
              refine ⟨1434202334289036775065901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912269779052049033421201 1434202334289036775065901)
              ·
                refine ⟨537825875358388790649713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434202334289036775065901 537825875358388790649713)
                ·
                  refine ⟨403369406518791592987285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537825875358388790649713 403369406518791592987285)
                  ·
                    rfl

theorem cell20_883754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_883754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883754 prefixEnd_883754 := by exact prefixLift 883754
  have htrace : WordTrace (prefixWord ++ tailWord_883754) baseStart_883754 baseEnd_883754 := by
    simpa [prefixWord, tailWord_883754, baseEnd_883754] using wordTrace_append hprefix tailTrace_883754
  have hstable : (prefixWord ++ tailWord_883754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883754).length < 2 ^ (prefixWord ++ tailWord_883754).sum := by decide
  have hdescent : baseEnd_883754 < baseStart_883754 := by decide
  rcases family_descends (prefixWord ++ tailWord_883754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883755 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_883755 : Nat := 118140960795 + 883755 * 2 ^ 59
def prefixEnd_883755 : Nat := 4983230072969 + 3 ^ 40 * 883755 * 2
def baseEnd_883755 : Nat := 403369862946040033953947

theorem tailTrace_883755 : CollatzResearch.WordTrace tailWord_883755 prefixEnd_883755 403369862946040033953947 := by
  unfold tailWord_883755
  simp only [CollatzResearch.WordTrace]
  refine ⟨32233192913314043182692719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21488795275542695455128479 32233192913314043182692719)
  ·
    refine ⟨48349789369971064774039079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32233192913314043182692719 48349789369971064774039079)
    ·
      refine ⟨72524684054956597161058619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48349789369971064774039079 72524684054956597161058619)
      ·
        refine ⟨108787026082434895741587929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72524684054956597161058619 108787026082434895741587929)
        ·
          refine ⟨81590269561826171806190947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108787026082434895741587929 81590269561826171806190947)
          ·
            refine ⟨122385404342739257709286421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81590269561826171806190947 122385404342739257709286421)
            ·
              refine ⟨5736815828565902705122801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122385404342739257709286421 5736815828565902705122801)
              ·
                refine ⟨4302611871424427028842101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736815828565902705122801 4302611871424427028842101)
                ·
                  refine ⟨403369862946040033953947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302611871424427028842101 403369862946040033953947)
                  ·
                    rfl

theorem cell20_883755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_883755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883755 prefixEnd_883755 := by exact prefixLift 883755
  have htrace : WordTrace (prefixWord ++ tailWord_883755) baseStart_883755 baseEnd_883755 := by
    simpa [prefixWord, tailWord_883755, baseEnd_883755] using wordTrace_append hprefix tailTrace_883755
  have hstable : (prefixWord ++ tailWord_883755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883755).length < 2 ^ (prefixWord ++ tailWord_883755).sum := by decide
  have hdescent : baseEnd_883755 < baseStart_883755 := by decide
  rcases family_descends (prefixWord ++ tailWord_883755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883772 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_883772 : Nat := 118140960795 + 883772 * 2 ^ 59
def prefixEnd_883772 : Nat := 4983230072969 + 3 ^ 40 * 883772 * 2
def baseEnd_883772 : Nat := 403377622209263530387211

theorem tailTrace_883772 : CollatzResearch.WordTrace tailWord_883772 prefixEnd_883772 403377622209263530387211 := by
  unfold tailWord_883772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116906477126227543030785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21489208636168303390707713 16116906477126227543030785)
  ·
    refine ⟨12087679857844670657273089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16116906477126227543030785 12087679857844670657273089)
    ·
      refine ⟨9065759893383502992954817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12087679857844670657273089 9065759893383502992954817)
      ·
        refine ⟨6799319920037627244716113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9065759893383502992954817 6799319920037627244716113)
        ·
          refine ⟨5099489940028220433537085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6799319920037627244716113 5099489940028220433537085)
          ·
            refine ⟨1912308727510582662576407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5099489940028220433537085 1912308727510582662576407)
            ·
              refine ⟨2868463091265873993864611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912308727510582662576407 2868463091265873993864611)
              ·
                refine ⟨4302694636898810990796917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868463091265873993864611 4302694636898810990796917)
                ·
                  refine ⟨403377622209263530387211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302694636898810990796917 403377622209263530387211)
                  ·
                    rfl

theorem cell20_883772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_883772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883772 prefixEnd_883772 := by exact prefixLift 883772
  have htrace : WordTrace (prefixWord ++ tailWord_883772) baseStart_883772 baseEnd_883772 := by
    simpa [prefixWord, tailWord_883772, baseEnd_883772] using wordTrace_append hprefix tailTrace_883772
  have hstable : (prefixWord ++ tailWord_883772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883772).length < 2 ^ (prefixWord ++ tailWord_883772).sum := by decide
  have hdescent : baseEnd_883772 < baseStart_883772 := by decide
  rcases family_descends (prefixWord ++ tailWord_883772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883779 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_883779 : Nat := 118140960795 + 883779 * 2 ^ 59
def prefixEnd_883779 : Nat := 4983230072969 + 3 ^ 40 * 883779 * 2
def baseEnd_883779 : Nat := 403380817200002617153849

theorem tailTrace_883779 : CollatzResearch.WordTrace tailWord_883779 prefixEnd_883779 403380817200002617153849 := by
  unfold tailWord_883779
  simp only [CollatzResearch.WordTrace]
  refine ⟨32234068265227095281566391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21489378843484730187710927 32234068265227095281566391)
  ·
    refine ⟨48351102397840642922349587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32234068265227095281566391 48351102397840642922349587)
    ·
      refine ⟨72526653596760964383524381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48351102397840642922349587 72526653596760964383524381)
      ·
        refine ⟨27197495098785361643821643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72526653596760964383524381 27197495098785361643821643)
        ·
          refine ⟨40796242648178042465732465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27197495098785361643821643 40796242648178042465732465)
          ·
            refine ⟨30597181986133531849299349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40796242648178042465732465 30597181986133531849299349)
            ·
              refine ⟨1434242905600009305435907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30597181986133531849299349 1434242905600009305435907)
              ·
                refine ⟨2151364358400013958153861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434242905600009305435907 2151364358400013958153861)
                ·
                  refine ⟨403380817200002617153849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151364358400013958153861 403380817200002617153849)
                  ·
                    rfl

theorem cell20_883779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_883779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883779 prefixEnd_883779 := by exact prefixLift 883779
  have htrace : WordTrace (prefixWord ++ tailWord_883779) baseStart_883779 baseEnd_883779 := by
    simpa [prefixWord, tailWord_883779, baseEnd_883779] using wordTrace_append hprefix tailTrace_883779
  have hstable : (prefixWord ++ tailWord_883779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883779).length < 2 ^ (prefixWord ++ tailWord_883779).sum := by decide
  have hdescent : baseEnd_883779 < baseStart_883779 := by decide
  rcases family_descends (prefixWord ++ tailWord_883779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883806 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_883806 : Nat := 118140960795 + 883806 * 2 ^ 59
def prefixEnd_883806 : Nat := 4983230072969 + 3 ^ 40 * 883806 * 2
def baseEnd_883806 : Nat := 403393140735710523253739

theorem tailTrace_883806 : CollatzResearch.WordTrace tailWord_883806 prefixEnd_883806 403393140735710523253739 := by
  unfold tailWord_883806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029381629516159861599909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21490035357419519261866181 4029381629516159861599909)
  ·
    refine ⟨755509055534279974049983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4029381629516159861599909 755509055534279974049983)
    ·
      refine ⟨1133263583301419961074975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755509055534279974049983 1133263583301419961074975)
      ·
        refine ⟨1699895374952129941612463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133263583301419961074975 1699895374952129941612463)
        ·
          refine ⟨2549843062428194912418695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699895374952129941612463 2549843062428194912418695)
          ·
            refine ⟨3824764593642292368628043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549843062428194912418695 3824764593642292368628043)
            ·
              refine ⟨5737146890463438552942065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824764593642292368628043 5737146890463438552942065)
              ·
                refine ⟨4302860167847578914706549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737146890463438552942065 4302860167847578914706549)
                ·
                  refine ⟨403393140735710523253739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302860167847578914706549 403393140735710523253739)
                  ·
                    rfl

theorem cell20_883806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_883806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883806 prefixEnd_883806 := by exact prefixLift 883806
  have htrace : WordTrace (prefixWord ++ tailWord_883806) baseStart_883806 baseEnd_883806 := by
    simpa [prefixWord, tailWord_883806, baseEnd_883806] using wordTrace_append hprefix tailTrace_883806
  have hstable : (prefixWord ++ tailWord_883806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883806).length < 2 ^ (prefixWord ++ tailWord_883806).sum := by decide
  have hdescent : baseEnd_883806 < baseStart_883806 := by decide
  rcases family_descends (prefixWord ++ tailWord_883806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883830 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_883830 : Nat := 118140960795 + 883830 * 2 ^ 59
def prefixEnd_883830 : Nat := 4983230072969 + 3 ^ 40 * 883830 * 2
def baseEnd_883830 : Nat := 403404094989673106453641

theorem tailTrace_883830 : CollatzResearch.WordTrace tailWord_883830 prefixEnd_883830 403404094989673106453641 := by
  unfold tailWord_883830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014745524252645686979559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21490618925361553994448629 2014745524252645686979559)
  ·
    refine ⟨3022118286378968530469339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2014745524252645686979559 3022118286378968530469339)
    ·
      refine ⟨4533177429568452795704009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022118286378968530469339 4533177429568452795704009)
      ·
        refine ⟨3399883072176339596778007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533177429568452795704009 3399883072176339596778007)
        ·
          refine ⟨5099824608264509395167011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399883072176339596778007 5099824608264509395167011)
          ·
            refine ⟨7649736912396764092750517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099824608264509395167011 7649736912396764092750517)
            ·
              refine ⟨717162835537196633695361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7649736912396764092750517 717162835537196633695361)
              ·
                refine ⟨537872126652897475271521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717162835537196633695361 537872126652897475271521)
                ·
                  refine ⟨403404094989673106453641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537872126652897475271521 403404094989673106453641)
                  ·
                    rfl

theorem cell20_883830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_883830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883830 prefixEnd_883830 := by exact prefixLift 883830
  have htrace : WordTrace (prefixWord ++ tailWord_883830) baseStart_883830 baseEnd_883830 := by
    simpa [prefixWord, tailWord_883830, baseEnd_883830] using wordTrace_append hprefix tailTrace_883830
  have hstable : (prefixWord ++ tailWord_883830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883830).length < 2 ^ (prefixWord ++ tailWord_883830).sum := by decide
  have hdescent : baseEnd_883830 < baseStart_883830 := by decide
  rcases family_descends (prefixWord ++ tailWord_883830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883831 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_883831 : Nat := 118140960795 + 883831 * 2 ^ 59
def prefixEnd_883831 : Nat := 4983230072969 + 3 ^ 40 * 883831 * 2
def baseEnd_883831 : Nat := 403404551416921547420303

theorem tailTrace_883831 : CollatzResearch.WordTrace tailWord_883831 prefixEnd_883831 403404551416921547420303 := by
  unfold tailWord_883831
  simp only [CollatzResearch.WordTrace]
  refine ⟨32235964861038708162459347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21490643240692472108306231 32235964861038708162459347)
  ·
    refine ⟨48353947291558062243689021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32235964861038708162459347 48353947291558062243689021)
    ·
      refine ⟨18132730234334273341383383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48353947291558062243689021 18132730234334273341383383)
      ·
        refine ⟨27199095351501410012075075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18132730234334273341383383 27199095351501410012075075)
        ·
          refine ⟨40798643027252115018112613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27199095351501410012075075 40798643027252115018112613)
          ·
            refine ⟨7649745567609771565896115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40798643027252115018112613 7649745567609771565896115)
            ·
              refine ⟨11474618351414657348844173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649745567609771565896115 11474618351414657348844173)
              ·
                refine ⟨4302981881780496505816565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11474618351414657348844173 4302981881780496505816565)
                ·
                  refine ⟨403404551416921547420303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302981881780496505816565 403404551416921547420303)
                  ·
                    rfl

theorem cell20_883831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_883831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883831 prefixEnd_883831 := by exact prefixLift 883831
  have htrace : WordTrace (prefixWord ++ tailWord_883831) baseStart_883831 baseEnd_883831 := by
    simpa [prefixWord, tailWord_883831, baseEnd_883831] using wordTrace_append hprefix tailTrace_883831
  have hstable : (prefixWord ++ tailWord_883831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883831).length < 2 ^ (prefixWord ++ tailWord_883831).sum := by decide
  have hdescent : baseEnd_883831 < baseStart_883831 := by decide
  rcases family_descends (prefixWord ++ tailWord_883831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883841 : List Nat := [1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_883841 : Nat := 118140960795 + 883841 * 2 ^ 59
def prefixEnd_883841 : Nat := 4983230072969 + 3 ^ 40 * 883841 * 2
def baseEnd_883841 : Nat := 134469705229801985695643

theorem tailTrace_883841 : CollatzResearch.WordTrace tailWord_883841 prefixEnd_883841 134469705229801985695643 := by
  unfold tailWord_883841
  simp only [CollatzResearch.WordTrace]
  refine ⟨32236329591002479870323377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21490886394001653246882251 32236329591002479870323377)
  ·
    refine ⟨24177247193251859902742533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32236329591002479870323377 24177247193251859902742533)
    ·
      refine ⟨4533233848734723731764225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24177247193251859902742533 4533233848734723731764225)
      ·
        refine ⟨3399925386551042798823169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533233848734723731764225 3399925386551042798823169)
        ·
          refine ⟨2549944039913282099117377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399925386551042798823169 2549944039913282099117377)
          ·
            refine ⟨1912458029934961574338033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2549944039913282099117377 1912458029934961574338033)
            ·
              refine ⟨1434343522451221180753525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912458029934961574338033 1434343522451221180753525)
              ·
                refine ⟨134469705229801985695643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434343522451221180753525 134469705229801985695643)
                ·
                  rfl

theorem cell20_883841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_883841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883841 prefixEnd_883841 := by exact prefixLift 883841
  have htrace : WordTrace (prefixWord ++ tailWord_883841) baseStart_883841 baseEnd_883841 := by
    simpa [prefixWord, tailWord_883841, baseEnd_883841] using wordTrace_append hprefix tailTrace_883841
  have hstable : (prefixWord ++ tailWord_883841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883841).length < 2 ^ (prefixWord ++ tailWord_883841).sum := by decide
  have hdescent : baseEnd_883841 < baseStart_883841 := by decide
  rcases family_descends (prefixWord ++ tailWord_883841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883844 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_883844 : Nat := 118140960795 + 883844 * 2 ^ 59
def prefixEnd_883844 : Nat := 4983230072969 + 3 ^ 40 * 883844 * 2
def baseEnd_883844 : Nat := 403410484971151279986917

theorem tailTrace_883844 : CollatzResearch.WordTrace tailWord_883844 prefixEnd_883844 403410484971151279986917 := by
  unfold tailWord_883844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118219504995805691341293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21490959339994407588455057 16118219504995805691341293)
  ·
    refine ⟨6044332314373427134252985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16118219504995805691341293 6044332314373427134252985)
    ·
      refine ⟨4533249235780070350689739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6044332314373427134252985 4533249235780070350689739)
      ·
        refine ⟨6799873853670105526034609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533249235780070350689739 6799873853670105526034609)
        ·
          refine ⟨5099905390252579144525957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6799873853670105526034609 5099905390252579144525957)
          ·
            refine ⟨956232260672358589598617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5099905390252579144525957 956232260672358589598617)
            ·
              refine ⟨717174195504268942198963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956232260672358589598617 717174195504268942198963)
              ·
                refine ⟨1075761293256403413298445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717174195504268942198963 1075761293256403413298445)
                ·
                  refine ⟨403410484971151279986917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075761293256403413298445 403410484971151279986917)
                  ·
                    rfl

theorem cell20_883844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_883844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883844 prefixEnd_883844 := by exact prefixLift 883844
  have htrace : WordTrace (prefixWord ++ tailWord_883844) baseStart_883844 baseEnd_883844 := by
    simpa [prefixWord, tailWord_883844, baseEnd_883844] using wordTrace_append hprefix tailTrace_883844
  have hstable : (prefixWord ++ tailWord_883844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883844).length < 2 ^ (prefixWord ++ tailWord_883844).sum := by decide
  have hdescent : baseEnd_883844 < baseStart_883844 := by decide
  rcases family_descends (prefixWord ++ tailWord_883844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883872 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_883872 : Nat := 118140960795 + 883872 * 2 ^ 59
def prefixEnd_883872 : Nat := 4983230072969 + 3 ^ 40 * 883872 * 2
def baseEnd_883872 : Nat := 403423264934107627053469

theorem tailTrace_883872 : CollatzResearch.WordTrace tailWord_883872 prefixEnd_883872 403423264934107627053469 := by
  unfold tailWord_883872
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118730126945086082350935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21491640169260114776467913 16118730126945086082350935)
  ·
    refine ⟨24178095190417629123526403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16118730126945086082350935 24178095190417629123526403)
    ·
      refine ⟨36267142785626443685289605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24178095190417629123526403 36267142785626443685289605)
      ·
        refine ⟨6800089272304958190991801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36267142785626443685289605 6800089272304958190991801)
        ·
          refine ⟨5100066954228718643243851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6800089272304958190991801 5100066954228718643243851)
          ·
            refine ⟨7650100431343077964865777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100066954228718643243851 7650100431343077964865777)
            ·
              refine ⟨5737575323507308473649333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7650100431343077964865777 5737575323507308473649333)
              ·
                refine ⟨537897686578810169404625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5737575323507308473649333 537897686578810169404625)
                ·
                  refine ⟨403423264934107627053469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537897686578810169404625 403423264934107627053469)
                  ·
                    rfl

theorem cell20_883872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_883872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883872 prefixEnd_883872 := by exact prefixLift 883872
  have htrace : WordTrace (prefixWord ++ tailWord_883872) baseStart_883872 baseEnd_883872 := by
    simpa [prefixWord, tailWord_883872, baseEnd_883872] using wordTrace_append hprefix tailTrace_883872
  have hstable : (prefixWord ++ tailWord_883872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883872).length < 2 ^ (prefixWord ++ tailWord_883872).sum := by decide
  have hdescent : baseEnd_883872 < baseStart_883872 := by decide
  rcases family_descends (prefixWord ++ tailWord_883872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883882 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_883882 : Nat := 118140960795 + 883882 * 2 ^ 59
def prefixEnd_883882 : Nat := 4983230072969 + 3 ^ 40 * 883882 * 2
def baseEnd_883882 : Nat := 403427829206592036720095

theorem tailTrace_883882 : CollatzResearch.WordTrace tailWord_883882 prefixEnd_883882 403427829206592036720095 := by
  unfold tailWord_883882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059456245963485968141475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21491883322569295915043933 8059456245963485968141475)
  ·
    refine ⟨12089184368945228952212213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059456245963485968141475 12089184368945228952212213)
    ·
      refine ⟨1133361034588615214269895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12089184368945228952212213 1133361034588615214269895)
      ·
        refine ⟨1700041551882922821404843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133361034588615214269895 1700041551882922821404843)
        ·
          refine ⟨2550062327824384232107265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700041551882922821404843 2550062327824384232107265)
          ·
            refine ⟨1912546745868288174080449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2550062327824384232107265 1912546745868288174080449)
            ·
              refine ⟨1434410059401216130560337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912546745868288174080449 1434410059401216130560337)
              ·
                refine ⟨1075807544550912097920253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434410059401216130560337 1075807544550912097920253)
                ·
                  refine ⟨403427829206592036720095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075807544550912097920253 403427829206592036720095)
                  ·
                    rfl

theorem cell20_883882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_883882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883882 prefixEnd_883882 := by exact prefixLift 883882
  have htrace : WordTrace (prefixWord ++ tailWord_883882) baseStart_883882 baseEnd_883882 := by
    simpa [prefixWord, tailWord_883882, baseEnd_883882] using wordTrace_append hprefix tailTrace_883882
  have hstable : (prefixWord ++ tailWord_883882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883882).length < 2 ^ (prefixWord ++ tailWord_883882).sum := by decide
  have hdescent : baseEnd_883882 < baseStart_883882 := by decide
  rcases family_descends (prefixWord ++ tailWord_883882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883885 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 2]
def baseStart_883885 : Nat := 118140960795 + 883885 * 2 ^ 59
def prefixEnd_883885 : Nat := 4983230072969 + 3 ^ 40 * 883885 * 2
def baseEnd_883885 : Nat := 403429198488337359620083

theorem tailTrace_883885 : CollatzResearch.WordTrace tailWord_883885 prefixEnd_883885 403429198488337359620083 := by
  unfold tailWord_883885
  simp only [CollatzResearch.WordTrace]
  refine ⟨32237934402843075384925109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21491956268562050256616739 32237934402843075384925109)
  ·
    refine ⟨3022306350266538317336729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32237934402843075384925109 3022306350266538317336729)
    ·
      refine ⟨2266729762699903738002547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3022306350266538317336729 2266729762699903738002547)
      ·
        refine ⟨3400094644049855607003821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266729762699903738002547 3400094644049855607003821)
        ·
          refine ⟨1275035491518695852626433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400094644049855607003821 1275035491518695852626433)
          ·
            refine ⟨956276618639021889469825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275035491518695852626433 956276618639021889469825)
            ·
              refine ⟨717207463979266417102369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956276618639021889469825 717207463979266417102369)
              ·
                refine ⟨537905597984449812826777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717207463979266417102369 537905597984449812826777)
                ·
                  refine ⟨403429198488337359620083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537905597984449812826777 403429198488337359620083)
                  ·
                    rfl

theorem cell20_883885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_883885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883885 prefixEnd_883885 := by exact prefixLift 883885
  have htrace : WordTrace (prefixWord ++ tailWord_883885) baseStart_883885 baseEnd_883885 := by
    simpa [prefixWord, tailWord_883885, baseEnd_883885] using wordTrace_append hprefix tailTrace_883885
  have hstable : (prefixWord ++ tailWord_883885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883885).length < 2 ^ (prefixWord ++ tailWord_883885).sum := by decide
  have hdescent : baseEnd_883885 < baseStart_883885 := by decide
  rcases family_descends (prefixWord ++ tailWord_883885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883889 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 2]
def baseStart_883889 : Nat := 118140960795 + 883889 * 2 ^ 59
def prefixEnd_883889 : Nat := 4983230072969 + 3 ^ 40 * 883889 * 2
def baseEnd_883889 : Nat := 403431024197331123486733

theorem tailTrace_883889 : CollatzResearch.WordTrace tailWord_883889 prefixEnd_883889 403431024197331123486733 := by
  unfold tailWord_883889
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238080294828584068070721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492053529885722712047147 32238080294828584068070721)
  ·
    refine ⟨24178560221121438051053041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32238080294828584068070721 24178560221121438051053041)
    ·
      refine ⟨18133920165841078538289781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24178560221121438051053041 18133920165841078538289781)
      ·
        refine ⟨1700055015547601112964667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18133920165841078538289781 1700055015547601112964667)
        ·
          refine ⟨2550082523321401669447001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700055015547601112964667 2550082523321401669447001)
          ·
            refine ⟨1912561892491051252085251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2550082523321401669447001 1912561892491051252085251)
            ·
              refine ⟨2868842838736576878127877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912561892491051252085251 2868842838736576878127877)
              ·
                refine ⟨537908032263108164648977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2868842838736576878127877 537908032263108164648977)
                ·
                  refine ⟨403431024197331123486733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537908032263108164648977 403431024197331123486733)
                  ·
                    rfl

theorem cell20_883889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_883889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883889 prefixEnd_883889 := by exact prefixLift 883889
  have htrace : WordTrace (prefixWord ++ tailWord_883889) baseStart_883889 baseEnd_883889 := by
    simpa [prefixWord, tailWord_883889, baseEnd_883889] using wordTrace_append hprefix tailTrace_883889
  have hstable : (prefixWord ++ tailWord_883889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883889).length < 2 ^ (prefixWord ++ tailWord_883889).sum := by decide
  have hdescent : baseEnd_883889 < baseStart_883889 := by decide
  rcases family_descends (prefixWord ++ tailWord_883889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883906 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_883906 : Nat := 118140960795 + 883906 * 2 ^ 59
def prefixEnd_883906 : Nat := 4983230072969 + 3 ^ 40 * 883906 * 2
def baseEnd_883906 : Nat := 403438783460554619919997

theorem tailTrace_883906 : CollatzResearch.WordTrace tailWord_883906 prefixEnd_883906 403438783460554619919997 := by
  unfold tailWord_883906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059675083941748992859893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21492466890511330647626381 8059675083941748992859893)
  ·
    refine ⟨755594539119538968080615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8059675083941748992859893 755594539119538968080615)
    ·
      refine ⟨1133391808679308452120923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755594539119538968080615 1133391808679308452120923)
      ·
        refine ⟨1700087713018962678181385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133391808679308452120923 1700087713018962678181385)
        ·
          refine ⟨1275065784764222008636039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700087713018962678181385 1275065784764222008636039)
          ·
            refine ⟨1912598677146333012954059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275065784764222008636039 1912598677146333012954059)
            ·
              refine ⟨2868898015719499519431089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912598677146333012954059 2868898015719499519431089)
              ·
                refine ⟨2151673511789624639573317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868898015719499519431089 2151673511789624639573317)
                ·
                  refine ⟨403438783460554619919997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151673511789624639573317 403438783460554619919997)
                  ·
                    rfl

theorem cell20_883906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_883906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883906 prefixEnd_883906 := by exact prefixLift 883906
  have htrace : WordTrace (prefixWord ++ tailWord_883906) baseStart_883906 baseEnd_883906 := by
    simpa [prefixWord, tailWord_883906, baseEnd_883906] using wordTrace_append hprefix tailTrace_883906
  have hstable : (prefixWord ++ tailWord_883906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883906).length < 2 ^ (prefixWord ++ tailWord_883906).sum := by decide
  have hdescent : baseEnd_883906 < baseStart_883906 := by decide
  rcases family_descends (prefixWord ++ tailWord_883906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883948 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_883948 : Nat := 118140960795 + 883948 * 2 ^ 59
def prefixEnd_883948 : Nat := 4983230072969 + 3 ^ 40 * 883948 * 2
def baseEnd_883948 : Nat := 403457953404989140519825

theorem tailTrace_883948 : CollatzResearch.WordTrace tailWord_883948 prefixEnd_883948 403457953404989140519825 := by
  unfold tailWord_883948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120116100807418572234249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21493488134409891429645665 16120116100807418572234249)
  ·
    refine ⟨12090087075605563929175687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16120116100807418572234249 12090087075605563929175687)
    ·
      refine ⟨18135130613408345893763531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12090087075605563929175687 18135130613408345893763531)
      ·
        refine ⟨27202695920112518840645297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18135130613408345893763531 27202695920112518840645297)
        ·
          refine ⟨20402021940084389130483973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27202695920112518840645297 20402021940084389130483973)
          ·
            refine ⟨3825379113765822961965745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20402021940084389130483973 3825379113765822961965745)
            ·
              refine ⟨2869034335324367221474309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825379113765822961965745 2869034335324367221474309)
              ·
                refine ⟨537943937873318854026433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2869034335324367221474309 537943937873318854026433)
                ·
                  refine ⟨403457953404989140519825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537943937873318854026433 403457953404989140519825)
                  ·
                    rfl

theorem cell20_883948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_883948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883948 prefixEnd_883948 := by exact prefixLift 883948
  have htrace : WordTrace (prefixWord ++ tailWord_883948) baseStart_883948 baseEnd_883948 := by
    simpa [prefixWord, tailWord_883948, baseEnd_883948] using wordTrace_append hprefix tailTrace_883948
  have hstable : (prefixWord ++ tailWord_883948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883948).length < 2 ^ (prefixWord ++ tailWord_883948).sum := by decide
  have hdescent : baseEnd_883948 < baseStart_883948 := by decide
  rcases family_descends (prefixWord ++ tailWord_883948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883969 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_883969 : Nat := 118140960795 + 883969 * 2 ^ 59
def prefixEnd_883969 : Nat := 4983230072969 + 3 ^ 40 * 883969 * 2
def baseEnd_883969 : Nat := 403467538377206400819739

theorem tailTrace_883969 : CollatzResearch.WordTrace tailWord_883969 prefixEnd_883969 403467538377206400819739 := by
  unfold tailWord_883969
  simp only [CollatzResearch.WordTrace]
  refine ⟨32240998134538757730982961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21493998756359171820655307 32240998134538757730982961)
  ·
    refine ⟨24180748600904068298237221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32240998134538757730982961 24180748600904068298237221)
    ·
      refine ⟨4533890362669512805919479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24180748600904068298237221 4533890362669512805919479)
      ·
        refine ⟨6800835544004269208879219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533890362669512805919479 6800835544004269208879219)
        ·
          refine ⟨10201253316006403813318829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800835544004269208879219 10201253316006403813318829)
          ·
            refine ⟨3825469993502401429994561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10201253316006403813318829 3825469993502401429994561)
            ·
              refine ⟨2869102495126801072495921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825469993502401429994561 2869102495126801072495921)
              ·
                refine ⟨2151826871345100804371941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869102495126801072495921 2151826871345100804371941)
                ·
                  refine ⟨403467538377206400819739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151826871345100804371941 403467538377206400819739)
                  ·
                    rfl

theorem cell20_883969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_883969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883969 prefixEnd_883969 := by exact prefixLift 883969
  have htrace : WordTrace (prefixWord ++ tailWord_883969) baseStart_883969 baseEnd_883969 := by
    simpa [prefixWord, tailWord_883969, baseEnd_883969] using wordTrace_append hprefix tailTrace_883969
  have hstable : (prefixWord ++ tailWord_883969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883969).length < 2 ^ (prefixWord ++ tailWord_883969).sum := by decide
  have hdescent : baseEnd_883969 < baseStart_883969 := by decide
  rcases family_descends (prefixWord ++ tailWord_883969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883972 : List Nat := [2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_883972 : Nat := 118140960795 + 883972 * 2 ^ 59
def prefixEnd_883972 : Nat := 4983230072969 + 3 ^ 40 * 883972 * 2
def baseEnd_883972 : Nat := 134489635886317241239909

theorem tailTrace_883972 : CollatzResearch.WordTrace tailWord_883972 prefixEnd_883972 134489635886317241239909 := by
  unfold tailWord_883972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120553776763944621671085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21494071702351926162228113 16120553776763944621671085)
  ·
    refine ⟨6045207666286479233126657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16120553776763944621671085 6045207666286479233126657)
    ·
      refine ⟨4533905749714859424844993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6045207666286479233126657 4533905749714859424844993)
      ·
        refine ⟨3400429312286144568633745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533905749714859424844993 3400429312286144568633745)
        ·
          refine ⟨2550321984214608426475309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3400429312286144568633745 2550321984214608426475309)
          ·
            refine ⟨956370744080478159928241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2550321984214608426475309 956370744080478159928241)
            ·
              refine ⟨717278058060358619946181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956370744080478159928241 717278058060358619946181)
              ·
                refine ⟨134489635886317241239909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717278058060358619946181 134489635886317241239909)
                ·
                  rfl

theorem cell20_883972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_883972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_883972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_883972 prefixEnd_883972 := by exact prefixLift 883972
  have htrace : WordTrace (prefixWord ++ tailWord_883972) baseStart_883972 baseEnd_883972 := by
    simpa [prefixWord, tailWord_883972, baseEnd_883972] using wordTrace_append hprefix tailTrace_883972
  have hstable : (prefixWord ++ tailWord_883972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883972).length < 2 ^ (prefixWord ++ tailWord_883972).sum := by decide
  have hdescent : baseEnd_883972 < baseStart_883972 := by decide
  rcases family_descends (prefixWord ++ tailWord_883972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884003 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 2]
def baseStart_884003 : Nat := 118140960795 + 884003 * 2 ^ 59
def prefixEnd_884003 : Nat := 4983230072969 + 3 ^ 40 * 884003 * 2
def baseEnd_884003 : Nat := 403483056903653393686267

theorem tailTrace_884003 : CollatzResearch.WordTrace tailWord_884003 prefixEnd_884003 403483056903653393686267 := by
  unfold tailWord_884003
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242238216415581537720663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21494825477610387691813775 32242238216415581537720663)
  ·
    refine ⟨48363357324623372306580995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32242238216415581537720663 48363357324623372306580995)
    ·
      refine ⟨72545035986935058459871493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48363357324623372306580995 72545035986935058459871493)
      ·
        refine ⟨13602194247550323461225905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72545035986935058459871493 13602194247550323461225905)
        ·
          refine ⟨10201645685662742595919429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13602194247550323461225905 10201645685662742595919429)
          ·
            refine ⟨1912808566061764236734893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10201645685662742595919429 1912808566061764236734893)
            ·
              refine ⟨717303212273161588775585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1912808566061764236734893 717303212273161588775585)
              ·
                refine ⟨537977409204871191581689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717303212273161588775585 537977409204871191581689)
                ·
                  refine ⟨403483056903653393686267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537977409204871191581689 403483056903653393686267)
                  ·
                    rfl

theorem cell20_884003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2].length) (baseStart_884003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884003 prefixEnd_884003 := by exact prefixLift 884003
  have htrace : WordTrace (prefixWord ++ tailWord_884003) baseStart_884003 baseEnd_884003 := by
    simpa [prefixWord, tailWord_884003, baseEnd_884003] using wordTrace_append hprefix tailTrace_884003
  have hstable : (prefixWord ++ tailWord_884003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884003).length < 2 ^ (prefixWord ++ tailWord_884003).sum := by decide
  have hdescent : baseEnd_884003 < baseStart_884003 := by decide
  rcases family_descends (prefixWord ++ tailWord_884003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884013 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 3]
def baseStart_884013 : Nat := 118140960795 + 884013 * 2 ^ 59
def prefixEnd_884013 : Nat := 4983230072969 + 3 ^ 40 * 884013 * 2
def baseEnd_884013 : Nat := 403487621176137803352893

theorem tailTrace_884013 : CollatzResearch.WordTrace tailWord_884013 prefixEnd_884013 403487621176137803352893 := by
  unfold tailWord_884013
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242602946379353245584693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21495068630919568830389795 32242602946379353245584693)
  ·
    refine ⟨3022744026223064366773565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32242602946379353245584693 3022744026223064366773565)
    ·
      refine ⟨1133529009833649137540087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3022744026223064366773565 1133529009833649137540087)
      ·
        refine ⟨1700293514750473706310131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133529009833649137540087 1700293514750473706310131)
        ·
          refine ⟨2550440272125710559465197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700293514750473706310131 2550440272125710559465197)
          ·
            refine ⟨956415102047141459799449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2550440272125710559465197 956415102047141459799449)
            ·
              refine ⟨717311326535356094849587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956415102047141459799449 717311326535356094849587)
              ·
                refine ⟨1075966989803034142274381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717311326535356094849587 1075966989803034142274381)
                ·
                  refine ⟨403487621176137803352893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075966989803034142274381 403487621176137803352893)
                  ·
                    rfl

theorem cell20_884013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_884013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884013 prefixEnd_884013 := by exact prefixLift 884013
  have htrace : WordTrace (prefixWord ++ tailWord_884013) baseStart_884013 baseEnd_884013 := by
    simpa [prefixWord, tailWord_884013, baseEnd_884013] using wordTrace_append hprefix tailTrace_884013
  have hstable : (prefixWord ++ tailWord_884013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884013).length < 2 ^ (prefixWord ++ tailWord_884013).sum := by decide
  have hdescent : baseEnd_884013 < baseStart_884013 := by decide
  rcases family_descends (prefixWord ++ tailWord_884013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884017 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 3]
def baseStart_884017 : Nat := 118140960795 + 884017 * 2 ^ 59
def prefixEnd_884017 : Nat := 4983230072969 + 3 ^ 40 * 884017 * 2
def baseEnd_884017 : Nat := 403489446885131567219543

theorem tailTrace_884017 : CollatzResearch.WordTrace tailWord_884017 prefixEnd_884017 403489446885131567219543 := by
  unfold tailWord_884017
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242748838364861928730305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21495165892243241285820203 32242748838364861928730305)
  ·
    refine ⟨24182061628773646446547729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32242748838364861928730305 24182061628773646446547729)
    ·
      refine ⟨18136546221580234834910797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24182061628773646446547729 18136546221580234834910797)
      ·
        refine ⟨6801204833092588063091549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18136546221580234834910797 6801204833092588063091549)
        ·
          refine ⟨2550451812409720523659331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6801204833092588063091549 2550451812409720523659331)
          ·
            refine ⟨3825677718614580785488997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550451812409720523659331 3825677718614580785488997)
            ·
              refine ⟨717314572240233897279187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3825677718614580785488997 717314572240233897279187)
              ·
                refine ⟨1075971858360350845918781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717314572240233897279187 1075971858360350845918781)
                ·
                  refine ⟨403489446885131567219543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075971858360350845918781 403489446885131567219543)
                  ·
                    rfl

theorem cell20_884017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_884017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884017 prefixEnd_884017 := by exact prefixLift 884017
  have htrace : WordTrace (prefixWord ++ tailWord_884017) baseStart_884017 baseEnd_884017 := by
    simpa [prefixWord, tailWord_884017, baseEnd_884017] using wordTrace_append hprefix tailTrace_884017
  have hstable : (prefixWord ++ tailWord_884017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884017).length < 2 ^ (prefixWord ++ tailWord_884017).sum := by decide
  have hdescent : baseEnd_884017 < baseStart_884017 := by decide
  rcases family_descends (prefixWord ++ tailWord_884017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884054 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_884054 : Nat := 118140960795 + 884054 * 2 ^ 59
def prefixEnd_884054 : Nat := 4983230072969 + 3 ^ 40 * 884054 * 2
def baseEnd_884054 : Nat := 403506334693323882986059

theorem tailTrace_884054 : CollatzResearch.WordTrace tailWord_884054 prefixEnd_884054 403506334693323882986059 := by
  unfold tailWord_884054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015256146201926077989201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21496065559487211498551477 2015256146201926077989201)
  ·
    refine ⟨1511442109651444558491901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2015256146201926077989201 1511442109651444558491901)
    ·
      refine ⟨566790791119291709434463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1511442109651444558491901 566790791119291709434463)
      ·
        refine ⟨850186186678937564151695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566790791119291709434463 850186186678937564151695)
        ·
          refine ⟨1275279280018406346227543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850186186678937564151695 1275279280018406346227543)
          ·
            refine ⟨1912918920027609519341315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275279280018406346227543 1912918920027609519341315)
            ·
              refine ⟨2869378380041414279011973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912918920027609519341315 2869378380041414279011973)
              ·
                refine ⟨538008446257765177314745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2869378380041414279011973 538008446257765177314745)
                ·
                  refine ⟨403506334693323882986059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538008446257765177314745 403506334693323882986059)
                  ·
                    rfl

theorem cell20_884054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_884054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884054 prefixEnd_884054 := by exact prefixLift 884054
  have htrace : WordTrace (prefixWord ++ tailWord_884054) baseStart_884054 baseEnd_884054 := by
    simpa [prefixWord, tailWord_884054, baseEnd_884054] using wordTrace_append hprefix tailTrace_884054
  have hstable : (prefixWord ++ tailWord_884054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884054).length < 2 ^ (prefixWord ++ tailWord_884054).sum := by decide
  have hdescent : baseEnd_884054 < baseStart_884054 := by decide
  rcases family_descends (prefixWord ++ tailWord_884054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884073 : List Nat := [1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_884073 : Nat := 118140960795 + 884073 * 2 ^ 59
def prefixEnd_884073 : Nat := 4983230072969 + 3 ^ 40 * 884073 * 2
def baseEnd_884073 : Nat := 134505002270348087117549

theorem tailTrace_884073 : CollatzResearch.WordTrace tailWord_884073 prefixEnd_884073 134505002270348087117549 := by
  unfold tailWord_884073
  simp only [CollatzResearch.WordTrace]
  refine ⟨32244791326161983492768873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21496527550774655661845915 32244791326161983492768873)
  ·
    refine ⟨24183593494621487619576655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32244791326161983492768873 24183593494621487619576655)
    ·
      refine ⟨36275390241932231429364983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24183593494621487619576655 36275390241932231429364983)
      ·
        refine ⟨54413085362898347144047475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36275390241932231429364983 54413085362898347144047475)
        ·
          refine ⟨81619628044347520716071213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54413085362898347144047475 81619628044347520716071213)
          ·
            refine ⟨30607360516630320268526705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81619628044347520716071213 30607360516630320268526705)
            ·
              refine ⟨22955520387472740201395029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30607360516630320268526705 22955520387472740201395029)
              ·
                refine ⟨134505002270348087117549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22955520387472740201395029 134505002270348087117549)
                ·
                  rfl

theorem cell20_884073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_884073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884073 prefixEnd_884073 := by exact prefixLift 884073
  have htrace : WordTrace (prefixWord ++ tailWord_884073) baseStart_884073 baseEnd_884073 := by
    simpa [prefixWord, tailWord_884073, baseEnd_884073] using wordTrace_append hprefix tailTrace_884073
  have hstable : (prefixWord ++ tailWord_884073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884073).length < 2 ^ (prefixWord ++ tailWord_884073).sum := by decide
  have hdescent : baseEnd_884073 < baseStart_884073 := by decide
  rcases family_descends (prefixWord ++ tailWord_884073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884076 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_884076 : Nat := 118140960795 + 884076 * 2 ^ 59
def prefixEnd_884076 : Nat := 4983230072969 + 3 ^ 40 * 884076 * 2
def baseEnd_884076 : Nat := 403516376092789584252635

theorem tailTrace_884076 : CollatzResearch.WordTrace tailWord_884076 prefixEnd_884076 403516376092789584252635 := by
  unfold tailWord_884076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16122450372575557502564041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21496600496767410003418721 16122450372575557502564041)
  ·
    refine ⟨12091837779431668126923031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16122450372575557502564041 12091837779431668126923031)
    ·
      refine ⟨18137756669147502190384547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12091837779431668126923031 18137756669147502190384547)
      ·
        refine ⟨27206635003721253285576821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18137756669147502190384547 27206635003721253285576821)
        ·
          refine ⟨2550622031598867495522827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27206635003721253285576821 2550622031598867495522827)
          ·
            refine ⟨3825933047398301243284241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550622031598867495522827 3825933047398301243284241)
            ·
              refine ⟨2869449785548725932463181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825933047398301243284241 2869449785548725932463181)
              ·
                refine ⟨1076043669580772224673693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869449785548725932463181 1076043669580772224673693)
                ·
                  refine ⟨403516376092789584252635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076043669580772224673693 403516376092789584252635)
                  ·
                    rfl

theorem cell20_884076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_884076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884076 prefixEnd_884076 := by exact prefixLift 884076
  have htrace : WordTrace (prefixWord ++ tailWord_884076) baseStart_884076 baseEnd_884076 := by
    simpa [prefixWord, tailWord_884076, baseEnd_884076] using wordTrace_append hprefix tailTrace_884076
  have hstable : (prefixWord ++ tailWord_884076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884076).length < 2 ^ (prefixWord ++ tailWord_884076).sum := by decide
  have hdescent : baseEnd_884076 < baseStart_884076 := by decide
  rcases family_descends (prefixWord ++ tailWord_884076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884100 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_884100 : Nat := 118140960795 + 884100 * 2 ^ 59
def prefixEnd_884100 : Nat := 4983230072969 + 3 ^ 40 * 884100 * 2
def baseEnd_884100 : Nat := 403527330346752167452537

theorem tailTrace_884100 : CollatzResearch.WordTrace tailWord_884100 prefixEnd_884100 403527330346752167452537 := by
  unfold tailWord_884100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16122888048532083552000877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21497184064709444736001169 16122888048532083552000877)
  ·
    refine ⟨6046083018199531332000329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16122888048532083552000877 6046083018199531332000329)
    ·
      refine ⟨4534562263649648499000247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6046083018199531332000329 4534562263649648499000247)
      ·
        refine ⟨6801843395474472748500371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534562263649648499000247 6801843395474472748500371)
        ·
          refine ⟨10202765093211709122750557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801843395474472748500371 10202765093211709122750557)
          ·
            refine ⟨3826036909954390921031459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10202765093211709122750557 3826036909954390921031459)
            ·
              refine ⟨5739055364931586381547189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826036909954390921031459 5739055364931586381547189)
              ·
                refine ⟨538036440462336223270049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5739055364931586381547189 538036440462336223270049)
                ·
                  refine ⟨403527330346752167452537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538036440462336223270049 403527330346752167452537)
                  ·
                    rfl

theorem cell20_884100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_884100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884100 prefixEnd_884100 := by exact prefixLift 884100
  have htrace : WordTrace (prefixWord ++ tailWord_884100) baseStart_884100 baseEnd_884100 := by
    simpa [prefixWord, tailWord_884100, baseEnd_884100] using wordTrace_append hprefix tailTrace_884100
  have hstable : (prefixWord ++ tailWord_884100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884100).length < 2 ^ (prefixWord ++ tailWord_884100).sum := by decide
  have hdescent : baseEnd_884100 < baseStart_884100 := by decide
  rcases family_descends (prefixWord ++ tailWord_884100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884110 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_884110 : Nat := 118140960795 + 884110 * 2 ^ 59
def prefixEnd_884110 : Nat := 4983230072969 + 3 ^ 40 * 884110 * 2
def baseEnd_884110 : Nat := 403531894619236577119163

theorem tailTrace_884110 : CollatzResearch.WordTrace tailWord_884110 prefixEnd_884110 403531894619236577119163 := by
  unfold tailWord_884110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030767603378492351483223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21497427218018625874577189 4030767603378492351483223)
  ·
    refine ⟨6046151405067738527224835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030767603378492351483223 6046151405067738527224835)
    ·
      refine ⟨9069227107601607790837253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046151405067738527224835 9069227107601607790837253)
      ·
        refine ⟨1700480082675301460781985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9069227107601607790837253 1700480082675301460781985)
        ·
          refine ⟨1275360062006476095586489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700480082675301460781985 1275360062006476095586489)
          ·
            refine ⟨956520046504857071689867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275360062006476095586489 956520046504857071689867)
            ·
              refine ⟨1434780069757285607534801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956520046504857071689867 1434780069757285607534801)
              ·
                refine ⟨1076085052317964205651101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434780069757285607534801 1076085052317964205651101)
                ·
                  refine ⟨403531894619236577119163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076085052317964205651101 403531894619236577119163)
                  ·
                    rfl

theorem cell20_884110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_884110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884110 prefixEnd_884110 := by exact prefixLift 884110
  have htrace : WordTrace (prefixWord ++ tailWord_884110) baseStart_884110 baseEnd_884110 := by
    simpa [prefixWord, tailWord_884110, baseEnd_884110] using wordTrace_append hprefix tailTrace_884110
  have hstable : (prefixWord ++ tailWord_884110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884110).length < 2 ^ (prefixWord ++ tailWord_884110).sum := by decide
  have hdescent : baseEnd_884110 < baseStart_884110 := by decide
  rcases family_descends (prefixWord ++ tailWord_884110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884121 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_884121 : Nat := 118140960795 + 884121 * 2 ^ 59
def prefixEnd_884121 : Nat := 4983230072969 + 3 ^ 40 * 884121 * 2
def baseEnd_884121 : Nat := 403536915318969427752451

theorem tailTrace_884121 : CollatzResearch.WordTrace tailWord_884121 prefixEnd_884121 403536915318969427752451 := by
  unfold tailWord_884121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32246542029988087690516217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21497694686658725127010811 32246542029988087690516217)
  ·
    refine ⟨24184906522491065767887163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32246542029988087690516217 24184906522491065767887163)
    ·
      refine ⟨36277359783736598651830745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24184906522491065767887163 36277359783736598651830745)
      ·
        refine ⟨27208019837802448988873059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36277359783736598651830745 27208019837802448988873059)
        ·
          refine ⟨40812029756703673483309589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27208019837802448988873059 40812029756703673483309589)
          ·
            refine ⟨1913063894845484694530137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40812029756703673483309589 1913063894845484694530137)
            ·
              refine ⟨1434797921134113520897603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913063894845484694530137 1434797921134113520897603)
              ·
                refine ⟨2152196881701170281346405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434797921134113520897603 2152196881701170281346405)
                ·
                  refine ⟨403536915318969427752451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152196881701170281346405 403536915318969427752451)
                  ·
                    rfl

theorem cell20_884121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_884121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884121 prefixEnd_884121 := by exact prefixLift 884121
  have htrace : WordTrace (prefixWord ++ tailWord_884121) baseStart_884121 baseEnd_884121 := by
    simpa [prefixWord, tailWord_884121, baseEnd_884121] using wordTrace_append hprefix tailTrace_884121
  have hstable : (prefixWord ++ tailWord_884121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884121).length < 2 ^ (prefixWord ++ tailWord_884121).sum := by decide
  have hdescent : baseEnd_884121 < baseStart_884121 := by decide
  rcases family_descends (prefixWord ++ tailWord_884121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884225 : List Nat := [1, 2, 4, 1, 12]
def baseStart_884225 : Nat := 118140960795 + 884225 * 2 ^ 59
def prefixEnd_884225 : Nat := 4983230072969 + 3 ^ 40 * 884225 * 2
def baseEnd_884225 : Nat := 4982523256207497386239

theorem tailTrace_884225 : CollatzResearch.WordTrace tailWord_884225 prefixEnd_884225 4982523256207497386239 := by
  unfold tailWord_884225
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250335221611313452302129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21500223481074208968201419 32250335221611313452302129)
  ·
    refine ⟨24187751416208485089226597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32250335221611313452302129 24187751416208485089226597)
    ·
      refine ⟨4535203390539090954229987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24187751416208485089226597 4535203390539090954229987)
      ·
        refine ⟨6802805085808636431344981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4535203390539090954229987 6802805085808636431344981)
        ·
          refine ⟨4982523256207497386239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6802805085808636431344981 4982523256207497386239)
          ·
            rfl

theorem cell20_884225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 12].length) (baseStart_884225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884225 prefixEnd_884225 := by exact prefixLift 884225
  have htrace : WordTrace (prefixWord ++ tailWord_884225) baseStart_884225 baseEnd_884225 := by
    simpa [prefixWord, tailWord_884225, baseEnd_884225] using wordTrace_append hprefix tailTrace_884225
  have hstable : (prefixWord ++ tailWord_884225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884225).length < 2 ^ (prefixWord ++ tailWord_884225).sum := by decide
  have hdescent : baseEnd_884225 < baseStart_884225 := by decide
  rcases family_descends (prefixWord ++ tailWord_884225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884231 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 2]
def baseStart_884231 : Nat := 118140960795 + 884231 * 2 ^ 59
def prefixEnd_884231 : Nat := 4983230072969 + 3 ^ 40 * 884231 * 2
def baseEnd_884231 : Nat := 403587122316297934085335

theorem tailTrace_884231 : CollatzResearch.WordTrace tailWord_884231 prefixEnd_884231 403587122316297934085335 := by
  unfold tailWord_884231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250554059589576477020547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21500369373059717651347031 32250554059589576477020547)
  ·
    refine ⟨48375831089384364715530821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32250554059589576477020547 48375831089384364715530821)
    ·
      refine ⟨9070468329259568384162029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48375831089384364715530821 9070468329259568384162029)
      ·
        refine ⟨3401425623472338144060761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9070468329259568384162029 3401425623472338144060761)
        ·
          refine ⟨2551069217604253608045571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401425623472338144060761 2551069217604253608045571)
          ·
            refine ⟨3826603826406380412068357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551069217604253608045571 3826603826406380412068357)
            ·
              refine ⟨717488217451196327262817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3826603826406380412068357 717488217451196327262817)
              ·
                refine ⟨538116163088397245447113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717488217451196327262817 538116163088397245447113)
                ·
                  refine ⟨403587122316297934085335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538116163088397245447113 403587122316297934085335)
                  ·
                    rfl

theorem cell20_884231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2].length) (baseStart_884231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884231 prefixEnd_884231 := by exact prefixLift 884231
  have htrace : WordTrace (prefixWord ++ tailWord_884231) baseStart_884231 baseEnd_884231 := by
    simpa [prefixWord, tailWord_884231, baseEnd_884231] using wordTrace_append hprefix tailTrace_884231
  have hstable : (prefixWord ++ tailWord_884231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884231).length < 2 ^ (prefixWord ++ tailWord_884231).sum := by decide
  have hdescent : baseEnd_884231 < baseStart_884231 := by decide
  rcases family_descends (prefixWord ++ tailWord_884231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884238 : List Nat := [4, 1, 1, 2, 5, 1, 1, 5]
def baseStart_884238 : Nat := 118140960795 + 884238 * 2 ^ 59
def prefixEnd_884238 : Nat := 4983230072969 + 3 ^ 40 * 884238 * 2
def baseEnd_884238 : Nat := 134530105769012340283991

theorem tailTrace_884238 : CollatzResearch.WordTrace tailWord_884238 prefixEnd_884238 134530105769012340283991 := by
  unfold tailWord_884238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4031351171320527084065671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21500539580376144448350245 4031351171320527084065671)
  ·
    refine ⟨6047026756980790626098507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4031351171320527084065671 6047026756980790626098507)
    ·
      refine ⟨9070540135471185939147761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047026756980790626098507 9070540135471185939147761)
      ·
        refine ⟨6802905101603389454360821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9070540135471185939147761 6802905101603389454360821)
        ·
          refine ⟨637772353275317761346327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6802905101603389454360821 637772353275317761346327)
          ·
            refine ⟨956658529912976642019491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637772353275317761346327 956658529912976642019491)
            ·
              refine ⟨1434987794869464963029237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956658529912976642019491 1434987794869464963029237)
              ·
                refine ⟨134530105769012340283991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434987794869464963029237 134530105769012340283991)
                ·
                  rfl

theorem cell20_884238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_884238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884238 prefixEnd_884238 := by exact prefixLift 884238
  have htrace : WordTrace (prefixWord ++ tailWord_884238) baseStart_884238 baseEnd_884238 := by
    simpa [prefixWord, tailWord_884238, baseEnd_884238] using wordTrace_append hprefix tailTrace_884238
  have hstable : (prefixWord ++ tailWord_884238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884238).length < 2 ^ (prefixWord ++ tailWord_884238).sum := by decide
  have hdescent : baseEnd_884238 < baseStart_884238 := by decide
  rcases family_descends (prefixWord ++ tailWord_884238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884259 : List Nat := [1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_884259 : Nat := 118140960795 + 884259 * 2 ^ 59
def prefixEnd_884259 : Nat := 4983230072969 + 3 ^ 40 * 884259 * 2
def baseEnd_884259 : Nat := 134533300759751427050629

theorem tailTrace_884259 : CollatzResearch.WordTrace tailWord_884259 prefixEnd_884259 134533300759751427050629 := by
  unfold tailWord_884259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32251575303488137259039831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21501050202325424839359887 32251575303488137259039831)
  ·
    refine ⟨48377362955232205888559747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32251575303488137259039831 48377362955232205888559747)
    ·
      refine ⟨72566044432848308832839621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48377362955232205888559747 72566044432848308832839621)
      ·
        refine ⟨13606133331159057906157429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72566044432848308832839621 13606133331159057906157429)
        ·
          refine ⟨1275574999796161678702259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13606133331159057906157429 1275574999796161678702259)
          ·
            refine ⟨1913362499694242518053389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275574999796161678702259 1913362499694242518053389)
            ·
              refine ⟨717510937385340944270021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913362499694242518053389 717510937385340944270021)
              ·
                refine ⟨134533300759751427050629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717510937385340944270021 134533300759751427050629)
                ·
                  rfl

theorem cell20_884259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_884259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884259 prefixEnd_884259 := by exact prefixLift 884259
  have htrace : WordTrace (prefixWord ++ tailWord_884259) baseStart_884259 baseEnd_884259 := by
    simpa [prefixWord, tailWord_884259, baseEnd_884259] using wordTrace_append hprefix tailTrace_884259
  have hstable : (prefixWord ++ tailWord_884259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884259).length < 2 ^ (prefixWord ++ tailWord_884259).sum := by decide
  have hdescent : baseEnd_884259 < baseStart_884259 := by decide
  rcases family_descends (prefixWord ++ tailWord_884259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884287 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_884287 : Nat := 118140960795 + 884287 * 2 ^ 59
def prefixEnd_884287 : Nat := 4983230072969 + 3 ^ 40 * 884287 * 2
def baseEnd_884287 : Nat := 403612682242210628218439

theorem tailTrace_884287 : CollatzResearch.WordTrace tailWord_884287 prefixEnd_884287 403612682242210628218439 := by
  unfold tailWord_884287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252596547386698041059115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21501731031591132027372743 32252596547386698041059115)
  ·
    refine ⟨48378894821080047061588673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32252596547386698041059115 48378894821080047061588673)
    ·
      refine ⟨36284171115810035296191505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48378894821080047061588673 36284171115810035296191505)
      ·
        refine ⟨27213128336857526472143629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36284171115810035296191505 27213128336857526472143629)
        ·
          refine ⟨10204923126321572427053861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27213128336857526472143629 10204923126321572427053861)
          ·
            refine ⟨1913423086185294830072599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10204923126321572427053861 1913423086185294830072599)
            ·
              refine ⟨2870134629277942245108899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913423086185294830072599 2870134629277942245108899)
              ·
                refine ⟨4305201943916913367663349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870134629277942245108899 4305201943916913367663349)
                ·
                  refine ⟨403612682242210628218439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305201943916913367663349 403612682242210628218439)
                  ·
                    rfl

theorem cell20_884287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_884287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884287 prefixEnd_884287 := by exact prefixLift 884287
  have htrace : WordTrace (prefixWord ++ tailWord_884287) baseStart_884287 baseEnd_884287 := by
    simpa [prefixWord, tailWord_884287, baseEnd_884287] using wordTrace_append hprefix tailTrace_884287
  have hstable : (prefixWord ++ tailWord_884287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884287).length < 2 ^ (prefixWord ++ tailWord_884287).sum := by decide
  have hdescent : baseEnd_884287 < baseStart_884287 := by decide
  rcases family_descends (prefixWord ++ tailWord_884287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884304 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_884304 : Nat := 118140960795 + 884304 * 2 ^ 59
def prefixEnd_884304 : Nat := 4983230072969 + 3 ^ 40 * 884304 * 2
def baseEnd_884304 : Nat := 403620441505434124651703

theorem tailTrace_884304 : CollatzResearch.WordTrace tailWord_884304 prefixEnd_884304 403620441505434124651703 := by
  unfold tailWord_884304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126608294162554972213983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21502144392216739962951977 16126608294162554972213983)
  ·
    refine ⟨24189912441243832458320975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16126608294162554972213983 24189912441243832458320975)
    ·
      refine ⟨36284868661865748687481463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24189912441243832458320975 36284868661865748687481463)
      ·
        refine ⟨54427302992798623031222195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36284868661865748687481463 54427302992798623031222195)
        ·
          refine ⟨81640954489197934546833293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54427302992798623031222195 81640954489197934546833293)
          ·
            refine ⟨30615357933449225455062485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81640954489197934546833293 30615357933449225455062485)
            ·
              refine ⟨717547451565216221603027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30615357933449225455062485 717547451565216221603027)
              ·
                refine ⟨1076321177347824332404541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717547451565216221603027 1076321177347824332404541)
                ·
                  refine ⟨403620441505434124651703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076321177347824332404541 403620441505434124651703)
                  ·
                    rfl

theorem cell20_884304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_884304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884304 prefixEnd_884304 := by exact prefixLift 884304
  have htrace : WordTrace (prefixWord ++ tailWord_884304) baseStart_884304 baseEnd_884304 := by
    simpa [prefixWord, tailWord_884304, baseEnd_884304] using wordTrace_append hprefix tailTrace_884304
  have hstable : (prefixWord ++ tailWord_884304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884304).length < 2 ^ (prefixWord ++ tailWord_884304).sum := by decide
  have hdescent : baseEnd_884304 < baseStart_884304 := by decide
  rcases family_descends (prefixWord ++ tailWord_884304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884310 : List Nat := [5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_884310 : Nat := 118140960795 + 884310 * 2 ^ 59
def prefixEnd_884310 : Nat := 4983230072969 + 3 ^ 40 * 884310 * 2
def baseEnd_884310 : Nat := 134541060022974923483893

theorem tailTrace_884310 : CollatzResearch.WordTrace tailWord_884310 prefixEnd_884310 134541060022974923483893 := by
  unfold tailWord_884310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015839714143960810571649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21502290284202248646097589 2015839714143960810571649)
  ·
    refine ⟨1511879785607970607928737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2015839714143960810571649 1511879785607970607928737)
    ·
      refine ⟨1133909839205977955946553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1511879785607970607928737 1133909839205977955946553)
      ·
        refine ⟨850432379404483466959915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133909839205977955946553 850432379404483466959915)
        ·
          refine ⟨1275648569106725200439873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850432379404483466959915 1275648569106725200439873)
          ·
            refine ⟨956736426830043900329905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275648569106725200439873 956736426830043900329905)
            ·
              refine ⟨717552320122532925247429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956736426830043900329905 717552320122532925247429)
              ·
                refine ⟨134541060022974923483893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717552320122532925247429 134541060022974923483893)
                ·
                  rfl

theorem cell20_884310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_884310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884310 prefixEnd_884310 := by exact prefixLift 884310
  have htrace : WordTrace (prefixWord ++ tailWord_884310) baseStart_884310 baseEnd_884310 := by
    simpa [prefixWord, tailWord_884310, baseEnd_884310] using wordTrace_append hprefix tailTrace_884310
  have hstable : (prefixWord ++ tailWord_884310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884310).length < 2 ^ (prefixWord ++ tailWord_884310).sum := by decide
  have hdescent : baseEnd_884310 < baseStart_884310 := by decide
  rcases family_descends (prefixWord ++ tailWord_884310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884325 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_884325 : Nat := 118140960795 + 884325 * 2 ^ 59
def prefixEnd_884325 : Nat := 4983230072969 + 3 ^ 40 * 884325 * 2
def baseEnd_884325 : Nat := 403630026477651384951617

theorem tailTrace_884325 : CollatzResearch.WordTrace tailWord_884325 prefixEnd_884325 403630026477651384951617 := by
  unfold tailWord_884325
  simp only [CollatzResearch.WordTrace]
  refine ⟨32253982521249030530942429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21502655014166020353961619 32253982521249030530942429)
  ·
    refine ⟨12095243445468386449103411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32253982521249030530942429 12095243445468386449103411)
    ·
      refine ⟨18142865168202579673655117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12095243445468386449103411 18142865168202579673655117)
      ·
        refine ⟨6803574438075967377620669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18142865168202579673655117 6803574438075967377620669)
        ·
          refine ⟨2551340414278487766607751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6803574438075967377620669 2551340414278487766607751)
          ·
            refine ⟨3827010621417731649911627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551340414278487766607751 3827010621417731649911627)
            ·
              refine ⟨5740515932126597474867441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827010621417731649911627 5740515932126597474867441)
              ·
                refine ⟨4305386949094948106150581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740515932126597474867441 4305386949094948106150581)
                ·
                  refine ⟨403630026477651384951617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305386949094948106150581 403630026477651384951617)
                  ·
                    rfl

theorem cell20_884325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_884325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884325 prefixEnd_884325 := by exact prefixLift 884325
  have htrace : WordTrace (prefixWord ++ tailWord_884325) baseStart_884325 baseEnd_884325 := by
    simpa [prefixWord, tailWord_884325, baseEnd_884325] using wordTrace_append hprefix tailTrace_884325
  have hstable : (prefixWord ++ tailWord_884325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884325).length < 2 ^ (prefixWord ++ tailWord_884325).sum := by decide
  have hdescent : baseEnd_884325 < baseStart_884325 := by decide
  rcases family_descends (prefixWord ++ tailWord_884325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884342 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_884342 : Nat := 118140960795 + 884342 * 2 ^ 59
def prefixEnd_884342 : Nat := 4983230072969 + 3 ^ 40 * 884342 * 2
def baseEnd_884342 : Nat := 403637785740874881384881

theorem tailTrace_884342 : CollatzResearch.WordTrace tailWord_884342 prefixEnd_884342 403637785740874881384881 := by
  unfold tailWord_884342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015912660136715152144455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21503068374791628289540853 2015912660136715152144455)
  ·
    refine ⟨3023868990205072728216683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015912660136715152144455 3023868990205072728216683)
    ·
      refine ⟨4535803485307609092325025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023868990205072728216683 4535803485307609092325025)
      ·
        refine ⟨3401852613980706819243769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535803485307609092325025 3401852613980706819243769)
        ·
          refine ⟨2551389460485530114432827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401852613980706819243769 2551389460485530114432827)
          ·
            refine ⟨3827084190728295171649241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551389460485530114432827 3827084190728295171649241)
            ·
              refine ⟨2870313143046221378736931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3827084190728295171649241 2870313143046221378736931)
              ·
                refine ⟨4305469714569332068105397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870313143046221378736931 4305469714569332068105397)
                ·
                  refine ⟨403637785740874881384881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4305469714569332068105397 403637785740874881384881)
                  ·
                    rfl

theorem cell20_884342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_884342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884342 prefixEnd_884342 := by exact prefixLift 884342
  have htrace : WordTrace (prefixWord ++ tailWord_884342) baseStart_884342 baseEnd_884342 := by
    simpa [prefixWord, tailWord_884342, baseEnd_884342] using wordTrace_append hprefix tailTrace_884342
  have hstable : (prefixWord ++ tailWord_884342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884342).length < 2 ^ (prefixWord ++ tailWord_884342).sum := by decide
  have hdescent : baseEnd_884342 < baseStart_884342 := by decide
  rcases family_descends (prefixWord ++ tailWord_884342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884349 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_884349 : Nat := 118140960795 + 884349 * 2 ^ 59
def prefixEnd_884349 : Nat := 4983230072969 + 3 ^ 40 * 884349 * 2
def baseEnd_884349 : Nat := 403640980731613968151519

theorem tailTrace_884349 : CollatzResearch.WordTrace tailWord_884349 prefixEnd_884349 403640980731613968151519 := by
  unfold tailWord_884349
  simp only [CollatzResearch.WordTrace]
  refine ⟨32254857873162082629816101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21503238582108055086544067 32254857873162082629816101)
  ·
    refine ⟨6047785851217890493090519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32254857873162082629816101 6047785851217890493090519)
    ·
      refine ⟨9071678776826835739635779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047785851217890493090519 9071678776826835739635779)
      ·
        refine ⟨13607518165240253609453669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071678776826835739635779 13607518165240253609453669)
        ·
          refine ⟨2551409655982547551772563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13607518165240253609453669 2551409655982547551772563)
          ·
            refine ⟨3827114483973821327658845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551409655982547551772563 3827114483973821327658845)
            ·
              refine ⟨1435167931490182997872067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3827114483973821327658845 1435167931490182997872067)
              ·
                refine ⟨2152751897235274496808101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435167931490182997872067 2152751897235274496808101)
                ·
                  refine ⟨403640980731613968151519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152751897235274496808101 403640980731613968151519)
                  ·
                    rfl

theorem cell20_884349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_884349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884349 prefixEnd_884349 := by exact prefixLift 884349
  have htrace : WordTrace (prefixWord ++ tailWord_884349) baseStart_884349 baseEnd_884349 := by
    simpa [prefixWord, tailWord_884349, baseEnd_884349] using wordTrace_append hprefix tailTrace_884349
  have hstable : (prefixWord ++ tailWord_884349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884349).length < 2 ^ (prefixWord ++ tailWord_884349).sum := by decide
  have hdescent : baseEnd_884349 < baseStart_884349 := by decide
  rcases family_descends (prefixWord ++ tailWord_884349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884359 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 3]
def baseStart_884359 : Nat := 118140960795 + 884359 * 2 ^ 59
def prefixEnd_884359 : Nat := 4983230072969 + 3 ^ 40 * 884359 * 2
def baseEnd_884359 : Nat := 403645545004098377818145

theorem tailTrace_884359 : CollatzResearch.WordTrace tailWord_884359 prefixEnd_884359 403645545004098377818145 := by
  unfold tailWord_884359
  simp only [CollatzResearch.WordTrace]
  refine ⟨32255222603125854337680131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21503481735417236225120087 32255222603125854337680131)
  ·
    refine ⟨48382833904688781506520197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32255222603125854337680131 48382833904688781506520197)
    ·
      refine ⟨9071781357129146532472537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48382833904688781506520197 9071781357129146532472537)
      ·
        refine ⟨6803836017846859899354403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9071781357129146532472537 6803836017846859899354403)
        ·
          refine ⟨10205754026770289849031605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803836017846859899354403 10205754026770289849031605)
          ·
            refine ⟨956789440009714673346713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10205754026770289849031605 956789440009714673346713)
            ·
              refine ⟨717592080007286005010035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956789440009714673346713 717592080007286005010035)
              ·
                refine ⟨1076388120010929007515053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717592080007286005010035 1076388120010929007515053)
                ·
                  refine ⟨403645545004098377818145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076388120010929007515053 403645545004098377818145)
                  ·
                    rfl

theorem cell20_884359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_884359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884359 prefixEnd_884359 := by exact prefixLift 884359
  have htrace : WordTrace (prefixWord ++ tailWord_884359) baseStart_884359 baseEnd_884359 := by
    simpa [prefixWord, tailWord_884359, baseEnd_884359] using wordTrace_append hprefix tailTrace_884359
  have hstable : (prefixWord ++ tailWord_884359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884359).length < 2 ^ (prefixWord ++ tailWord_884359).sum := by decide
  have hdescent : baseEnd_884359 < baseStart_884359 := by decide
  rcases family_descends (prefixWord ++ tailWord_884359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884363 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_884363 : Nat := 118140960795 + 884363 * 2 ^ 59
def prefixEnd_884363 : Nat := 4983230072969 + 3 ^ 40 * 884363 * 2
def baseEnd_884363 : Nat := 403647370713092141684795

theorem tailTrace_884363 : CollatzResearch.WordTrace tailWord_884363 prefixEnd_884363 403647370713092141684795 := by
  unfold tailWord_884363
  simp only [CollatzResearch.WordTrace]
  refine ⟨32255368495111363020825743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21503578996740908680550495 32255368495111363020825743)
  ·
    refine ⟨48383052742667044531238615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32255368495111363020825743 48383052742667044531238615)
    ·
      refine ⟨72574579114000566796857923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48383052742667044531238615 72574579114000566796857923)
      ·
        refine ⟨108861868671000850195286885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72574579114000566796857923 108861868671000850195286885)
        ·
          refine ⟨20411600375812659411616291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108861868671000850195286885 20411600375812659411616291)
          ·
            refine ⟨30617400563718989117424437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20411600375812659411616291 30617400563718989117424437)
            ·
              refine ⟨2870381302848655229758541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30617400563718989117424437 2870381302848655229758541)
              ·
                refine ⟨1076392988568245711159453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2870381302848655229758541 1076392988568245711159453)
                ·
                  refine ⟨403647370713092141684795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076392988568245711159453 403647370713092141684795)
                  ·
                    rfl

theorem cell20_884363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_884363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884363 prefixEnd_884363 := by exact prefixLift 884363
  have htrace : WordTrace (prefixWord ++ tailWord_884363) baseStart_884363 baseEnd_884363 := by
    simpa [prefixWord, tailWord_884363, baseEnd_884363] using wordTrace_append hprefix tailTrace_884363
  have hstable : (prefixWord ++ tailWord_884363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884363).length < 2 ^ (prefixWord ++ tailWord_884363).sum := by decide
  have hdescent : baseEnd_884363 < baseStart_884363 := by decide
  rcases family_descends (prefixWord ++ tailWord_884363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884387 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 2]
def baseStart_884387 : Nat := 118140960795 + 884387 * 2 ^ 59
def prefixEnd_884387 : Nat := 4983230072969 + 3 ^ 40 * 884387 * 2
def baseEnd_884387 : Nat := 403658324967054724884697

theorem tailTrace_884387 : CollatzResearch.WordTrace tailWord_884387 prefixEnd_884387 403658324967054724884697 := by
  unfold tailWord_884387
  simp only [CollatzResearch.WordTrace]
  refine ⟨32256243847024415119699415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21504162564682943413132943 32256243847024415119699415)
  ·
    refine ⟨48384365770536622679549123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32256243847024415119699415 48384365770536622679549123)
    ·
      refine ⟨72576548655804934019323685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48384365770536622679549123 72576548655804934019323685)
      ·
        refine ⟨13608102872963425128623191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72576548655804934019323685 13608102872963425128623191)
        ·
          refine ⟨20412154309445137692934787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13608102872963425128623191 20412154309445137692934787)
          ·
            refine ⟨30618231464167706539402181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20412154309445137692934787 30618231464167706539402181)
            ·
              refine ⟨5740918399531444976137909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30618231464167706539402181 5740918399531444976137909)
              ·
                refine ⟨538211099956072966512929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5740918399531444976137909 538211099956072966512929)
                ·
                  refine ⟨403658324967054724884697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538211099956072966512929 403658324967054724884697)
                  ·
                    rfl

theorem cell20_884387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2].length) (baseStart_884387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884387 prefixEnd_884387 := by exact prefixLift 884387
  have htrace : WordTrace (prefixWord ++ tailWord_884387) baseStart_884387 baseEnd_884387 := by
    simpa [prefixWord, tailWord_884387, baseEnd_884387] using wordTrace_append hprefix tailTrace_884387
  have hstable : (prefixWord ++ tailWord_884387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884387).length < 2 ^ (prefixWord ++ tailWord_884387).sum := by decide
  have hdescent : baseEnd_884387 < baseStart_884387 := by decide
  rcases family_descends (prefixWord ++ tailWord_884387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884442 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_884442 : Nat := 118140960795 + 884442 * 2 ^ 59
def prefixEnd_884442 : Nat := 4983230072969 + 3 ^ 40 * 884442 * 2
def baseEnd_884442 : Nat := 403683428465718978051139

theorem tailTrace_884442 : CollatzResearch.WordTrace tailWord_884442 prefixEnd_884442 403683428465718978051139 := by
  unfold tailWord_884442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064562465456289878237895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21505499907883439675301053 8064562465456289878237895)
  ·
    refine ⟨12096843698184434817356843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8064562465456289878237895 12096843698184434817356843)
    ·
      refine ⟨18145265547276652226035265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12096843698184434817356843 18145265547276652226035265)
      ·
        refine ⟨13608949160457489169526449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18145265547276652226035265 13608949160457489169526449)
        ·
          refine ⟨10206711870343116877144837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13608949160457489169526449 10206711870343116877144837)
          ·
            refine ⟨1913758475689334414464657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10206711870343116877144837 1913758475689334414464657)
            ·
              refine ⟨1435318856767000810848493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913758475689334414464657 1435318856767000810848493)
              ·
                refine ⟨538244571287625304068185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1435318856767000810848493 538244571287625304068185)
                ·
                  refine ⟨403683428465718978051139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538244571287625304068185 403683428465718978051139)
                  ·
                    rfl

theorem cell20_884442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_884442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884442 prefixEnd_884442 := by exact prefixLift 884442
  have htrace : WordTrace (prefixWord ++ tailWord_884442) baseStart_884442 baseEnd_884442 := by
    simpa [prefixWord, tailWord_884442, baseEnd_884442] using wordTrace_append hprefix tailTrace_884442
  have hstable : (prefixWord ++ tailWord_884442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884442).length < 2 ^ (prefixWord ++ tailWord_884442).sum := by decide
  have hdescent : baseEnd_884442 < baseStart_884442 := by decide
  rcases family_descends (prefixWord ++ tailWord_884442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884453 : List Nat := [1, 3, 1, 4, 1, 1, 9]
def baseStart_884453 : Nat := 118140960795 + 884453 * 2 ^ 59
def prefixEnd_884453 : Nat := 4983230072969 + 3 ^ 40 * 884453 * 2
def baseEnd_884453 : Nat := 44854272129494647631603

theorem tailTrace_884453 : CollatzResearch.WordTrace tailWord_884453 prefixEnd_884453 44854272129494647631603 := by
  unfold tailWord_884453
  simp only [CollatzResearch.WordTrace]
  refine ⟨32258651064785308391602013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21505767376523538927734675 32258651064785308391602013)
  ·
    refine ⟨12096994149294490646850755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32258651064785308391602013 12096994149294490646850755)
    ·
      refine ⟨18145491223941735970276133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12096994149294490646850755 18145491223941735970276133)
      ·
        refine ⟨3402279604489075494426775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18145491223941735970276133 3402279604489075494426775)
        ·
          refine ⟨5103419406733613241640163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402279604489075494426775 5103419406733613241640163)
          ·
            refine ⟨7655129110100419862460245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103419406733613241640163 7655129110100419862460245)
            ·
              refine ⟨44854272129494647631603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7655129110100419862460245 44854272129494647631603)
              ·
                rfl

theorem cell20_884453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_884453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884453 prefixEnd_884453 := by exact prefixLift 884453
  have htrace : WordTrace (prefixWord ++ tailWord_884453) baseStart_884453 baseEnd_884453 := by
    simpa [prefixWord, tailWord_884453, baseEnd_884453] using wordTrace_append hprefix tailTrace_884453
  have hstable : (prefixWord ++ tailWord_884453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884453).length < 2 ^ (prefixWord ++ tailWord_884453).sum := by decide
  have hdescent : baseEnd_884453 < baseStart_884453 := by decide
  rcases family_descends (prefixWord ++ tailWord_884453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884456 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_884456 : Nat := 118140960795 + 884456 * 2 ^ 59
def prefixEnd_884456 : Nat := 4983230072969 + 3 ^ 40 * 884456 * 2
def baseEnd_884456 : Nat := 403689818447197151584415

theorem tailTrace_884456 : CollatzResearch.WordTrace tailWord_884456 prefixEnd_884456 403689818447197151584415 := by
  unfold tailWord_884456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16129380241887219951980611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21505840322516293269307481 16129380241887219951980611)
  ·
    refine ⟨24194070362830829927970917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16129380241887219951980611 24194070362830829927970917)
    ·
      refine ⟨4536388193030780611494547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24194070362830829927970917 4536388193030780611494547)
      ·
        refine ⟨6804582289546170917241821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536388193030780611494547 6804582289546170917241821)
        ·
          refine ⟨2551718358579814093965683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6804582289546170917241821 2551718358579814093965683)
          ·
            refine ⟨3827577537869721140948525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551718358579814093965683 3827577537869721140948525)
            ·
              refine ⟨1435341576701145427855697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3827577537869721140948525 1435341576701145427855697)
              ·
                refine ⟨1076506182525859070891773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435341576701145427855697 1076506182525859070891773)
                ·
                  refine ⟨403689818447197151584415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076506182525859070891773 403689818447197151584415)
                  ·
                    rfl

theorem cell20_884456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_884456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884456 prefixEnd_884456 := by exact prefixLift 884456
  have htrace : WordTrace (prefixWord ++ tailWord_884456) baseStart_884456 baseEnd_884456 := by
    simpa [prefixWord, tailWord_884456, baseEnd_884456] using wordTrace_append hprefix tailTrace_884456
  have hstable : (prefixWord ++ tailWord_884456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884456).length < 2 ^ (prefixWord ++ tailWord_884456).sum := by decide
  have hdescent : baseEnd_884456 < baseStart_884456 := by decide
  rcases family_descends (prefixWord ++ tailWord_884456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884463 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 2]
def baseStart_884463 : Nat := 118140960795 + 884463 * 2 ^ 59
def prefixEnd_884463 : Nat := 4983230072969 + 3 ^ 40 * 884463 * 2
def baseEnd_884463 : Nat := 403693013437936238351053

theorem tailTrace_884463 : CollatzResearch.WordTrace tailWord_884463 prefixEnd_884463 403693013437936238351053 := by
  unfold tailWord_884463
  simp only [CollatzResearch.WordTrace]
  refine ⟨32259015794749080099466043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21506010529832720066310695 32259015794749080099466043)
  ·
    refine ⟨48388523692123620149199065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32259015794749080099466043 48388523692123620149199065)
    ·
      refine ⟨36291392769092715111899299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48388523692123620149199065 36291392769092715111899299)
      ·
        refine ⟨54437089153639072667848949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36291392769092715111899299 54437089153639072667848949)
        ·
          refine ⟨5103477108153663062610839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54437089153639072667848949 5103477108153663062610839)
          ·
            refine ⟨7655215662230494593916259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103477108153663062610839 7655215662230494593916259)
            ·
              refine ⟨11482823493345741890874389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655215662230494593916259 11482823493345741890874389)
              ·
                refine ⟨538257351250581651134737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11482823493345741890874389 538257351250581651134737)
                ·
                  refine ⟨403693013437936238351053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538257351250581651134737 403693013437936238351053)
                  ·
                    rfl

theorem cell20_884463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2].length) (baseStart_884463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884463 prefixEnd_884463 := by exact prefixLift 884463
  have htrace : WordTrace (prefixWord ++ tailWord_884463) baseStart_884463 baseEnd_884463 := by
    simpa [prefixWord, tailWord_884463, baseEnd_884463] using wordTrace_append hprefix tailTrace_884463
  have hstable : (prefixWord ++ tailWord_884463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884463).length < 2 ^ (prefixWord ++ tailWord_884463).sum := by decide
  have hdescent : baseEnd_884463 < baseStart_884463 := by decide
  rcases family_descends (prefixWord ++ tailWord_884463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884529 : List Nat := [1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_884529 : Nat := 118140960795 + 884529 * 2 ^ 59
def prefixEnd_884529 : Nat := 4983230072969 + 3 ^ 40 * 884529 * 2
def baseEnd_884529 : Nat := 134574379212111114050261

theorem tailTrace_884529 : CollatzResearch.WordTrace tailWord_884529 prefixEnd_884529 134574379212111114050261 := by
  unfold tailWord_884529
  simp only [CollatzResearch.WordTrace]
  refine ⟨32261423012509973371368641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21507615341673315580912427 32261423012509973371368641)
  ·
    refine ⟨24196067259382480028526481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32261423012509973371368641 24196067259382480028526481)
    ·
      refine ⟨18147050444536860021394861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24196067259382480028526481 18147050444536860021394861)
      ·
        refine ⟨6805143916701322508023073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18147050444536860021394861 6805143916701322508023073)
        ·
          refine ⟨5103857937525991881017305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6805143916701322508023073 5103857937525991881017305)
          ·
            refine ⟨3827893453144493910762979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5103857937525991881017305 3827893453144493910762979)
            ·
              refine ⟨5741840179716740866144469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827893453144493910762979 5741840179716740866144469)
              ·
                refine ⟨134574379212111114050261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5741840179716740866144469 134574379212111114050261)
                ·
                  rfl

theorem cell20_884529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_884529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884529 prefixEnd_884529 := by exact prefixLift 884529
  have htrace : WordTrace (prefixWord ++ tailWord_884529) baseStart_884529 baseEnd_884529 := by
    simpa [prefixWord, tailWord_884529, baseEnd_884529] using wordTrace_append hprefix tailTrace_884529
  have hstable : (prefixWord ++ tailWord_884529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884529).length < 2 ^ (prefixWord ++ tailWord_884529).sum := by decide
  have hdescent : baseEnd_884529 < baseStart_884529 := by decide
  rcases family_descends (prefixWord ++ tailWord_884529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884567 : List Nat := [1, 1, 3, 2, 5, 8]
def baseStart_884567 : Nat := 118140960795 + 884567 * 2 ^ 59
def prefixEnd_884567 : Nat := 4983230072969 + 3 ^ 40 * 884567 * 2
def baseEnd_884567 : Nat := 14953351180436077736443

theorem tailTrace_884567 : CollatzResearch.WordTrace tailWord_884567 prefixEnd_884567 14953351180436077736443 := by
  unfold tailWord_884567
  simp only [CollatzResearch.WordTrace]
  refine ⟨32262808986372305861251955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21508539324248203907501303 32262808986372305861251955)
  ·
    refine ⟨48394213479558458791877933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32262808986372305861251955 48394213479558458791877933)
    ·
      refine ⟨18147830054834422046954225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48394213479558458791877933 18147830054834422046954225)
      ·
        refine ⟨13610872541125816535215669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18147830054834422046954225 13610872541125816535215669)
        ·
          refine ⟨1276019300730545300176469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13610872541125816535215669 1276019300730545300176469)
          ·
            refine ⟨14953351180436077736443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1276019300730545300176469 14953351180436077736443)
            ·
              rfl

theorem cell20_884567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 8].length) (baseStart_884567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884567 prefixEnd_884567 := by exact prefixLift 884567
  have htrace : WordTrace (prefixWord ++ tailWord_884567) baseStart_884567 baseEnd_884567 := by
    simpa [prefixWord, tailWord_884567, baseEnd_884567] using wordTrace_append hprefix tailTrace_884567
  have hstable : (prefixWord ++ tailWord_884567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884567).length < 2 ^ (prefixWord ++ tailWord_884567).sum := by decide
  have hdescent : baseEnd_884567 < baseStart_884567 := by decide
  rcases family_descends (prefixWord ++ tailWord_884567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884577 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 2]
def baseStart_884577 : Nat := 118140960795 + 884577 * 2 ^ 59
def prefixEnd_884577 : Nat := 4983230072969 + 3 ^ 40 * 884577 * 2
def baseEnd_884577 : Nat := 403745046144258508550587

theorem tailTrace_884577 : CollatzResearch.WordTrace tailWord_884577 prefixEnd_884577 403745046144258508550587 := by
  unfold tailWord_884577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32263173716336077569115985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21508782477557385046077323 32263173716336077569115985)
  ·
    refine ⟨24197380287252058176836989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32263173716336077569115985 24197380287252058176836989)
    ·
      refine ⟨9074017607719521816313871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24197380287252058176836989 9074017607719521816313871)
      ·
        refine ⟨13611026411579282724470807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074017607719521816313871 13611026411579282724470807)
        ·
          refine ⟨20416539617368924086706211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13611026411579282724470807 20416539617368924086706211)
          ·
            refine ⟨30624809426053386130059317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20416539617368924086706211 30624809426053386130059317)
            ·
              refine ⟨2871075883692504949693061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30624809426053386130059317 2871075883692504949693061)
              ·
                refine ⟨538326728192344678067449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2871075883692504949693061 538326728192344678067449)
                ·
                  refine ⟨403745046144258508550587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538326728192344678067449 403745046144258508550587)
                  ·
                    rfl

theorem cell20_884577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_884577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884577 prefixEnd_884577 := by exact prefixLift 884577
  have htrace : WordTrace (prefixWord ++ tailWord_884577) baseStart_884577 baseEnd_884577 := by
    simpa [prefixWord, tailWord_884577, baseEnd_884577] using wordTrace_append hprefix tailTrace_884577
  have hstable : (prefixWord ++ tailWord_884577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884577).length < 2 ^ (prefixWord ++ tailWord_884577).sum := by decide
  have hdescent : baseEnd_884577 < baseStart_884577 := by decide
  rcases family_descends (prefixWord ++ tailWord_884577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884619 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_884619 : Nat := 118140960795 + 884619 * 2 ^ 59
def prefixEnd_884619 : Nat := 4983230072969 + 3 ^ 40 * 884619 * 2
def baseEnd_884619 : Nat := 403764216088693029150415

theorem tailTrace_884619 : CollatzResearch.WordTrace tailWord_884619 prefixEnd_884619 403764216088693029150415 := by
  unfold tailWord_884619
  simp only [CollatzResearch.WordTrace]
  refine ⟨32264705582183918742144911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21509803721455945828096607 32264705582183918742144911)
  ·
    refine ⟨48397058373275878113217367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32264705582183918742144911 48397058373275878113217367)
    ·
      refine ⟨72595587559913817169826051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48397058373275878113217367 72595587559913817169826051)
      ·
        refine ⟨108893381339870725754739077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72595587559913817169826051 108893381339870725754739077)
        ·
          refine ⟨20417509001225761079013577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108893381339870725754739077 20417509001225761079013577)
          ·
            refine ⟨15313131750919320809260183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20417509001225761079013577 15313131750919320809260183)
            ·
              refine ⟨22969697626378981213890275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313131750919320809260183 22969697626378981213890275)
              ·
                refine ⟨34454546439568471820835413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22969697626378981213890275 34454546439568471820835413)
                ·
                  refine ⟨403764216088693029150415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34454546439568471820835413 403764216088693029150415)
                  ·
                    rfl

theorem cell20_884619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_884619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884619 prefixEnd_884619 := by exact prefixLift 884619
  have htrace : WordTrace (prefixWord ++ tailWord_884619) baseStart_884619 baseEnd_884619 := by
    simpa [prefixWord, tailWord_884619, baseEnd_884619] using wordTrace_append hprefix tailTrace_884619
  have hstable : (prefixWord ++ tailWord_884619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884619).length < 2 ^ (prefixWord ++ tailWord_884619).sum := by decide
  have hdescent : baseEnd_884619 < baseStart_884619 := by decide
  rcases family_descends (prefixWord ++ tailWord_884619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884632 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_884632 : Nat := 118140960795 + 884632 * 2 ^ 59
def prefixEnd_884632 : Nat := 4983230072969 + 3 ^ 40 * 884632 * 2
def baseEnd_884632 : Nat := 403770149642922761717029

theorem tailTrace_884632 : CollatzResearch.WordTrace tailWord_884632 prefixEnd_884632 403770149642922761717029 := by
  unfold tailWord_884632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132589865568410981184075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21510119820757881308245433 16132589865568410981184075)
  ·
    refine ⟨24198884798352616471776113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16132589865568410981184075 24198884798352616471776113)
    ·
      refine ⟨18149163598764462353832085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24198884798352616471776113 18149163598764462353832085)
      ·
        refine ⟨850742043692084172835879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18149163598764462353832085 850742043692084172835879)
        ·
          refine ⟨1276113065538126259253819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850742043692084172835879 1276113065538126259253819)
          ·
            refine ⟨1914169598307189388880729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276113065538126259253819 1914169598307189388880729)
            ·
              refine ⟨1435627198730392041660547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914169598307189388880729 1435627198730392041660547)
              ·
                refine ⟨2153440798095588062490821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435627198730392041660547 2153440798095588062490821)
                ·
                  refine ⟨403770149642922761717029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153440798095588062490821 403770149642922761717029)
                  ·
                    rfl

theorem cell20_884632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_884632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884632 prefixEnd_884632 := by exact prefixLift 884632
  have htrace : WordTrace (prefixWord ++ tailWord_884632) baseStart_884632 baseEnd_884632 := by
    simpa [prefixWord, tailWord_884632, baseEnd_884632] using wordTrace_append hprefix tailTrace_884632
  have hstable : (prefixWord ++ tailWord_884632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884632).length < 2 ^ (prefixWord ++ tailWord_884632).sum := by decide
  have hdescent : baseEnd_884632 < baseStart_884632 := by decide
  rcases family_descends (prefixWord ++ tailWord_884632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884670 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_884670 : Nat := 118140960795 + 884670 * 2 ^ 59
def prefixEnd_884670 : Nat := 4983230072969 + 3 ^ 40 * 884670 * 2
def baseEnd_884670 : Nat := 403787493878363518450207

theorem tailTrace_884670 : CollatzResearch.WordTrace tailWord_884670 prefixEnd_884670 403787493878363518450207 := by
  unfold tailWord_884670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033320713124894306531433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21511043803332769634834309 4033320713124894306531433)
  ·
    refine ⟨3024990534843670729898575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4033320713124894306531433 3024990534843670729898575)
    ·
      refine ⟨4537485802265506094847863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3024990534843670729898575 4537485802265506094847863)
      ·
        refine ⟨6806228703398259142271795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537485802265506094847863 6806228703398259142271795)
        ·
          refine ⟨10209343055097388713407693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806228703398259142271795 10209343055097388713407693)
          ·
            refine ⟨3828503645661520767527885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10209343055097388713407693 3828503645661520767527885)
            ·
              refine ⟨1435688867123070287822957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3828503645661520767527885 1435688867123070287822957)
              ·
                refine ⟨538383325171151357933609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1435688867123070287822957 538383325171151357933609)
                ·
                  refine ⟨403787493878363518450207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538383325171151357933609 403787493878363518450207)
                  ·
                    rfl

theorem cell20_884670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_884670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884670 prefixEnd_884670 := by exact prefixLift 884670
  have htrace : WordTrace (prefixWord ++ tailWord_884670) baseStart_884670 baseEnd_884670 := by
    simpa [prefixWord, tailWord_884670, baseEnd_884670] using wordTrace_append hprefix tailTrace_884670
  have hstable : (prefixWord ++ tailWord_884670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884670).length < 2 ^ (prefixWord ++ tailWord_884670).sum := by decide
  have hdescent : baseEnd_884670 < baseStart_884670 := by decide
  rcases family_descends (prefixWord ++ tailWord_884670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884688 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_884688 : Nat := 118140960795 + 884688 * 2 ^ 59
def prefixEnd_884688 : Nat := 4983230072969 + 3 ^ 40 * 884688 * 2
def baseEnd_884688 : Nat := 403795709568835455850133

theorem tailTrace_884688 : CollatzResearch.WordTrace tailWord_884688 prefixEnd_884688 403795709568835455850133 := by
  unfold tailWord_884688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133611109466971763203359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21511481479289295684271145 16133611109466971763203359)
  ·
    refine ⟨24200416664200457644805039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133611109466971763203359 24200416664200457644805039)
    ·
      refine ⟨36300624996300686467207559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24200416664200457644805039 36300624996300686467207559)
      ·
        refine ⟨54450937494451029700811339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36300624996300686467207559 54450937494451029700811339)
        ·
          refine ⟨81676406241676544551217009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54450937494451029700811339 81676406241676544551217009)
          ·
            refine ⟨61257304681257408413412757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81676406241676544551217009 61257304681257408413412757)
            ·
              refine ⟨2871436156933941019378723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61257304681257408413412757 2871436156933941019378723)
              ·
                refine ⟨4307154235400911529068085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871436156933941019378723 4307154235400911529068085)
                ·
                  refine ⟨403795709568835455850133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4307154235400911529068085 403795709568835455850133)
                  ·
                    rfl

theorem cell20_884688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_884688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884688 prefixEnd_884688 := by exact prefixLift 884688
  have htrace : WordTrace (prefixWord ++ tailWord_884688) baseStart_884688 baseEnd_884688 := by
    simpa [prefixWord, tailWord_884688, baseEnd_884688] using wordTrace_append hprefix tailTrace_884688
  have hstable : (prefixWord ++ tailWord_884688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884688).length < 2 ^ (prefixWord ++ tailWord_884688).sum := by decide
  have hdescent : baseEnd_884688 < baseStart_884688 := by decide
  rcases family_descends (prefixWord ++ tailWord_884688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884698 : List Nat := [3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_884698 : Nat := 118140960795 + 884698 * 2 ^ 59
def prefixEnd_884698 : Nat := 4983230072969 + 3 ^ 40 * 884698 * 2
def baseEnd_884698 : Nat := 134600091280439955172253

theorem tailTrace_884698 : CollatzResearch.WordTrace tailWord_884698 prefixEnd_884698 134600091280439955172253 := by
  unfold tailWord_884698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8066896737224428808567687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21511724632598476822847165 8066896737224428808567687)
  ·
    refine ⟨12100345105836643212851531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8066896737224428808567687 12100345105836643212851531)
    ·
      refine ⟨18150517658754964819277297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12100345105836643212851531 18150517658754964819277297)
      ·
        refine ⟨13612888244066223614457973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18150517658754964819277297 13612888244066223614457973)
        ·
          refine ⟨1276208272881208463855435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13612888244066223614457973 1276208272881208463855435)
          ·
            refine ⟨1914312409321812695783153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276208272881208463855435 1914312409321812695783153)
            ·
              refine ⟨1435734306991359521837365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914312409321812695783153 1435734306991359521837365)
              ·
                refine ⟨134600091280439955172253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1435734306991359521837365 134600091280439955172253)
                ·
                  rfl

theorem cell20_884698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_884698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884698 prefixEnd_884698 := by exact prefixLift 884698
  have htrace : WordTrace (prefixWord ++ tailWord_884698) baseStart_884698 baseEnd_884698 := by
    simpa [prefixWord, tailWord_884698, baseEnd_884698] using wordTrace_append hprefix tailTrace_884698
  have hstable : (prefixWord ++ tailWord_884698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884698).length < 2 ^ (prefixWord ++ tailWord_884698).sum := by decide
  have hdescent : baseEnd_884698 < baseStart_884698 := by decide
  rcases family_descends (prefixWord ++ tailWord_884698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884743 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_884743 : Nat := 118140960795 + 884743 * 2 ^ 59
def prefixEnd_884743 : Nat := 4983230072969 + 3 ^ 40 * 884743 * 2
def baseEnd_884743 : Nat := 403820813067499709016575

theorem tailTrace_884743 : CollatzResearch.WordTrace tailWord_884743 prefixEnd_884743 403820813067499709016575 := by
  unfold tailWord_884743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32269228233734687919658883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21512818822489791946439255 32269228233734687919658883)
  ·
    refine ⟨48403842350602031879488325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32269228233734687919658883 48403842350602031879488325)
    ·
      refine ⟨9075720440737880977404061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48403842350602031879488325 9075720440737880977404061)
      ·
        refine ⟨3403395165276705366526523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9075720440737880977404061 3403395165276705366526523)
        ·
          refine ⟨5105092747915058049789785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403395165276705366526523 5105092747915058049789785)
          ·
            refine ⟨3828819560936293537342339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5105092747915058049789785 3828819560936293537342339)
            ·
              refine ⟨5743229341404440306013509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828819560936293537342339 5743229341404440306013509)
              ·
                refine ⟨1076855501513332557377533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5743229341404440306013509 1076855501513332557377533)
                ·
                  refine ⟨403820813067499709016575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076855501513332557377533 403820813067499709016575)
                  ·
                    rfl

theorem cell20_884743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_884743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884743 prefixEnd_884743 := by exact prefixLift 884743
  have htrace : WordTrace (prefixWord ++ tailWord_884743) baseStart_884743 baseEnd_884743 := by
    simpa [prefixWord, tailWord_884743, baseEnd_884743] using wordTrace_append hprefix tailTrace_884743
  have hstable : (prefixWord ++ tailWord_884743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884743).length < 2 ^ (prefixWord ++ tailWord_884743).sum := by decide
  have hdescent : baseEnd_884743 < baseStart_884743 := by decide
  rcases family_descends (prefixWord ++ tailWord_884743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884746 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_884746 : Nat := 118140960795 + 884746 * 2 ^ 59
def prefixEnd_884746 : Nat := 4983230072969 + 3 ^ 40 * 884746 * 2
def baseEnd_884746 : Nat := 403822182349245031916563

theorem tailTrace_884746 : CollatzResearch.WordTrace tailWord_884746 prefixEnd_884746 403822182349245031916563 := by
  unfold tailWord_884746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067334413180954858004523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21512891768482546288012061 8067334413180954858004523)
  ·
    refine ⟨12101001619771432287006785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8067334413180954858004523 12101001619771432287006785)
    ·
      refine ⟨9075751214828574215255089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12101001619771432287006785 9075751214828574215255089)
      ·
        refine ⟨6806813411121430661441317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9075751214828574215255089 6806813411121430661441317)
        ·
          refine ⟨1276277514585268249020247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6806813411121430661441317 1276277514585268249020247)
          ·
            refine ⟨1914416271877902373530371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276277514585268249020247 1914416271877902373530371)
            ·
              refine ⟨2871624407816853560295557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914416271877902373530371 2871624407816853560295557)
              ·
                refine ⟨538429576465660042555417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2871624407816853560295557 538429576465660042555417)
                ·
                  refine ⟨403822182349245031916563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538429576465660042555417 403822182349245031916563)
                  ·
                    rfl

theorem cell20_884746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_884746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884746 prefixEnd_884746 := by exact prefixLift 884746
  have htrace : WordTrace (prefixWord ++ tailWord_884746) baseStart_884746 baseEnd_884746 := by
    simpa [prefixWord, tailWord_884746, baseEnd_884746] using wordTrace_append hprefix tailTrace_884746
  have hstable : (prefixWord ++ tailWord_884746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884746).length < 2 ^ (prefixWord ++ tailWord_884746).sum := by decide
  have hdescent : baseEnd_884746 < baseStart_884746 := by decide
  rcases family_descends (prefixWord ++ tailWord_884746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884749 : List Nat := [1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_884749 : Nat := 118140960795 + 884749 * 2 ^ 59
def prefixEnd_884749 : Nat := 4983230072969 + 3 ^ 40 * 884749 * 2
def baseEnd_884749 : Nat := 134607850543663451605517

theorem tailTrace_884749 : CollatzResearch.WordTrace tailWord_884749 prefixEnd_884749 134607850543663451605517 := by
  unfold tailWord_884749
  simp only [CollatzResearch.WordTrace]
  refine ⟨32269447071712950944377301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21512964714475300629584867 32269447071712950944377301)
  ·
    refine ⟨756315165743272287758843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32269447071712950944377301 756315165743272287758843)
    ·
      refine ⟨1134472748614908431638265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756315165743272287758843 1134472748614908431638265)
      ·
        refine ⟨850854561461181323728699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134472748614908431638265 850854561461181323728699)
        ·
          refine ⟨1276281842191771985593049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850854561461181323728699 1276281842191771985593049)
          ·
            refine ⟨957211381643828989194787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276281842191771985593049 957211381643828989194787)
            ·
              refine ⟨1435817072465743483792181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957211381643828989194787 1435817072465743483792181)
              ·
                refine ⟨134607850543663451605517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1435817072465743483792181 134607850543663451605517)
                ·
                  rfl

theorem cell20_884749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_884749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884749 prefixEnd_884749 := by exact prefixLift 884749
  have htrace : WordTrace (prefixWord ++ tailWord_884749) baseStart_884749 baseEnd_884749 := by
    simpa [prefixWord, tailWord_884749, baseEnd_884749] using wordTrace_append hprefix tailTrace_884749
  have hstable : (prefixWord ++ tailWord_884749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884749).length < 2 ^ (prefixWord ++ tailWord_884749).sum := by decide
  have hdescent : baseEnd_884749 < baseStart_884749 := by decide
  rcases family_descends (prefixWord ++ tailWord_884749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884750 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_884750 : Nat := 118140960795 + 884750 * 2 ^ 59
def prefixEnd_884750 : Nat := 4983230072969 + 3 ^ 40 * 884750 * 2
def baseEnd_884750 : Nat := 403824008058238795783213

theorem tailTrace_884750 : CollatzResearch.WordTrace tailWord_884750 prefixEnd_884750 403824008058238795783213 := by
  unfold tailWord_884750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033685443088666014395463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21512989029806218743442469 4033685443088666014395463)
  ·
    refine ⟨6050528164632999021593195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4033685443088666014395463 6050528164632999021593195)
    ·
      refine ⟨9075792246949498532389793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050528164632999021593195 9075792246949498532389793)
      ·
        refine ⟨6806844185212123899292345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9075792246949498532389793 6806844185212123899292345)
        ·
          refine ⟨5105133138909092924469259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6806844185212123899292345 5105133138909092924469259)
          ·
            refine ⟨7657699708363639386703889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105133138909092924469259 7657699708363639386703889)
            ·
              refine ⟨5743274781272729540027917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657699708363639386703889 5743274781272729540027917)
              ·
                refine ⟨2153728042977273577510469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5743274781272729540027917 2153728042977273577510469)
                ·
                  refine ⟨403824008058238795783213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153728042977273577510469 403824008058238795783213)
                  ·
                    rfl

theorem cell20_884750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_884750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884750 prefixEnd_884750 := by exact prefixLift 884750
  have htrace : WordTrace (prefixWord ++ tailWord_884750) baseStart_884750 baseEnd_884750 := by
    simpa [prefixWord, tailWord_884750, baseEnd_884750] using wordTrace_append hprefix tailTrace_884750
  have hstable : (prefixWord ++ tailWord_884750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884750).length < 2 ^ (prefixWord ++ tailWord_884750).sum := by decide
  have hdescent : baseEnd_884750 < baseStart_884750 := by decide
  rcases family_descends (prefixWord ++ tailWord_884750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884798 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_884798 : Nat := 118140960795 + 884798 * 2 ^ 59
def prefixEnd_884798 : Nat := 4983230072969 + 3 ^ 40 * 884798 * 2
def baseEnd_884798 : Nat := 403845916566163962183017

theorem tailTrace_884798 : CollatzResearch.WordTrace tailWord_884798 prefixEnd_884798 403845916566163962183017 := by
  unfold tailWord_884798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033904281066929039113881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21514156165690288208607365 4033904281066929039113881)
  ·
    refine ⟨3025428210800196779335411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4033904281066929039113881 3025428210800196779335411)
    ·
      refine ⟨4538142316200295169003117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025428210800196779335411 4538142316200295169003117)
      ·
        refine ⟨1701803368575110688376169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4538142316200295169003117 1701803368575110688376169)
        ·
          refine ⟨1276352526431333016282127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701803368575110688376169 1276352526431333016282127)
          ·
            refine ⟨1914528789646999524423191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276352526431333016282127 1914528789646999524423191)
            ·
              refine ⟨2871793184470499286634787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914528789646999524423191 2871793184470499286634787)
              ·
                refine ⟨4307689776705748929952181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871793184470499286634787 4307689776705748929952181)
                ·
                  refine ⟨403845916566163962183017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4307689776705748929952181 403845916566163962183017)
                  ·
                    rfl

theorem cell20_884798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_884798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884798 prefixEnd_884798 := by exact prefixLift 884798
  have htrace : WordTrace (prefixWord ++ tailWord_884798) baseStart_884798 baseEnd_884798 := by
    simpa [prefixWord, tailWord_884798, baseEnd_884798] using wordTrace_append hprefix tailTrace_884798
  have hstable : (prefixWord ++ tailWord_884798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884798).length < 2 ^ (prefixWord ++ tailWord_884798).sum := by decide
  have hdescent : baseEnd_884798 < baseStart_884798 := by decide
  rcases family_descends (prefixWord ++ tailWord_884798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884822 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_884822 : Nat := 118140960795 + 884822 * 2 ^ 59
def prefixEnd_884822 : Nat := 4983230072969 + 3 ^ 40 * 884822 * 2
def baseEnd_884822 : Nat := 403856870820126545382919

theorem tailTrace_884822 : CollatzResearch.WordTrace tailWord_884822 prefixEnd_884822 403856870820126545382919 := by
  unfold tailWord_884822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017006850028030275736545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21514739733632322941189813 2017006850028030275736545)
  ·
    refine ⟨1512755137521022706802409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2017006850028030275736545 1512755137521022706802409)
    ·
      refine ⟨1134566353140767030101807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1512755137521022706802409 1134566353140767030101807)
      ·
        refine ⟨1701849529711150545152711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134566353140767030101807 1701849529711150545152711)
        ·
          refine ⟨2552774294566725817729067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701849529711150545152711 2552774294566725817729067)
          ·
            refine ⟨3829161441850088726593601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552774294566725817729067 3829161441850088726593601)
            ·
              refine ⟨2871871081387566544945201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829161441850088726593601 2871871081387566544945201)
              ·
                refine ⟨2153903311040674908708901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871871081387566544945201 2153903311040674908708901)
                ·
                  refine ⟨403856870820126545382919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153903311040674908708901 403856870820126545382919)
                  ·
                    rfl

theorem cell20_884822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_884822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884822 prefixEnd_884822 := by exact prefixLift 884822
  have htrace : WordTrace (prefixWord ++ tailWord_884822) baseStart_884822 baseEnd_884822 := by
    simpa [prefixWord, tailWord_884822, baseEnd_884822] using wordTrace_append hprefix tailTrace_884822
  have hstable : (prefixWord ++ tailWord_884822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884822).length < 2 ^ (prefixWord ++ tailWord_884822).sum := by decide
  have hdescent : baseEnd_884822 < baseStart_884822 := by decide
  rcases family_descends (prefixWord ++ tailWord_884822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884829 : List Nat := [1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_884829 : Nat := 118140960795 + 884829 * 2 ^ 59
def prefixEnd_884829 : Nat := 4983230072969 + 3 ^ 40 * 884829 * 2
def baseEnd_884829 : Nat := 134620021936955210716519

theorem tailTrace_884829 : CollatzResearch.WordTrace tailWord_884829 prefixEnd_884829 134620021936955210716519 := by
  unfold tailWord_884829
  simp only [CollatzResearch.WordTrace]
  refine ⟨32272364911423124607289541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21514909940948749738193027 32272364911423124607289541)
  ·
    refine ⟨6051068420891835863866789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32272364911423124607289541 6051068420891835863866789)
    ·
      refine ⟨1134575328917219224475023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6051068420891835863866789 1134575328917219224475023)
      ·
        refine ⟨1701862993375828836712535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134575328917219224475023 1701862993375828836712535)
        ·
          refine ⟨2552794490063743255068803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701862993375828836712535 2552794490063743255068803)
          ·
            refine ⟨3829191735095614882603205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552794490063743255068803 3829191735095614882603205)
            ·
              refine ⟨717973450330427790488101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3829191735095614882603205 717973450330427790488101)
              ·
                refine ⟨134620021936955210716519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717973450330427790488101 134620021936955210716519)
                ·
                  rfl

theorem cell20_884829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_884829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884829 prefixEnd_884829 := by exact prefixLift 884829
  have htrace : WordTrace (prefixWord ++ tailWord_884829) baseStart_884829 baseEnd_884829 := by
    simpa [prefixWord, tailWord_884829, baseEnd_884829] using wordTrace_append hprefix tailTrace_884829
  have hstable : (prefixWord ++ tailWord_884829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884829).length < 2 ^ (prefixWord ++ tailWord_884829).sum := by decide
  have hdescent : baseEnd_884829 < baseStart_884829 := by decide
  rcases family_descends (prefixWord ++ tailWord_884829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884860 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_884860 : Nat := 118140960795 + 884860 * 2 ^ 59
def prefixEnd_884860 : Nat := 4983230072969 + 3 ^ 40 * 884860 * 2
def baseEnd_884860 : Nat := 403874215055567302116097

theorem tailTrace_884860 : CollatzResearch.WordTrace tailWord_884860 prefixEnd_884860 403874215055567302116097 := by
  unfold tailWord_884860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136747787155408450834017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21515663716207211267778689 16136747787155408450834017)
  ·
    refine ⟨12102560840366556338125513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16136747787155408450834017 12102560840366556338125513)
    ·
      refine ⟨9076920630274917253594135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12102560840366556338125513 9076920630274917253594135)
      ·
        refine ⟨13615380945412375880391203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076920630274917253594135 13615380945412375880391203)
        ·
          refine ⟨20423071418118563820586805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615380945412375880391203 20423071418118563820586805)
          ·
            refine ⟨1914662945448615358180013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20423071418118563820586805 1914662945448615358180013)
            ·
              refine ⟨717998604543230759317505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1914662945448615358180013 717998604543230759317505)
              ·
                refine ⟨538498953407423069488129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717998604543230759317505 538498953407423069488129)
                ·
                  refine ⟨403874215055567302116097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538498953407423069488129 403874215055567302116097)
                  ·
                    rfl

theorem cell20_884860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_884860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884860 prefixEnd_884860 := by exact prefixLift 884860
  have htrace : WordTrace (prefixWord ++ tailWord_884860) baseStart_884860 baseEnd_884860 := by
    simpa [prefixWord, tailWord_884860, baseEnd_884860] using wordTrace_append hprefix tailTrace_884860
  have hstable : (prefixWord ++ tailWord_884860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884860).length < 2 ^ (prefixWord ++ tailWord_884860).sum := by decide
  have hdescent : baseEnd_884860 < baseStart_884860 := by decide
  rcases family_descends (prefixWord ++ tailWord_884860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884874 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_884874 : Nat := 118140960795 + 884874 * 2 ^ 59
def prefixEnd_884874 : Nat := 4983230072969 + 3 ^ 40 * 884874 * 2
def baseEnd_884874 : Nat := 403880605037045475649373

theorem tailTrace_884874 : CollatzResearch.WordTrace tailWord_884874 prefixEnd_884874 403880605037045475649373 := by
  unfold tailWord_884874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8068501549065024323169419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21516004130840064861785117 8068501549065024323169419)
  ·
    refine ⟨12102752323597536484754129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8068501549065024323169419 12102752323597536484754129)
    ·
      refine ⟨9077064242698152363565597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12102752323597536484754129 9077064242698152363565597)
      ·
        refine ⟨3403899091011807136337099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9077064242698152363565597 3403899091011807136337099)
        ·
          refine ⟨5105848636517710704505649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403899091011807136337099 5105848636517710704505649)
          ·
            refine ⟨3829386477388283028379237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5105848636517710704505649 3829386477388283028379237)
            ·
              refine ⟨718009964510303067821107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3829386477388283028379237 718009964510303067821107)
              ·
                refine ⟨1077014946765454601731661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718009964510303067821107 1077014946765454601731661)
                ·
                  refine ⟨403880605037045475649373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077014946765454601731661 403880605037045475649373)
                  ·
                    rfl

theorem cell20_884874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_884874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884874 prefixEnd_884874 := by exact prefixLift 884874
  have htrace : WordTrace (prefixWord ++ tailWord_884874) baseStart_884874 baseEnd_884874 := by
    simpa [prefixWord, tailWord_884874, baseEnd_884874] using wordTrace_append hprefix tailTrace_884874
  have hstable : (prefixWord ++ tailWord_884874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884874).length < 2 ^ (prefixWord ++ tailWord_884874).sum := by decide
  have hdescent : baseEnd_884874 < baseStart_884874 := by decide
  rcases family_descends (prefixWord ++ tailWord_884874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884885 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_884885 : Nat := 118140960795 + 884885 * 2 ^ 59
def prefixEnd_884885 : Nat := 4983230072969 + 3 ^ 40 * 884885 * 2
def baseEnd_884885 : Nat := 403885625736778326282661

theorem tailTrace_884885 : CollatzResearch.WordTrace tailWord_884885 prefixEnd_884885 403885625736778326282661 := by
  unfold tailWord_884885
  simp only [CollatzResearch.WordTrace]
  refine ⟨32274407399220246171328109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21516271599480164114218739 32274407399220246171328109)
  ·
    refine ⟨12102902774707592314248041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32274407399220246171328109 12102902774707592314248041)
    ·
      refine ⟨9077177081030694235686031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12102902774707592314248041 9077177081030694235686031)
      ·
        refine ⟨13615765621546041353529047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077177081030694235686031 13615765621546041353529047)
        ·
          refine ⟨20423648432319062030293571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615765621546041353529047 20423648432319062030293571)
          ·
            refine ⟨30635472648478593045440357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20423648432319062030293571 30635472648478593045440357)
            ·
              refine ⟨5744151121589736196020067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30635472648478593045440357 5744151121589736196020067)
              ·
                refine ⟨8616226682384604294030101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744151121589736196020067 8616226682384604294030101)
                ·
                  refine ⟨403885625736778326282661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8616226682384604294030101 403885625736778326282661)
                  ·
                    rfl

theorem cell20_884885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_884885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884885 prefixEnd_884885 := by exact prefixLift 884885
  have htrace : WordTrace (prefixWord ++ tailWord_884885) baseStart_884885 baseEnd_884885 := by
    simpa [prefixWord, tailWord_884885, baseEnd_884885] using wordTrace_append hprefix tailTrace_884885
  have hstable : (prefixWord ++ tailWord_884885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884885).length < 2 ^ (prefixWord ++ tailWord_884885).sum := by decide
  have hdescent : baseEnd_884885 < baseStart_884885 := by decide
  rcases family_descends (prefixWord ++ tailWord_884885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884909 : List Nat := [1, 5, 2, 1, 2, 9]
def baseStart_884909 : Nat := 118140960795 + 884909 * 2 ^ 59
def prefixEnd_884909 : Nat := 4983230072969 + 3 ^ 40 * 884909 * 2
def baseEnd_884909 : Nat := 14959132592249663314169

theorem tailTrace_884909 : CollatzResearch.WordTrace tailWord_884909 prefixEnd_884909 14959132592249663314169 := by
  unfold tailWord_884909
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275282751133298270201781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21516855167422198846801187 32275282751133298270201781)
  ·
    refine ⟨3025807757918746712831417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32275282751133298270201781 3025807757918746712831417)
    ·
      refine ⟨2269355818439060034623563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025807757918746712831417 2269355818439060034623563)
      ·
        refine ⟨3404033727658590051935345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269355818439060034623563 3404033727658590051935345)
        ·
          refine ⟨2553025295743942538951509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404033727658590051935345 2553025295743942538951509)
          ·
            refine ⟨14959132592249663314169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2553025295743942538951509 14959132592249663314169)
            ·
              rfl

theorem cell20_884909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 9].length) (baseStart_884909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884909 prefixEnd_884909 := by exact prefixLift 884909
  have htrace : WordTrace (prefixWord ++ tailWord_884909) baseStart_884909 baseEnd_884909 := by
    simpa [prefixWord, tailWord_884909, baseEnd_884909] using wordTrace_append hprefix tailTrace_884909
  have hstable : (prefixWord ++ tailWord_884909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884909).length < 2 ^ (prefixWord ++ tailWord_884909).sum := by decide
  have hdescent : baseEnd_884909 < baseStart_884909 := by decide
  rcases family_descends (prefixWord ++ tailWord_884909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884919 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 2]
def baseStart_884919 : Nat := 118140960795 + 884919 * 2 ^ 59
def prefixEnd_884919 : Nat := 4983230072969 + 3 ^ 40 * 884919 * 2
def baseEnd_884919 : Nat := 403901144263225319149189

theorem tailTrace_884919 : CollatzResearch.WordTrace tailWord_884919 prefixEnd_884919 403901144263225319149189 := by
  unfold tailWord_884919
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275647481097069978065811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21517098320731379985377207 32275647481097069978065811)
  ·
    refine ⟨48413471221645604967098717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32275647481097069978065811 48413471221645604967098717)
    ·
      refine ⟨18155051708117101862662019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48413471221645604967098717 18155051708117101862662019)
      ·
        refine ⟨27232577562175652793993029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155051708117101862662019 27232577562175652793993029)
        ·
          refine ⟨5106108292907934898873693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27232577562175652793993029 5106108292907934898873693)
          ·
            refine ⟨1914790609840475587077635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5106108292907934898873693 1914790609840475587077635)
            ·
              refine ⟨2872185914760713380616453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914790609840475587077635 2872185914760713380616453)
              ·
                refine ⟨538534859017633758865585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2872185914760713380616453 538534859017633758865585)
                ·
                  refine ⟨403901144263225319149189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538534859017633758865585 403901144263225319149189)
                  ·
                    rfl

theorem cell20_884919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 2].length) (baseStart_884919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884919 prefixEnd_884919 := by exact prefixLift 884919
  have htrace : WordTrace (prefixWord ++ tailWord_884919) baseStart_884919 baseEnd_884919 := by
    simpa [prefixWord, tailWord_884919, baseEnd_884919] using wordTrace_append hprefix tailTrace_884919
  have hstable : (prefixWord ++ tailWord_884919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884919).length < 2 ^ (prefixWord ++ tailWord_884919).sum := by decide
  have hdescent : baseEnd_884919 < baseStart_884919 := by decide
  rcases family_descends (prefixWord ++ tailWord_884919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884923 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_884923 : Nat := 118140960795 + 884923 * 2 ^ 59
def prefixEnd_884923 : Nat := 4983230072969 + 3 ^ 40 * 884923 * 2
def baseEnd_884923 : Nat := 403902969972219083015839

theorem tailTrace_884923 : CollatzResearch.WordTrace tailWord_884923 prefixEnd_884923 403902969972219083015839 := by
  unfold tailWord_884923
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275793373082578661211423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21517195582055052440807615 32275793373082578661211423)
  ·
    refine ⟨48413690059623867991817135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32275793373082578661211423 48413690059623867991817135)
    ·
      refine ⟨72620535089435801987725703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48413690059623867991817135 72620535089435801987725703)
      ·
        refine ⟨108930802634153702981588555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72620535089435801987725703 108930802634153702981588555)
        ·
          refine ⟨163396203951230554472382833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108930802634153702981588555 163396203951230554472382833)
          ·
            refine ⟨122547152963422915854287125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163396203951230554472382833 122547152963422915854287125)
            ·
              refine ⟨5744397795160449180669709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122547152963422915854287125 5744397795160449180669709)
              ·
                refine ⟨2154149173185168442751141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5744397795160449180669709 2154149173185168442751141)
                ·
                  refine ⟨403902969972219083015839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154149173185168442751141 403902969972219083015839)
                  ·
                    rfl

theorem cell20_884923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_884923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884923 prefixEnd_884923 := by exact prefixLift 884923
  have htrace : WordTrace (prefixWord ++ tailWord_884923) baseStart_884923 baseEnd_884923 := by
    simpa [prefixWord, tailWord_884923, baseEnd_884923] using wordTrace_append hprefix tailTrace_884923
  have hstable : (prefixWord ++ tailWord_884923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884923).length < 2 ^ (prefixWord ++ tailWord_884923).sum := by decide
  have hdescent : baseEnd_884923 < baseStart_884923 := by decide
  rcases family_descends (prefixWord ++ tailWord_884923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884961 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_884961 : Nat := 118140960795 + 884961 * 2 ^ 59
def prefixEnd_884961 : Nat := 4983230072969 + 3 ^ 40 * 884961 * 2
def baseEnd_884961 : Nat := 403920314207659839749017

theorem tailTrace_884961 : CollatzResearch.WordTrace tailWord_884961 prefixEnd_884961 403920314207659839749017 := by
  unfold tailWord_884961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277179346944911151094737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21518119564629940767396491 32277179346944911151094737)
  ·
    refine ⟨24207884510208683363321053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32277179346944911151094737 24207884510208683363321053)
    ·
      refine ⟨9077956691328256261245395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24207884510208683363321053 9077956691328256261245395)
      ·
        refine ⟨13616935036992384391868093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077956691328256261245395 13616935036992384391868093)
        ·
          refine ⟨5106350638872144146950535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13616935036992384391868093 5106350638872144146950535)
          ·
            refine ⟨7659525958308216220425803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106350638872144146950535 7659525958308216220425803)
            ·
              refine ⟨11489288937462324330638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659525958308216220425803 11489288937462324330638705)
              ·
                refine ⟨8616966703096743247979029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11489288937462324330638705 8616966703096743247979029)
                ·
                  refine ⟨403920314207659839749017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8616966703096743247979029 403920314207659839749017)
                  ·
                    rfl

theorem cell20_884961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_884961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884961 prefixEnd_884961 := by exact prefixLift 884961
  have htrace : WordTrace (prefixWord ++ tailWord_884961) baseStart_884961 baseEnd_884961 := by
    simpa [prefixWord, tailWord_884961, baseEnd_884961] using wordTrace_append hprefix tailTrace_884961
  have hstable : (prefixWord ++ tailWord_884961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884961).length < 2 ^ (prefixWord ++ tailWord_884961).sum := by decide
  have hdescent : baseEnd_884961 < baseStart_884961 := by decide
  rcases family_descends (prefixWord ++ tailWord_884961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884978 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_884978 : Nat := 118140960795 + 884978 * 2 ^ 59
def prefixEnd_884978 : Nat := 4983230072969 + 3 ^ 40 * 884978 * 2
def baseEnd_884978 : Nat := 403928073470883336182281

theorem tailTrace_884978 : CollatzResearch.WordTrace tailWord_884978 prefixEnd_884978 403928073470883336182281 := by
  unfold tailWord_884978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069449846970830763615897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21518532925255548702975725 8069449846970830763615897)
  ·
    refine ⟨6052087385228123072711923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8069449846970830763615897 6052087385228123072711923)
    ·
      refine ⟨9078131077842184609067885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052087385228123072711923 9078131077842184609067885)
      ·
        refine ⟨3404299154190819228400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9078131077842184609067885 3404299154190819228400457)
        ·
          refine ⟨2553224365643114421300343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404299154190819228400457 2553224365643114421300343)
          ·
            refine ⟨3829836548464671631950515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553224365643114421300343 3829836548464671631950515)
            ·
              refine ⟨5744754822697007447925773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829836548464671631950515 5744754822697007447925773)
              ·
                refine ⟨2154283058511377792972165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5744754822697007447925773 2154283058511377792972165)
                ·
                  refine ⟨403928073470883336182281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154283058511377792972165 403928073470883336182281)
                  ·
                    rfl

theorem cell20_884978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_884978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884978 prefixEnd_884978 := by exact prefixLift 884978
  have htrace : WordTrace (prefixWord ++ tailWord_884978) baseStart_884978 baseEnd_884978 := by
    simpa [prefixWord, tailWord_884978, baseEnd_884978] using wordTrace_append hprefix tailTrace_884978
  have hstable : (prefixWord ++ tailWord_884978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884978).length < 2 ^ (prefixWord ++ tailWord_884978).sum := by decide
  have hdescent : baseEnd_884978 < baseStart_884978 := by decide
  rcases family_descends (prefixWord ++ tailWord_884978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884988 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_884988 : Nat := 118140960795 + 884988 * 2 ^ 59
def prefixEnd_884988 : Nat := 4983230072969 + 3 ^ 40 * 884988 * 2
def baseEnd_884988 : Nat := 403932637743367745848907

theorem tailTrace_884988 : CollatzResearch.WordTrace tailWord_884988 prefixEnd_884988 403932637743367745848907 := by
  unfold tailWord_884988
  simp only [CollatzResearch.WordTrace]
  refine ⟨16139082058923547381163809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21518776078564729841551745 16139082058923547381163809)
  ·
    refine ⟨12104311544192660535872857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16139082058923547381163809 12104311544192660535872857)
    ·
      refine ⟨9078233658144495401904643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12104311544192660535872857 9078233658144495401904643)
      ·
        refine ⟨13617350487216743102856965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078233658144495401904643 13617350487216743102856965)
        ·
          refine ⟨2553253216353139331785681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13617350487216743102856965 2553253216353139331785681)
          ·
            refine ⟨1914939912264854498839261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553253216353139331785681 1914939912264854498839261)
            ·
              refine ⟨718102467099320437064723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1914939912264854498839261 718102467099320437064723)
              ·
                refine ⟨1077153700648980655597085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718102467099320437064723 1077153700648980655597085)
                ·
                  refine ⟨403932637743367745848907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077153700648980655597085 403932637743367745848907)
                  ·
                    rfl

theorem cell20_884988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_884988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884988 prefixEnd_884988 := by exact prefixLift 884988
  have htrace : WordTrace (prefixWord ++ tailWord_884988) baseStart_884988 baseEnd_884988 := by
    simpa [prefixWord, tailWord_884988, baseEnd_884988] using wordTrace_append hprefix tailTrace_884988
  have hstable : (prefixWord ++ tailWord_884988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884988).length < 2 ^ (prefixWord ++ tailWord_884988).sum := by decide
  have hdescent : baseEnd_884988 < baseStart_884988 := by decide
  rcases family_descends (prefixWord ++ tailWord_884988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884992 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_884992 : Nat := 118140960795 + 884992 * 2 ^ 59
def prefixEnd_884992 : Nat := 4983230072969 + 3 ^ 40 * 884992 * 2
def baseEnd_884992 : Nat := 403934463452361509715557

theorem tailTrace_884992 : CollatzResearch.WordTrace tailWord_884992 prefixEnd_884992 403934463452361509715557 := by
  unfold tailWord_884992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16139155004916301722736615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21518873339888402296982153 16139155004916301722736615)
  ·
    refine ⟨24208732507374452584104923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16139155004916301722736615 24208732507374452584104923)
    ·
      refine ⟨36313098761061678876157385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24208732507374452584104923 36313098761061678876157385)
      ·
        refine ⟨27234824070796259157118039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36313098761061678876157385 27234824070796259157118039)
        ·
          refine ⟨40852236106194388735677059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27234824070796259157118039 40852236106194388735677059)
          ·
            refine ⟨61278354159291583103515589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40852236106194388735677059 61278354159291583103515589)
            ·
              refine ⟨11489691404867171831909173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61278354159291583103515589 11489691404867171831909173)
              ·
                refine ⟨1077158569206297359241485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11489691404867171831909173 1077158569206297359241485)
                ·
                  refine ⟨403934463452361509715557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077158569206297359241485 403934463452361509715557)
                  ·
                    rfl

theorem cell20_884992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_884992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_884992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_884992 prefixEnd_884992 := by exact prefixLift 884992
  have htrace : WordTrace (prefixWord ++ tailWord_884992) baseStart_884992 baseEnd_884992 := by
    simpa [prefixWord, tailWord_884992, baseEnd_884992] using wordTrace_append hprefix tailTrace_884992
  have hstable : (prefixWord ++ tailWord_884992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884992).length < 2 ^ (prefixWord ++ tailWord_884992).sum := by decide
  have hdescent : baseEnd_884992 < baseStart_884992 := by decide
  rcases family_descends (prefixWord ++ tailWord_884992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885023 : List Nat := [1, 1, 2, 4, 3, 3, 6]
def baseStart_885023 : Nat := 118140960795 + 885023 * 2 ^ 59
def prefixEnd_885023 : Nat := 4983230072969 + 3 ^ 40 * 885023 * 2
def baseEnd_885023 : Nat := 44883179188562575520233

theorem tailTrace_885023 : CollatzResearch.WordTrace tailWord_885023 prefixEnd_885023 44883179188562575520233 := by
  unfold tailWord_885023
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279440672720295739851723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21519627115146863826567815 32279440672720295739851723)
  ·
    refine ⟨48419161009080443609777585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32279440672720295739851723 48419161009080443609777585)
    ·
      refine ⟨36314370756810332707333189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48419161009080443609777585 36314370756810332707333189)
      ·
        refine ⟨6808944516901937382624973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36314370756810332707333189 6808944516901937382624973)
        ·
          refine ⟨2553354193838226518484365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6808944516901937382624973 2553354193838226518484365)
          ·
            refine ⟨957507822689334944431637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2553354193838226518484365 957507822689334944431637)
            ·
              refine ⟨44883179188562575520233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 957507822689334944431637 44883179188562575520233)
              ·
                rfl

theorem cell20_885023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_885023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885023 prefixEnd_885023 := by exact prefixLift 885023
  have htrace : WordTrace (prefixWord ++ tailWord_885023) baseStart_885023 baseEnd_885023 := by
    simpa [prefixWord, tailWord_885023, baseEnd_885023] using wordTrace_append hprefix tailTrace_885023
  have hstable : (prefixWord ++ tailWord_885023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885023).length < 2 ^ (prefixWord ++ tailWord_885023).sum := by decide
  have hdescent : baseEnd_885023 < baseStart_885023 := by decide
  rcases family_descends (prefixWord ++ tailWord_885023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885078 : List Nat := [5, 2, 3, 10]
def baseStart_885078 : Nat := 118140960795 + 885078 * 2 ^ 59
def prefixEnd_885078 : Nat := 4983230072969 + 3 ^ 40 * 885078 * 2
def baseEnd_885078 : Nat := 1662443276525627295673

theorem tailTrace_885078 : CollatzResearch.WordTrace tailWord_885078 prefixEnd_885078 1662443276525627295673 := by
  unfold tailWord_885078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017590417970065008318993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21520964458347360088735925 2017590417970065008318993)
  ·
    refine ⟨1513192813477548756239245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2017590417970065008318993 1513192813477548756239245)
    ·
      refine ⟨567447305054080783589717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1513192813477548756239245 567447305054080783589717)
      ·
        refine ⟨1662443276525627295673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 567447305054080783589717 1662443276525627295673)
        ·
          rfl

theorem cell20_885078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 10].length) (baseStart_885078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885078 prefixEnd_885078 := by exact prefixLift 885078
  have htrace : WordTrace (prefixWord ++ tailWord_885078) baseStart_885078 baseEnd_885078 := by
    simpa [prefixWord, tailWord_885078, baseEnd_885078] using wordTrace_append hprefix tailTrace_885078
  have hstable : (prefixWord ++ tailWord_885078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885078).length < 2 ^ (prefixWord ++ tailWord_885078).sum := by decide
  have hdescent : baseEnd_885078 < baseStart_885078 := by decide
  rcases family_descends (prefixWord ++ tailWord_885078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885084 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_885084 : Nat := 118140960795 + 885084 * 2 ^ 59
def prefixEnd_885084 : Nat := 4983230072969 + 3 ^ 40 * 885084 * 2
def baseEnd_885084 : Nat := 403976454759218078648515

theorem tailTrace_885084 : CollatzResearch.WordTrace tailWord_885084 prefixEnd_885084 403976454759218078648515 := by
  unfold tailWord_885084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140832762749651578911153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21521110350332868771881537 16140832762749651578911153)
  ·
    refine ⟨12105624572062238684183365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16140832762749651578911153 12105624572062238684183365)
    ·
      refine ⟨2269804607261669753284381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12105624572062238684183365 2269804607261669753284381)
      ·
        refine ⟨851176727723126157481643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2269804607261669753284381 851176727723126157481643)
        ·
          refine ⟨1276765091584689236222465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851176727723126157481643 1276765091584689236222465)
          ·
            refine ⟨957573818688516927166849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276765091584689236222465 957573818688516927166849)
            ·
              refine ⟨718180364016387695375137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957573818688516927166849 718180364016387695375137)
              ·
                refine ⟨538635273012290771531353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718180364016387695375137 538635273012290771531353)
                ·
                  refine ⟨403976454759218078648515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538635273012290771531353 403976454759218078648515)
                  ·
                    rfl

theorem cell20_885084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_885084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885084 prefixEnd_885084 := by exact prefixLift 885084
  have htrace : WordTrace (prefixWord ++ tailWord_885084) baseStart_885084 baseEnd_885084 := by
    simpa [prefixWord, tailWord_885084, baseEnd_885084] using wordTrace_append hprefix tailTrace_885084
  have hstable : (prefixWord ++ tailWord_885084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885084).length < 2 ^ (prefixWord ++ tailWord_885084).sum := by decide
  have hdescent : baseEnd_885084 < baseStart_885084 := by decide
  rcases family_descends (prefixWord ++ tailWord_885084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885175 : List Nat := [1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_885175 : Nat := 118140960795 + 885175 * 2 ^ 59
def prefixEnd_885175 : Nat := 4983230072969 + 3 ^ 40 * 885175 * 2
def baseEnd_885175 : Nat := 134672663212942068871603

theorem tailTrace_885175 : CollatzResearch.WordTrace tailWord_885175 prefixEnd_885175 134672663212942068871603 := by
  unfold tailWord_885175
  simp only [CollatzResearch.WordTrace]
  refine ⟨32284984568169625699384979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21523323045446417132923319 32284984568169625699384979)
  ·
    refine ⟨48427476852254438549077469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32284984568169625699384979 48427476852254438549077469)
    ·
      refine ⟨18160303819595414455904051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48427476852254438549077469 18160303819595414455904051)
      ·
        refine ⟨27240455729393121683856077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18160303819595414455904051 27240455729393121683856077)
        ·
          refine ⟨10215170898522420631446029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27240455729393121683856077 10215170898522420631446029)
          ·
            refine ⟨3830689086945907736792261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10215170898522420631446029 3830689086945907736792261)
            ·
              refine ⟨718254203802357700648549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3830689086945907736792261 718254203802357700648549)
              ·
                refine ⟨134672663212942068871603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718254203802357700648549 134672663212942068871603)
                ·
                  rfl

theorem cell20_885175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_885175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885175 prefixEnd_885175 := by exact prefixLift 885175
  have htrace : WordTrace (prefixWord ++ tailWord_885175) baseStart_885175 baseEnd_885175 := by
    simpa [prefixWord, tailWord_885175, baseEnd_885175] using wordTrace_append hprefix tailTrace_885175
  have hstable : (prefixWord ++ tailWord_885175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885175).length < 2 ^ (prefixWord ++ tailWord_885175).sum := by decide
  have hdescent : baseEnd_885175 < baseStart_885175 := by decide
  rcases family_descends (prefixWord ++ tailWord_885175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885182 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_885182 : Nat := 118140960795 + 885182 * 2 ^ 59
def prefixEnd_885182 : Nat := 4983230072969 + 3 ^ 40 * 885182 * 2
def baseEnd_885182 : Nat := 404021184629565293381447

theorem tailTrace_885182 : CollatzResearch.WordTrace tailWord_885182 prefixEnd_885182 404021184629565293381447 := by
  unfold tailWord_885182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035654984893033236861225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21523493252762843929926533 4035654984893033236861225)
  ·
    refine ⟨3026741238669774927645919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4035654984893033236861225 3026741238669774927645919)
    ·
      refine ⟨4540111858004662391468879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026741238669774927645919 4540111858004662391468879)
      ·
        refine ⟨6810167787006993587203319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540111858004662391468879 6810167787006993587203319)
        ·
          refine ⟨10215251680510490380804979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810167787006993587203319 10215251680510490380804979)
          ·
            refine ⟨15322877520765735571207469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215251680510490380804979 15322877520765735571207469)
            ·
              refine ⟨5746079070287150839202801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15322877520765735571207469 5746079070287150839202801)
              ·
                refine ⟨4309559302715363129402101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746079070287150839202801 4309559302715363129402101)
                ·
                  refine ⟨404021184629565293381447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309559302715363129402101 404021184629565293381447)
                  ·
                    rfl

theorem cell20_885182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_885182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885182 prefixEnd_885182 := by exact prefixLift 885182
  have htrace : WordTrace (prefixWord ++ tailWord_885182) baseStart_885182 baseEnd_885182 := by
    simpa [prefixWord, tailWord_885182, baseEnd_885182] using wordTrace_append hprefix tailTrace_885182
  have hstable : (prefixWord ++ tailWord_885182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885182).length < 2 ^ (prefixWord ++ tailWord_885182).sum := by decide
  have hdescent : baseEnd_885182 < baseStart_885182 := by decide
  rcases family_descends (prefixWord ++ tailWord_885182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885202 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_885202 : Nat := 118140960795 + 885202 * 2 ^ 59
def prefixEnd_885202 : Nat := 4983230072969 + 3 ^ 40 * 885202 * 2
def baseEnd_885202 : Nat := 404030313174534112714699

theorem tailTrace_885202 : CollatzResearch.WordTrace tailWord_885202 prefixEnd_885202 404030313174534112714699 := by
  unfold tailWord_885202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071492334767952327654465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21523979559381206207078573 8071492334767952327654465)
  ·
    refine ⟨6053619251075964245740849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8071492334767952327654465 6053619251075964245740849)
    ·
      refine ⟨4540214438306973184305637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6053619251075964245740849 4540214438306973184305637)
      ·
        refine ⟨851290207182557472057307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4540214438306973184305637 851290207182557472057307)
        ·
          refine ⟨1276935310773836208085961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851290207182557472057307 1276935310773836208085961)
          ·
            refine ⟨957701483080377156064471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276935310773836208085961 957701483080377156064471)
            ·
              refine ⟨1436552224620565734096707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957701483080377156064471 1436552224620565734096707)
              ·
                refine ⟨2154828336930848601145061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436552224620565734096707 2154828336930848601145061)
                ·
                  refine ⟨404030313174534112714699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154828336930848601145061 404030313174534112714699)
                  ·
                    rfl

theorem cell20_885202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_885202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885202 prefixEnd_885202 := by exact prefixLift 885202
  have htrace : WordTrace (prefixWord ++ tailWord_885202) baseStart_885202 baseEnd_885202 := by
    simpa [prefixWord, tailWord_885202, baseEnd_885202] using wordTrace_append hprefix tailTrace_885202
  have hstable : (prefixWord ++ tailWord_885202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885202).length < 2 ^ (prefixWord ++ tailWord_885202).sum := by decide
  have hdescent : baseEnd_885202 < baseStart_885202 := by decide
  rcases family_descends (prefixWord ++ tailWord_885202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885213 : List Nat := [1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_885213 : Nat := 118140960795 + 885213 * 2 ^ 59
def prefixEnd_885213 : Nat := 4983230072969 + 3 ^ 40 * 885213 * 2
def baseEnd_885213 : Nat := 134678444624755654449329

theorem tailTrace_885213 : CollatzResearch.WordTrace tailWord_885213 prefixEnd_885213 134678444624755654449329 := by
  unfold tailWord_885213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286370542031958189268293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21524247028021305459512195 32286370542031958189268293)
  ·
    refine ⟨6053694476630992160487805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32286370542031958189268293 6053694476630992160487805)
    ·
      refine ⟨2270135428736622060182927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6053694476630992160487805 2270135428736622060182927)
      ·
        refine ⟨3405203143104933090274391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270135428736622060182927 3405203143104933090274391)
        ·
          refine ⟨5107804714657399635411587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405203143104933090274391 5107804714657399635411587)
          ·
            refine ⟨7661707071986099453117381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107804714657399635411587 7661707071986099453117381)
            ·
              refine ⟨1436570075997393647459509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7661707071986099453117381 1436570075997393647459509)
              ·
                refine ⟨134678444624755654449329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1436570075997393647459509 134678444624755654449329)
                ·
                  rfl

theorem cell20_885213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_885213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885213 prefixEnd_885213 := by exact prefixLift 885213
  have htrace : WordTrace (prefixWord ++ tailWord_885213) baseStart_885213 baseEnd_885213 := by
    simpa [prefixWord, tailWord_885213, baseEnd_885213] using wordTrace_append hprefix tailTrace_885213
  have hstable : (prefixWord ++ tailWord_885213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885213).length < 2 ^ (prefixWord ++ tailWord_885213).sum := by decide
  have hdescent : baseEnd_885213 < baseStart_885213 := by decide
  rcases family_descends (prefixWord ++ tailWord_885213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885241 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_885241 : Nat := 118140960795 + 885241 * 2 ^ 59
def prefixEnd_885241 : Nat := 4983230072969 + 3 ^ 40 * 885241 * 2
def baseEnd_885241 : Nat := 404048113837223310414539

theorem tailTrace_885241 : CollatzResearch.WordTrace tailWord_885241 prefixEnd_885241 404048113837223310414539 := by
  unfold tailWord_885241
  simp only [CollatzResearch.WordTrace]
  refine ⟨32287391785930518971287577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21524927857287012647525051 32287391785930518971287577)
  ·
    refine ⟨24215543839447889228465683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32287391785930518971287577 24215543839447889228465683)
    ·
      refine ⟨36323315759171833842698525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24215543839447889228465683 36323315759171833842698525)
      ·
        refine ⟨13621243409689437691011947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36323315759171833842698525 13621243409689437691011947)
        ·
          refine ⟨20431865114534156536517921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13621243409689437691011947 20431865114534156536517921)
          ·
            refine ⟨15323898835900617402388441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20431865114534156536517921 15323898835900617402388441)
            ·
              refine ⟨11492924126925463051791331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15323898835900617402388441 11492924126925463051791331)
              ·
                refine ⟨17239386190388194577686997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492924126925463051791331 17239386190388194577686997)
                ·
                  refine ⟨404048113837223310414539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17239386190388194577686997 404048113837223310414539)
                  ·
                    rfl

theorem cell20_885241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_885241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885241 prefixEnd_885241 := by exact prefixLift 885241
  have htrace : WordTrace (prefixWord ++ tailWord_885241) baseStart_885241 baseEnd_885241 := by
    simpa [prefixWord, tailWord_885241, baseEnd_885241] using wordTrace_append hprefix tailTrace_885241
  have hstable : (prefixWord ++ tailWord_885241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885241).length < 2 ^ (prefixWord ++ tailWord_885241).sum := by decide
  have hdescent : baseEnd_885241 < baseStart_885241 := by decide
  rcases family_descends (prefixWord ++ tailWord_885241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885244 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_885244 : Nat := 118140960795 + 885244 * 2 ^ 59
def prefixEnd_885244 : Nat := 4983230072969 + 3 ^ 40 * 885244 * 2
def baseEnd_885244 : Nat := 404049483118968633314527

theorem tailTrace_885244 : CollatzResearch.WordTrace tailWord_885244 prefixEnd_885244 404049483118968633314527 := by
  unfold tailWord_885244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143750602459825241823393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21525000803279766989097857 16143750602459825241823393)
  ·
    refine ⟨12107812951844868931367545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16143750602459825241823393 12107812951844868931367545)
    ·
      refine ⟨9080859713883651698525659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12107812951844868931367545 9080859713883651698525659)
      ·
        refine ⟨13621289570825477547788489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080859713883651698525659 13621289570825477547788489)
        ·
          refine ⟨10215967178119108160841367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621289570825477547788489 10215967178119108160841367)
          ·
            refine ⟨15323950767178662241262051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215967178119108160841367 15323950767178662241262051)
            ·
              refine ⟨22985926150767993361893077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15323950767178662241262051 22985926150767993361893077)
              ·
                refine ⟨538732644158624844419369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22985926150767993361893077 538732644158624844419369)
                ·
                  refine ⟨404049483118968633314527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538732644158624844419369 404049483118968633314527)
                  ·
                    rfl

theorem cell20_885244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_885244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885244 prefixEnd_885244 := by exact prefixLift 885244
  have htrace : WordTrace (prefixWord ++ tailWord_885244) baseStart_885244 baseEnd_885244 := by
    simpa [prefixWord, tailWord_885244, baseEnd_885244] using wordTrace_append hprefix tailTrace_885244
  have hstable : (prefixWord ++ tailWord_885244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885244).length < 2 ^ (prefixWord ++ tailWord_885244).sum := by decide
  have hdescent : baseEnd_885244 < baseStart_885244 := by decide
  rcases family_descends (prefixWord ++ tailWord_885244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885268 : List Nat := [2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_885268 : Nat := 118140960795 + 885268 * 2 ^ 59
def prefixEnd_885268 : Nat := 4983230072969 + 3 ^ 40 * 885268 * 2
def baseEnd_885268 : Nat := 134686812457643738838143

theorem tailTrace_885268 : CollatzResearch.WordTrace tailWord_885268 prefixEnd_885268 134686812457643738838143 := by
  unfold tailWord_885268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144188278416351291260229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21525584371221801721680305 16144188278416351291260229)
  ·
    refine ⟨3027035302203065867111293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16144188278416351291260229 3027035302203065867111293)
    ·
      refine ⟨1135138238326149700166735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3027035302203065867111293 1135138238326149700166735)
      ·
        refine ⟨1702707357489224550250103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135138238326149700166735 1702707357489224550250103)
        ·
          refine ⟨2554061036233836825375155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702707357489224550250103 2554061036233836825375155)
          ·
            refine ⟨3831091554350755238062733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554061036233836825375155 3831091554350755238062733)
            ·
              refine ⟨1436659332881533214273525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3831091554350755238062733 1436659332881533214273525)
              ·
                refine ⟨134686812457643738838143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1436659332881533214273525 134686812457643738838143)
                ·
                  rfl

theorem cell20_885268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_885268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885268 prefixEnd_885268 := by exact prefixLift 885268
  have htrace : WordTrace (prefixWord ++ tailWord_885268) baseStart_885268 baseEnd_885268 := by
    simpa [prefixWord, tailWord_885268, baseEnd_885268] using wordTrace_append hprefix tailTrace_885268
  have hstable : (prefixWord ++ tailWord_885268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885268).length < 2 ^ (prefixWord ++ tailWord_885268).sum := by decide
  have hdescent : baseEnd_885268 < baseStart_885268 := by decide
  rcases family_descends (prefixWord ++ tailWord_885268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885279 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_885279 : Nat := 118140960795 + 885279 * 2 ^ 59
def prefixEnd_885279 : Nat := 4983230072969 + 3 ^ 40 * 885279 * 2
def baseEnd_885279 : Nat := 404065458072664067147717

theorem tailTrace_885279 : CollatzResearch.WordTrace tailWord_885279 prefixEnd_885279 404065458072664067147717 := by
  unfold tailWord_885279
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288777759792851461170891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21525851839861900974113927 32288777759792851461170891)
  ·
    refine ⟨48433166639689277191756337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32288777759792851461170891 48433166639689277191756337)
    ·
      refine ⟨36324874979766957893817253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48433166639689277191756337 36324874979766957893817253)
      ·
        refine ⟨6810914058706304605090735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36324874979766957893817253 6810914058706304605090735)
        ·
          refine ⟨10216371088059456907636103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810914058706304605090735 10216371088059456907636103)
          ·
            refine ⟨15324556632089185361454155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10216371088059456907636103 15324556632089185361454155)
            ·
              refine ⟨22986834948133778042181233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15324556632089185361454155 22986834948133778042181233)
              ·
                refine ⟨17240126211100333531635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22986834948133778042181233 17240126211100333531635925)
                ·
                  refine ⟨404065458072664067147717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17240126211100333531635925 404065458072664067147717)
                  ·
                    rfl

theorem cell20_885279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_885279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885279 prefixEnd_885279 := by exact prefixLift 885279
  have htrace : WordTrace (prefixWord ++ tailWord_885279) baseStart_885279 baseEnd_885279 := by
    simpa [prefixWord, tailWord_885279, baseEnd_885279] using wordTrace_append hprefix tailTrace_885279
  have hstable : (prefixWord ++ tailWord_885279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885279).length < 2 ^ (prefixWord ++ tailWord_885279).sum := by decide
  have hdescent : baseEnd_885279 < baseStart_885279 := by decide
  rcases family_descends (prefixWord ++ tailWord_885279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885313 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_885313 : Nat := 118140960795 + 885313 * 2 ^ 59
def prefixEnd_885313 : Nat := 4983230072969 + 3 ^ 40 * 885313 * 2
def baseEnd_885313 : Nat := 404080976599111060014245

theorem tailTrace_885313 : CollatzResearch.WordTrace tailWord_885313 prefixEnd_885313 404080976599111060014245 := by
  unfold tailWord_885313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32290017841669675267908593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21526678561113116845272395 32290017841669675267908593)
  ·
    refine ⟨24217513381252256450931445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32290017841669675267908593 24217513381252256450931445)
    ·
      refine ⟨2270391879492399042274823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24217513381252256450931445 2270391879492399042274823)
      ·
        refine ⟨3405587819238598563412235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270391879492399042274823 3405587819238598563412235)
        ·
          refine ⟨5108381728857897845118353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405587819238598563412235 5108381728857897845118353)
          ·
            refine ⟨3831286296643423383838765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5108381728857897845118353 3831286296643423383838765)
            ·
              refine ⟨1436732361241283768939537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3831286296643423383838765 1436732361241283768939537)
              ·
                refine ⟨1077549270930962826704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436732361241283768939537 1077549270930962826704653)
                ·
                  refine ⟨404080976599111060014245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077549270930962826704653 404080976599111060014245)
                  ·
                    rfl

theorem cell20_885313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_885313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885313 prefixEnd_885313 := by exact prefixLift 885313
  have htrace : WordTrace (prefixWord ++ tailWord_885313) baseStart_885313 baseEnd_885313 := by
    simpa [prefixWord, tailWord_885313, baseEnd_885313] using wordTrace_append hprefix tailTrace_885313
  have hstable : (prefixWord ++ tailWord_885313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885313).length < 2 ^ (prefixWord ++ tailWord_885313).sum := by decide
  have hdescent : baseEnd_885313 < baseStart_885313 := by decide
  rcases family_descends (prefixWord ++ tailWord_885313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885348 : List Nat := [2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_885348 : Nat := 118140960795 + 885348 * 2 ^ 59
def prefixEnd_885348 : Nat := 4983230072969 + 3 ^ 40 * 885348 * 2
def baseEnd_885348 : Nat := 134698983850935497949145

theorem tailTrace_885348 : CollatzResearch.WordTrace tailWord_885348 prefixEnd_885348 134698983850935497949145 := by
  unfold tailWord_885348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145647198271438122716349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21527529597695250830288465 16145647198271438122716349)
  ·
    refine ⟨6054617699351789296018631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16145647198271438122716349 6054617699351789296018631)
    ·
      refine ⟨9081926549027683944027947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6054617699351789296018631 9081926549027683944027947)
      ·
        refine ⟨13622889823541525916041921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9081926549027683944027947 13622889823541525916041921)
        ·
          refine ⟨10217167367656144437031441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13622889823541525916041921 10217167367656144437031441)
          ·
            refine ⟨7662875525742108327773581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10217167367656144437031441 7662875525742108327773581)
            ·
              refine ⟨2873578322153290622915093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7662875525742108327773581 2873578322153290622915093)
              ·
                refine ⟨134698983850935497949145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2873578322153290622915093 134698983850935497949145)
                ·
                  rfl

theorem cell20_885348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_885348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885348 prefixEnd_885348 := by exact prefixLift 885348
  have htrace : WordTrace (prefixWord ++ tailWord_885348) baseStart_885348 baseEnd_885348 := by
    simpa [prefixWord, tailWord_885348, baseEnd_885348] using wordTrace_append hprefix tailTrace_885348
  have hstable : (prefixWord ++ tailWord_885348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885348).length < 2 ^ (prefixWord ++ tailWord_885348).sum := by decide
  have hdescent : baseEnd_885348 < baseStart_885348 := by decide
  rcases family_descends (prefixWord ++ tailWord_885348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885378 : List Nat := [3, 4, 3, 1, 1, 1, 2, 5]
def baseStart_885378 : Nat := 118140960795 + 885378 * 2 ^ 59
def prefixEnd_885378 : Nat := 4983230072969 + 3 ^ 40 * 885378 * 2
def baseEnd_885378 : Nat := 134703548123419907615771

theorem tailTrace_885378 : CollatzResearch.WordTrace tailWord_885378 prefixEnd_885378 134703548123419907615771 := by
  unfold tailWord_885378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8073097146608547842256197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21528259057622794246016525 8073097146608547842256197)
  ·
    refine ⟨1513705714989102720423037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8073097146608547842256197 1513705714989102720423037)
    ·
      refine ⟨567639643120913520158639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1513705714989102720423037 567639643120913520158639)
      ·
        refine ⟨851459464681370280237959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567639643120913520158639 851459464681370280237959)
        ·
          refine ⟨1277189197022055420356939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851459464681370280237959 1277189197022055420356939)
          ·
            refine ⟨1915783795533083130535409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277189197022055420356939 1915783795533083130535409)
            ·
              refine ⟨1436837846649812347901557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915783795533083130535409 1436837846649812347901557)
              ·
                refine ⟨134703548123419907615771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1436837846649812347901557 134703548123419907615771)
                ·
                  rfl

theorem cell20_885378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_885378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885378 prefixEnd_885378 := by exact prefixLift 885378
  have htrace : WordTrace (prefixWord ++ tailWord_885378) baseStart_885378 baseEnd_885378 := by
    simpa [prefixWord, tailWord_885378, baseEnd_885378] using wordTrace_append hprefix tailTrace_885378
  have hstable : (prefixWord ++ tailWord_885378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885378).length < 2 ^ (prefixWord ++ tailWord_885378).sum := by decide
  have hdescent : baseEnd_885378 < baseStart_885378 := by decide
  rcases family_descends (prefixWord ++ tailWord_885378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885379 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_885379 : Nat := 118140960795 + 885379 * 2 ^ 59
def prefixEnd_885379 : Nat := 4983230072969 + 3 ^ 40 * 885379 * 2
def baseEnd_885379 : Nat := 404111100797508163813975

theorem tailTrace_885379 : CollatzResearch.WordTrace tailWord_885379 prefixEnd_885379 404111100797508163813975 := by
  unfold tailWord_885379
  simp only [CollatzResearch.WordTrace]
  refine ⟨32292425059430568539811191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21528283372953712359874127 32292425059430568539811191)
  ·
    refine ⟨48438637589145852809716787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32292425059430568539811191 48438637589145852809716787)
    ·
      refine ⟨72657956383718779214575181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48438637589145852809716787 72657956383718779214575181)
      ·
        refine ⟨27246733643894542205465693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72657956383718779214575181 27246733643894542205465693)
        ·
          refine ⟨10217525116460453327049635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27246733643894542205465693 10217525116460453327049635)
          ·
            refine ⟨15326287674690679990574453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10217525116460453327049635 15326287674690679990574453)
            ·
              refine ⟨1436839469502251249116355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15326287674690679990574453 1436839469502251249116355)
              ·
                refine ⟨2155259204253376873674533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436839469502251249116355 2155259204253376873674533)
                ·
                  refine ⟨404111100797508163813975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2155259204253376873674533 404111100797508163813975)
                  ·
                    rfl

theorem cell20_885379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_885379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885379 prefixEnd_885379 := by exact prefixLift 885379
  have htrace : WordTrace (prefixWord ++ tailWord_885379) baseStart_885379 baseEnd_885379 := by
    simpa [prefixWord, tailWord_885379, baseEnd_885379] using wordTrace_append hprefix tailTrace_885379
  have hstable : (prefixWord ++ tailWord_885379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885379).length < 2 ^ (prefixWord ++ tailWord_885379).sum := by decide
  have hdescent : baseEnd_885379 < baseStart_885379 := by decide
  rcases family_descends (prefixWord ++ tailWord_885379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885434 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_885434 : Nat := 118140960795 + 885434 * 2 ^ 59
def prefixEnd_885434 : Nat := 4983230072969 + 3 ^ 40 * 885434 * 2
def baseEnd_885434 : Nat := 404136204296172416980417

theorem tailTrace_885434 : CollatzResearch.WordTrace tailWord_885434 prefixEnd_885434 404136204296172416980417 := by
  unfold tailWord_885434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8073607768557828233265839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21529620716154208622042237 8073607768557828233265839)
  ·
    refine ⟨12110411652836742349898759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8073607768557828233265839 12110411652836742349898759)
    ·
      refine ⟨18165617479255113524848139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12110411652836742349898759 18165617479255113524848139)
      ·
        refine ⟨27248426218882670287272209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18165617479255113524848139 27248426218882670287272209)
        ·
          refine ⟨20436319664162002715454157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27248426218882670287272209 20436319664162002715454157)
          ·
            refine ⟨7663619874060751018295309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20436319664162002715454157 7663619874060751018295309)
            ·
              refine ⟨2873857452772781631860741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7663619874060751018295309 2873857452772781631860741)
              ·
                refine ⟨538848272394896555973889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2873857452772781631860741 538848272394896555973889)
                ·
                  refine ⟨404136204296172416980417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538848272394896555973889 404136204296172416980417)
                  ·
                    rfl

theorem cell20_885434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_885434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885434 prefixEnd_885434 := by exact prefixLift 885434
  have htrace : WordTrace (prefixWord ++ tailWord_885434) baseStart_885434 baseEnd_885434 := by
    simpa [prefixWord, tailWord_885434, baseEnd_885434] using wordTrace_append hprefix tailTrace_885434
  have hstable : (prefixWord ++ tailWord_885434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885434).length < 2 ^ (prefixWord ++ tailWord_885434).sum := by decide
  have hdescent : baseEnd_885434 < baseStart_885434 := by decide
  rcases family_descends (prefixWord ++ tailWord_885434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885448 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_885448 : Nat := 118140960795 + 885448 * 2 ^ 59
def prefixEnd_885448 : Nat := 4983230072969 + 3 ^ 40 * 885448 * 2
def baseEnd_885448 : Nat := 404142594277650590513693

theorem tailTrace_885448 : CollatzResearch.WordTrace tailWord_885448 prefixEnd_885448 404142594277650590513693 := by
  unfold tailWord_885448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147470848090296662036499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21529961130787062216048665 16147470848090296662036499)
  ·
    refine ⟨24221206272135444993054749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16147470848090296662036499 24221206272135444993054749)
    ·
      refine ⟨9082952352050791872395531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24221206272135444993054749 9082952352050791872395531)
      ·
        refine ⟨13624428528076187808593297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9082952352050791872395531 13624428528076187808593297)
        ·
          refine ⟨10218321396057140856444973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13624428528076187808593297 10218321396057140856444973)
          ·
            refine ⟨3831870523521427821166865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10218321396057140856444973 3831870523521427821166865)
            ·
              refine ⟨2873902892641070865875149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831870523521427821166865 2873902892641070865875149)
              ·
                refine ⟨1077713584740401574703181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873902892641070865875149 1077713584740401574703181)
                ·
                  refine ⟨404142594277650590513693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077713584740401574703181 404142594277650590513693)
                  ·
                    rfl

theorem cell20_885448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_885448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885448 prefixEnd_885448 := by exact prefixLift 885448
  have htrace : WordTrace (prefixWord ++ tailWord_885448) baseStart_885448 baseEnd_885448 := by
    simpa [prefixWord, tailWord_885448, baseEnd_885448] using wordTrace_append hprefix tailTrace_885448
  have hstable : (prefixWord ++ tailWord_885448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885448).length < 2 ^ (prefixWord ++ tailWord_885448).sum := by decide
  have hdescent : baseEnd_885448 < baseStart_885448 := by decide
  rcases family_descends (prefixWord ++ tailWord_885448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885458 : List Nat := [3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_885458 : Nat := 118140960795 + 885458 * 2 ^ 59
def prefixEnd_885458 : Nat := 4983230072969 + 3 ^ 40 * 885458 * 2
def baseEnd_885458 : Nat := 134715719516711666726773

theorem tailTrace_885458 : CollatzResearch.WordTrace tailWord_885458 prefixEnd_885458 134715719516711666726773 := by
  unfold tailWord_885458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8073826606536091257984257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21530204284096243354624685 8073826606536091257984257)
  ·
    refine ⟨6055369954902068443488193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8073826606536091257984257 6055369954902068443488193)
    ·
      refine ⟨4541527466176551332616145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055369954902068443488193 4541527466176551332616145)
      ·
        refine ⟨3406145599632413499462109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4541527466176551332616145 3406145599632413499462109)
        ·
          refine ⟨1277304599862155062298291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3406145599632413499462109 1277304599862155062298291)
          ·
            refine ⟨1915956899793232593447437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277304599862155062298291 1915956899793232593447437)
            ·
              refine ⟨718483837422462222542789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1915956899793232593447437 718483837422462222542789)
              ·
                refine ⟨134715719516711666726773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718483837422462222542789 134715719516711666726773)
                ·
                  rfl

theorem cell20_885458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_885458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885458 prefixEnd_885458 := by exact prefixLift 885458
  have htrace : WordTrace (prefixWord ++ tailWord_885458) baseStart_885458 baseEnd_885458 := by
    simpa [prefixWord, tailWord_885458, baseEnd_885458] using wordTrace_append hprefix tailTrace_885458
  have hstable : (prefixWord ++ tailWord_885458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885458).length < 2 ^ (prefixWord ++ tailWord_885458).sum := by decide
  have hdescent : baseEnd_885458 < baseStart_885458 := by decide
  rcases family_descends (prefixWord ++ tailWord_885458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885468 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_885468 : Nat := 118140960795 + 885468 * 2 ^ 59
def prefixEnd_885468 : Nat := 4983230072969 + 3 ^ 40 * 885468 * 2
def baseEnd_885468 : Nat := 404151722822619409846945

theorem tailTrace_885468 : CollatzResearch.WordTrace tailWord_885468 prefixEnd_885468 404151722822619409846945 := by
  unfold tailWord_885468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147835578054068369900529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21530447437405424493200705 16147835578054068369900529)
  ·
    refine ⟨12110876683540551277425397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16147835578054068369900529 12110876683540551277425397)
    ·
      refine ⟨1135394689081926682258631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12110876683540551277425397 1135394689081926682258631)
      ·
        refine ⟨1703092033622890023387947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135394689081926682258631 1703092033622890023387947)
        ·
          refine ⟨2554638050434335035081921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703092033622890023387947 2554638050434335035081921)
          ·
            refine ⟨1915978537825751276311441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2554638050434335035081921 1915978537825751276311441)
            ·
              refine ⟨1436983903369313457233581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915978537825751276311441 1436983903369313457233581)
              ·
                refine ⟨538868963763492546462593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1436983903369313457233581 538868963763492546462593)
                ·
                  refine ⟨404151722822619409846945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538868963763492546462593 404151722822619409846945)
                  ·
                    rfl

theorem cell20_885468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_885468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885468 prefixEnd_885468 := by exact prefixLift 885468
  have htrace : WordTrace (prefixWord ++ tailWord_885468) baseStart_885468 baseEnd_885468 := by
    simpa [prefixWord, tailWord_885468, baseEnd_885468] using wordTrace_append hprefix tailTrace_885468
  have hstable : (prefixWord ++ tailWord_885468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885468).length < 2 ^ (prefixWord ++ tailWord_885468).sum := by decide
  have hdescent : baseEnd_885468 < baseStart_885468 := by decide
  rcases family_descends (prefixWord ++ tailWord_885468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885486 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_885486 : Nat := 118140960795 + 885486 * 2 ^ 59
def prefixEnd_885486 : Nat := 4983230072969 + 3 ^ 40 * 885486 * 2
def baseEnd_885486 : Nat := 404159938513091347246871

theorem tailTrace_885486 : CollatzResearch.WordTrace tailWord_885486 prefixEnd_885486 404159938513091347246871 := by
  unfold tailWord_885486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037040958755365726744539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21530885113361950542637541 4037040958755365726744539)
  ·
    refine ⟨6055561438133048590116809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037040958755365726744539 6055561438133048590116809)
    ·
      refine ⟨4541671078599786442587607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055561438133048590116809 4541671078599786442587607)
      ·
        refine ⟨6812506617899679663881411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541671078599786442587607 6812506617899679663881411)
        ·
          refine ⟨10218759926849519495822117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812506617899679663881411 10218759926849519495822117)
          ·
            refine ⟨1916017486284284905466647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10218759926849519495822117 1916017486284284905466647)
            ·
              refine ⟨2874026229426427358199971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916017486284284905466647 2874026229426427358199971)
              ·
                refine ⟨4311039344139641037299957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874026229426427358199971 4311039344139641037299957)
                ·
                  refine ⟨404159938513091347246871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4311039344139641037299957 404159938513091347246871)
                  ·
                    rfl

theorem cell20_885486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_885486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885486 prefixEnd_885486 := by exact prefixLift 885486
  have htrace : WordTrace (prefixWord ++ tailWord_885486) baseStart_885486 baseEnd_885486 := by
    simpa [prefixWord, tailWord_885486, baseEnd_885486] using wordTrace_append hprefix tailTrace_885486
  have hstable : (prefixWord ++ tailWord_885486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885486).length < 2 ^ (prefixWord ++ tailWord_885486).sum := by decide
  have hdescent : baseEnd_885486 < baseStart_885486 := by decide
  rcases family_descends (prefixWord ++ tailWord_885486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885538 : List Nat := [3, 3, 1, 1, 2, 2, 8]
def baseStart_885538 : Nat := 118140960795 + 885538 * 2 ^ 59
def prefixEnd_885538 : Nat := 4983230072969 + 3 ^ 40 * 885538 * 2
def baseEnd_885538 : Nat := 44909296970001141945925

theorem tailTrace_885538 : CollatzResearch.WordTrace tailWord_885538 prefixEnd_885538 44909296970001141945925 := by
  unfold tailWord_885538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074556066463634673712317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21532149510569692463232845 8074556066463634673712317)
  ·
    refine ⟨3027958524923863002642119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8074556066463634673712317 3027958524923863002642119)
    ·
      refine ⟨4541937787385794503963179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027958524923863002642119 4541937787385794503963179)
      ·
        refine ⟨6812906681078691755944769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541937787385794503963179 6812906681078691755944769)
        ·
          refine ⟨5109680010809018816958577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812906681078691755944769 5109680010809018816958577)
          ·
            refine ⟨3832260008106764112718933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5109680010809018816958577 3832260008106764112718933)
            ·
              refine ⟨44909296970001141945925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3832260008106764112718933 44909296970001141945925)
              ·
                rfl

theorem cell20_885538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_885538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885538 prefixEnd_885538 := by exact prefixLift 885538
  have htrace : WordTrace (prefixWord ++ tailWord_885538) baseStart_885538 baseEnd_885538 := by
    simpa [prefixWord, tailWord_885538, baseEnd_885538] using wordTrace_append hprefix tailTrace_885538
  have hstable : (prefixWord ++ tailWord_885538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885538).length < 2 ^ (prefixWord ++ tailWord_885538).sum := by decide
  have hdescent : baseEnd_885538 < baseStart_885538 := by decide
  rcases family_descends (prefixWord ++ tailWord_885538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885558 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_885558 : Nat := 118140960795 + 885558 * 2 ^ 59
def prefixEnd_885558 : Nat := 4983230072969 + 3 ^ 40 * 885558 * 2
def baseEnd_885558 : Nat := 404192801274979096846577

theorem tailTrace_885558 : CollatzResearch.WordTrace tailWord_885558 prefixEnd_885558 404192801274979096846577 := by
  unfold tailWord_885558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018684607861380131911083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21532635817188054740384885 2018684607861380131911083)
  ·
    refine ⟨3028026911792070197866625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018684607861380131911083 3028026911792070197866625)
    ·
      refine ⟨2271020183844052648399969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3028026911792070197866625 2271020183844052648399969)
      ·
        refine ⟨1703265137883039486299977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2271020183844052648399969 1703265137883039486299977)
        ·
          refine ⟨1277448853412279614724983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1703265137883039486299977 1277448853412279614724983)
          ·
            refine ⟨1916173280118419422087475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277448853412279614724983 1916173280118419422087475)
            ·
              refine ⟨2874259920177629133131213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916173280118419422087475 2874259920177629133131213)
              ·
                refine ⟨1077847470066610924924205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2874259920177629133131213 1077847470066610924924205)
                ·
                  refine ⟨404192801274979096846577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077847470066610924924205 404192801274979096846577)
                  ·
                    rfl

theorem cell20_885558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_885558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885558 prefixEnd_885558 := by exact prefixLift 885558
  have htrace : WordTrace (prefixWord ++ tailWord_885558) baseStart_885558 baseEnd_885558 := by
    simpa [prefixWord, tailWord_885558, baseEnd_885558] using wordTrace_append hprefix tailTrace_885558
  have hstable : (prefixWord ++ tailWord_885558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885558).length < 2 ^ (prefixWord ++ tailWord_885558).sum := by decide
  have hdescent : baseEnd_885558 < baseStart_885558 := by decide
  rcases family_descends (prefixWord ++ tailWord_885558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885586 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_885586 : Nat := 118140960795 + 885586 * 2 ^ 59
def prefixEnd_885586 : Nat := 4983230072969 + 3 ^ 40 * 885586 * 2
def baseEnd_885586 : Nat := 404205581237935443913129

theorem tailTrace_885586 : CollatzResearch.WordTrace tailWord_885586 prefixEnd_885586 404205581237935443913129 := by
  unfold tailWord_885586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074993742420160723149153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21533316646453761928397741 8074993742420160723149153)
  ·
    refine ⟨6056245306815120542361865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8074993742420160723149153 6056245306815120542361865)
    ·
      refine ⟨4542183980111340406771399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056245306815120542361865 4542183980111340406771399)
      ·
        refine ⟨6813275970167010610157099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542183980111340406771399 6813275970167010610157099)
        ·
          refine ⟨10219913955250515915235649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813275970167010610157099 10219913955250515915235649)
          ·
            refine ⟨7664935466437886936426737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10219913955250515915235649 7664935466437886936426737)
            ·
              refine ⟨5748701599828415202320053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664935466437886936426737 5748701599828415202320053)
              ·
                refine ⟨538940774983913925217505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5748701599828415202320053 538940774983913925217505)
                ·
                  refine ⟨404205581237935443913129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538940774983913925217505 404205581237935443913129)
                  ·
                    rfl

theorem cell20_885586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_885586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885586 prefixEnd_885586 := by exact prefixLift 885586
  have htrace : WordTrace (prefixWord ++ tailWord_885586) baseStart_885586 baseEnd_885586 := by
    simpa [prefixWord, tailWord_885586, baseEnd_885586] using wordTrace_append hprefix tailTrace_885586
  have hstable : (prefixWord ++ tailWord_885586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885586).length < 2 ^ (prefixWord ++ tailWord_885586).sum := by decide
  have hdescent : baseEnd_885586 < baseStart_885586 := by decide
  rcases family_descends (prefixWord ++ tailWord_885586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885597 : List Nat := [1, 4, 15]
def baseStart_885597 : Nat := 118140960795 + 885597 * 2 ^ 59
def prefixEnd_885597 : Nat := 4983230072969 + 3 ^ 40 * 885597 * 2
def baseEnd_885597 : Nat := 554472704989942790873

theorem tailTrace_885597 : CollatzResearch.WordTrace tailWord_885597 prefixEnd_885597 554472704989942790873 := by
  unfold tailWord_885597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300376172640791771247045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21533584115093861180831363 32300376172640791771247045)
  ·
    refine ⟨6056320532370148457108821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32300376172640791771247045 6056320532370148457108821)
    ·
      refine ⟨554472704989942790873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 6056320532370148457108821 554472704989942790873)
      ·
        rfl

theorem cell20_885597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 15].length) (baseStart_885597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885597 prefixEnd_885597 := by exact prefixLift 885597
  have htrace : WordTrace (prefixWord ++ tailWord_885597) baseStart_885597 baseEnd_885597 := by
    simpa [prefixWord, tailWord_885597, baseEnd_885597] using wordTrace_append hprefix tailTrace_885597
  have hstable : (prefixWord ++ tailWord_885597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885597).length < 2 ^ (prefixWord ++ tailWord_885597).sum := by decide
  have hdescent : baseEnd_885597 < baseStart_885597 := by decide
  rcases family_descends (prefixWord ++ tailWord_885597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885600 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_885600 : Nat := 118140960795 + 885600 * 2 ^ 59
def prefixEnd_885600 : Nat := 4983230072969 + 3 ^ 40 * 885600 * 2
def baseEnd_885600 : Nat := 404211971219413617446405

theorem tailTrace_885600 : CollatzResearch.WordTrace tailWord_885600 prefixEnd_885600 404211971219413617446405 := by
  unfold tailWord_885600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16150242795814961641803127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21533657061086615522404169 16150242795814961641803127)
  ·
    refine ⟨24225364193722442462704691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16150242795814961641803127 24225364193722442462704691)
    ·
      refine ⟨36338046290583663694057037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24225364193722442462704691 36338046290583663694057037)
      ·
        refine ⟨13626767358968873885271389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36338046290583663694057037 13626767358968873885271389)
        ·
          refine ⟨5110037759613327706976771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13626767358968873885271389 5110037759613327706976771)
          ·
            refine ⟨7665056639419991560465157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110037759613327706976771 7665056639419991560465157)
            ·
              refine ⟨1437198119891248417587217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7665056639419991560465157 1437198119891248417587217)
              ·
                refine ⟨1077898589918436313190413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437198119891248417587217 1077898589918436313190413)
                ·
                  refine ⟨404211971219413617446405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077898589918436313190413 404211971219413617446405)
                  ·
                    rfl

theorem cell20_885600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_885600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885600 prefixEnd_885600 := by exact prefixLift 885600
  have htrace : WordTrace (prefixWord ++ tailWord_885600) baseStart_885600 baseEnd_885600 := by
    simpa [prefixWord, tailWord_885600, baseEnd_885600] using wordTrace_append hprefix tailTrace_885600
  have hstable : (prefixWord ++ tailWord_885600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885600).length < 2 ^ (prefixWord ++ tailWord_885600).sum := by decide
  have hdescent : baseEnd_885600 < baseStart_885600 := by decide
  rcases family_descends (prefixWord ++ tailWord_885600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885603 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 2]
def baseStart_885603 : Nat := 118140960795 + 885603 * 2 ^ 59
def prefixEnd_885603 : Nat := 4983230072969 + 3 ^ 40 * 885603 * 2
def baseEnd_885603 : Nat := 404213340501158940346393

theorem tailTrace_885603 : CollatzResearch.WordTrace tailWord_885603 prefixEnd_885603 404213340501158940346393 := by
  unfold tailWord_885603
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300595010619054795965463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21533730007079369863976975 32300595010619054795965463)
  ·
    refine ⟨48450892515928582193948195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32300595010619054795965463 48450892515928582193948195)
    ·
      refine ⟨72676338773892873290922293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48450892515928582193948195 72676338773892873290922293)
      ·
        refine ⟨6813406760052456871023965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72676338773892873290922293 6813406760052456871023965)
        ·
          refine ⟨2555027535019671326633987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6813406760052456871023965 2555027535019671326633987)
          ·
            refine ⟨3832541302529506989950981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555027535019671326633987 3832541302529506989950981)
            ·
              refine ⟨718601494224282560615809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3832541302529506989950981 718601494224282560615809)
              ·
                refine ⟨538951120668211920461857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718601494224282560615809 538951120668211920461857)
                ·
                  refine ⟨404213340501158940346393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538951120668211920461857 404213340501158940346393)
                  ·
                    rfl

theorem cell20_885603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2].length) (baseStart_885603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885603 prefixEnd_885603 := by exact prefixLift 885603
  have htrace : WordTrace (prefixWord ++ tailWord_885603) baseStart_885603 baseEnd_885603 := by
    simpa [prefixWord, tailWord_885603, baseEnd_885603] using wordTrace_append hprefix tailTrace_885603
  have hstable : (prefixWord ++ tailWord_885603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885603).length < 2 ^ (prefixWord ++ tailWord_885603).sum := by decide
  have hdescent : baseEnd_885603 < baseStart_885603 := by decide
  rcases family_descends (prefixWord ++ tailWord_885603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885652 : List Nat := [2, 4, 2, 1, 1, 1, 9]
def baseStart_885652 : Nat := 118140960795 + 885652 * 2 ^ 59
def prefixEnd_885652 : Nat := 4983230072969 + 3 ^ 40 * 885652 * 2
def baseEnd_885652 : Nat := 44915078381814727523651

theorem tailTrace_885652 : CollatzResearch.WordTrace tailWord_885652 prefixEnd_885652 44915078381814727523651 := by
  unfold tailWord_885652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151191093720768082249605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21534921458294357442999473 16151191093720768082249605)
  ·
    refine ⟨3028348330072644015421801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16151191093720768082249605 3028348330072644015421801)
    ·
      refine ⟨2271261247554483011566351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3028348330072644015421801 2271261247554483011566351)
      ·
        refine ⟨3406891871331724517349527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271261247554483011566351 3406891871331724517349527)
        ·
          refine ⟨5110337806997586776024291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406891871331724517349527 5110337806997586776024291)
          ·
            refine ⟨7665506710496380164036437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110337806997586776024291 7665506710496380164036437)
            ·
              refine ⟨44915078381814727523651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7665506710496380164036437 44915078381814727523651)
              ·
                rfl

theorem cell20_885652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_885652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885652 prefixEnd_885652 := by exact prefixLift 885652
  have htrace : WordTrace (prefixWord ++ tailWord_885652) baseStart_885652 baseEnd_885652 := by
    simpa [prefixWord, tailWord_885652, baseEnd_885652] using wordTrace_append hprefix tailTrace_885652
  have hstable : (prefixWord ++ tailWord_885652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885652).length < 2 ^ (prefixWord ++ tailWord_885652).sum := by decide
  have hdescent : baseEnd_885652 < baseStart_885652 := by decide
  rcases family_descends (prefixWord ++ tailWord_885652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885673 : List Nat := [1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_885673 : Nat := 118140960795 + 885673 * 2 ^ 59
def prefixEnd_885673 : Nat := 4983230072969 + 3 ^ 40 * 885673 * 2
def baseEnd_885673 : Nat := 134748430136183269337591

theorem tailTrace_885673 : CollatzResearch.WordTrace tailWord_885673 prefixEnd_885673 134748430136183269337591 := by
  unfold tailWord_885673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32303148120365456751013673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21535432080243637834009115 32303148120365456751013673)
  ·
    refine ⟨24227361090274092563260255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32303148120365456751013673 24227361090274092563260255)
    ·
      refine ⟨36341041635411138844890383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24227361090274092563260255 36341041635411138844890383)
      ·
        refine ⟨54511562453116708267335575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36341041635411138844890383 54511562453116708267335575)
        ·
          refine ⟨81767343679675062401003363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54511562453116708267335575 81767343679675062401003363)
          ·
            refine ⟨122651015519512593601505045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81767343679675062401003363 122651015519512593601505045)
            ·
              refine ⟨5749266352477152825070549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122651015519512593601505045 5749266352477152825070549)
              ·
                refine ⟨134748430136183269337591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5749266352477152825070549 134748430136183269337591)
                ·
                  rfl

theorem cell20_885673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_885673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885673 prefixEnd_885673 := by exact prefixLift 885673
  have htrace : WordTrace (prefixWord ++ tailWord_885673) baseStart_885673 baseEnd_885673 := by
    simpa [prefixWord, tailWord_885673, baseEnd_885673] using wordTrace_append hprefix tailTrace_885673
  have hstable : (prefixWord ++ tailWord_885673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885673).length < 2 ^ (prefixWord ++ tailWord_885673).sum := by decide
  have hdescent : baseEnd_885673 < baseStart_885673 := by decide
  rcases family_descends (prefixWord ++ tailWord_885673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885711 : List Nat := [1, 1, 2, 1, 1, 6, 8]
def baseStart_885711 : Nat := 118140960795 + 885711 * 2 ^ 59
def prefixEnd_885711 : Nat := 4983230072969 + 3 ^ 40 * 885711 * 2
def baseEnd_885711 : Nat := 44918070515998951638439

theorem tailTrace_885711 : CollatzResearch.WordTrace tailWord_885711 prefixEnd_885711 44918070515998951638439 := by
  unfold tailWord_885711
  simp only [CollatzResearch.WordTrace]
  refine ⟨32304534094227789240896987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21536356062818526160597991 32304534094227789240896987)
  ·
    refine ⟨48456801141341683861345481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32304534094227789240896987 48456801141341683861345481)
    ·
      refine ⟨36342600856006262896009111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48456801141341683861345481 36342600856006262896009111)
      ·
        refine ⟨54513901284009394344013667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36342600856006262896009111 54513901284009394344013667)
        ·
          refine ⟨81770851926014091516020501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54513901284009394344013667 81770851926014091516020501)
          ·
            refine ⟨3833008684031910539813461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81770851926014091516020501 3833008684031910539813461)
            ·
              refine ⟨44918070515998951638439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3833008684031910539813461 44918070515998951638439)
              ·
                rfl

theorem cell20_885711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_885711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885711 prefixEnd_885711 := by exact prefixLift 885711
  have htrace : WordTrace (prefixWord ++ tailWord_885711) baseStart_885711 baseEnd_885711 := by
    simpa [prefixWord, tailWord_885711, baseEnd_885711] using wordTrace_append hprefix tailTrace_885711
  have hstable : (prefixWord ++ tailWord_885711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885711).length < 2 ^ (prefixWord ++ tailWord_885711).sum := by decide
  have hdescent : baseEnd_885711 < baseStart_885711 := by decide
  rcases family_descends (prefixWord ++ tailWord_885711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885714 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_885714 : Nat := 118140960795 + 885714 * 2 ^ 59
def prefixEnd_885714 : Nat := 4983230072969 + 3 ^ 40 * 885714 * 2
def baseEnd_885714 : Nat := 404264003925735887645939

theorem tailTrace_885714 : CollatzResearch.WordTrace tailWord_885714 prefixEnd_885714 404264003925735887645939 := by
  unfold tailWord_885714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076160878304230188314049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21536429008811280502170797 8076160878304230188314049)
  ·
    refine ⟨6057120658728172641235537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8076160878304230188314049 6057120658728172641235537)
    ·
      refine ⟨4542840494046129480926653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6057120658728172641235537 4542840494046129480926653)
      ·
        refine ⟨1703565185267298555347495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4542840494046129480926653 1703565185267298555347495)
        ·
          refine ⟨2555347777900947833021243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703565185267298555347495 2555347777900947833021243)
          ·
            refine ⟨3833021666851421749531865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555347777900947833021243 3833021666851421749531865)
            ·
              refine ⟨2874766250138566312148899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833021666851421749531865 2874766250138566312148899)
              ·
                refine ⟨4312149375207849468223349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874766250138566312148899 4312149375207849468223349)
                ·
                  refine ⟨404264003925735887645939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312149375207849468223349 404264003925735887645939)
                  ·
                    rfl

theorem cell20_885714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_885714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885714 prefixEnd_885714 := by exact prefixLift 885714
  have htrace : WordTrace (prefixWord ++ tailWord_885714) baseStart_885714 baseEnd_885714 := by
    simpa [prefixWord, tailWord_885714, baseEnd_885714] using wordTrace_append hprefix tailTrace_885714
  have hstable : (prefixWord ++ tailWord_885714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885714).length < 2 ^ (prefixWord ++ tailWord_885714).sum := by decide
  have hdescent : baseEnd_885714 < baseStart_885714 := by decide
  rcases family_descends (prefixWord ++ tailWord_885714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885717 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 4]
def baseStart_885717 : Nat := 118140960795 + 885717 * 2 ^ 59
def prefixEnd_885717 : Nat := 4983230072969 + 3 ^ 40 * 885717 * 2
def baseEnd_885717 : Nat := 404265373207481210545927

theorem tailTrace_885717 : CollatzResearch.WordTrace tailWord_885717 prefixEnd_885717 404265373207481210545927 := by
  unfold tailWord_885717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32304752932206052265615405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21536501954804034843743603 32304752932206052265615405)
  ·
    refine ⟨12114282349577269599605777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32304752932206052265615405 12114282349577269599605777)
    ·
      refine ⟨9085711762182952199704333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12114282349577269599605777 9085711762182952199704333)
      ·
        refine ⟨3407141910818607074889125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9085711762182952199704333 3407141910818607074889125)
        ·
          refine ⟨638839108278488826541711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3407141910818607074889125 638839108278488826541711)
          ·
            refine ⟨958258662417733239812567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638839108278488826541711 958258662417733239812567)
            ·
              refine ⟨1437387993626599859718851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958258662417733239812567 1437387993626599859718851)
              ·
                refine ⟨2156081990439899789578277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437387993626599859718851 2156081990439899789578277)
                ·
                  refine ⟨404265373207481210545927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156081990439899789578277 404265373207481210545927)
                  ·
                    rfl

theorem cell20_885717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_885717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885717 prefixEnd_885717 := by exact prefixLift 885717
  have htrace : WordTrace (prefixWord ++ tailWord_885717) baseStart_885717 baseEnd_885717 := by
    simpa [prefixWord, tailWord_885717, baseEnd_885717] using wordTrace_append hprefix tailTrace_885717
  have hstable : (prefixWord ++ tailWord_885717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885717).length < 2 ^ (prefixWord ++ tailWord_885717).sum := by decide
  have hdescent : baseEnd_885717 < baseStart_885717 := by decide
  rcases family_descends (prefixWord ++ tailWord_885717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885721 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_885721 : Nat := 118140960795 + 885721 * 2 ^ 59
def prefixEnd_885721 : Nat := 4983230072969 + 3 ^ 40 * 885721 * 2
def baseEnd_885721 : Nat := 404267198916474974412577

theorem tailTrace_885721 : CollatzResearch.WordTrace tailWord_885721 prefixEnd_885721 404267198916474974412577 := by
  unfold tailWord_885721
  simp only [CollatzResearch.WordTrace]
  refine ⟨32304898824191560948761017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21536599216127707299174011 32304898824191560948761017)
  ·
    refine ⟨24228674118143670711570763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32304898824191560948761017 24228674118143670711570763)
    ·
      refine ⟨36343011177215506067356145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24228674118143670711570763 36343011177215506067356145)
      ·
        refine ⟨27257258382911629550517109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36343011177215506067356145 27257258382911629550517109)
        ·
          refine ⟨2555367973397965270360979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27257258382911629550517109 2555367973397965270360979)
          ·
            refine ⟨3833051960096947905541469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555367973397965270360979 3833051960096947905541469)
            ·
              refine ⟨1437394485036355464578051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3833051960096947905541469 1437394485036355464578051)
              ·
                refine ⟨2156091727554533196867077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437394485036355464578051 2156091727554533196867077)
                ·
                  refine ⟨404267198916474974412577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156091727554533196867077 404267198916474974412577)
                  ·
                    rfl

theorem cell20_885721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_885721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885721 prefixEnd_885721 := by exact prefixLift 885721
  have htrace : WordTrace (prefixWord ++ tailWord_885721) baseStart_885721 baseEnd_885721 := by
    simpa [prefixWord, tailWord_885721, baseEnd_885721] using wordTrace_append hprefix tailTrace_885721
  have hstable : (prefixWord ++ tailWord_885721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885721).length < 2 ^ (prefixWord ++ tailWord_885721).sum := by decide
  have hdescent : baseEnd_885721 < baseStart_885721 := by decide
  rcases family_descends (prefixWord ++ tailWord_885721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885762 : List Nat := [3, 4, 1, 3, 2, 7]
def baseStart_885762 : Nat := 118140960795 + 885762 * 2 ^ 59
def prefixEnd_885762 : Nat := 4983230072969 + 3 ^ 40 * 885762 * 2
def baseEnd_885762 : Nat := 14973552312357816816509

theorem tailTrace_885762 : CollatzResearch.WordTrace tailWord_885762 prefixEnd_885762 14973552312357816816509 := by
  unfold tailWord_885762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076598554260756237750885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21537596144695349967335693 8076598554260756237750885)
  ·
    refine ⟨1514362228923891794578291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8076598554260756237750885 1514362228923891794578291)
    ·
      refine ⟨2271543343385837691867437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514362228923891794578291 2271543343385837691867437)
      ·
        refine ⟨851828753769689134450289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2271543343385837691867437 851828753769689134450289)
        ·
          refine ⟨638871565327266850837717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851828753769689134450289 638871565327266850837717)
          ·
            refine ⟨14973552312357816816509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 638871565327266850837717 14973552312357816816509)
            ·
              rfl

theorem cell20_885762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 7].length) (baseStart_885762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885762 prefixEnd_885762 := by exact prefixLift 885762
  have htrace : WordTrace (prefixWord ++ tailWord_885762) baseStart_885762 baseEnd_885762 := by
    simpa [prefixWord, tailWord_885762, baseEnd_885762] using wordTrace_append hprefix tailTrace_885762
  have hstable : (prefixWord ++ tailWord_885762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885762).length < 2 ^ (prefixWord ++ tailWord_885762).sum := by decide
  have hdescent : baseEnd_885762 < baseStart_885762 := by decide
  rcases family_descends (prefixWord ++ tailWord_885762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885783 : List Nat := [1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_885783 : Nat := 118140960795 + 885783 * 2 ^ 59
def prefixEnd_885783 : Nat := 4983230072969 + 3 ^ 40 * 885783 * 2
def baseEnd_885783 : Nat := 134765165801959438115219

theorem tailTrace_885783 : CollatzResearch.WordTrace tailWord_885783 prefixEnd_885783 134765165801959438115219 := by
  unfold tailWord_885783
  simp only [CollatzResearch.WordTrace]
  refine ⟨32307160149966945537518003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21538106766644630358345335 32307160149966945537518003)
  ·
    refine ⟨48460740224950418306277005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32307160149966945537518003 48460740224950418306277005)
    ·
      refine ⟨18172777584356406864853877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48460740224950418306277005 18172777584356406864853877)
      ·
        refine ⟨1703697898533413143580051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18172777584356406864853877 1703697898533413143580051)
        ·
          refine ⟨2555546847800119715370077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703697898533413143580051 2555546847800119715370077)
          ·
            refine ⟨958330067925044893263779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2555546847800119715370077 958330067925044893263779)
            ·
              refine ⟨1437495101887567339895669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958330067925044893263779 1437495101887567339895669)
              ·
                refine ⟨134765165801959438115219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1437495101887567339895669 134765165801959438115219)
                ·
                  rfl

theorem cell20_885783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_885783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885783 prefixEnd_885783 := by exact prefixLift 885783
  have htrace : WordTrace (prefixWord ++ tailWord_885783) baseStart_885783 baseEnd_885783 := by
    simpa [prefixWord, tailWord_885783, baseEnd_885783] using wordTrace_append hprefix tailTrace_885783
  have hstable : (prefixWord ++ tailWord_885783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885783).length < 2 ^ (prefixWord ++ tailWord_885783).sum := by decide
  have hdescent : baseEnd_885783 < baseStart_885783 := by decide
  rcases family_descends (prefixWord ++ tailWord_885783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885804 : List Nat := [2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_885804 : Nat := 118140960795 + 885804 * 2 ^ 59
def prefixEnd_885804 : Nat := 4983230072969 + 3 ^ 40 * 885804 * 2
def baseEnd_885804 : Nat := 134768360792698524881857

theorem tailTrace_885804 : CollatzResearch.WordTrace tailWord_885804 prefixEnd_885804 134768360792698524881857 := by
  unfold tailWord_885804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153963041445433062016233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21538617388593910749354977 16153963041445433062016233)
  ·
    refine ⟨12115472281084074796512175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16153963041445433062016233 12115472281084074796512175)
    ·
      refine ⟨18173208421626112194768263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115472281084074796512175 18173208421626112194768263)
      ·
        refine ⟨27259812632439168292152395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18173208421626112194768263 27259812632439168292152395)
        ·
          refine ⟨40889718948658752438228593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27259812632439168292152395 40889718948658752438228593)
          ·
            refine ⟨30667289211494064328671445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40889718948658752438228593 30667289211494064328671445)
            ·
              refine ⟨718764590894392132703237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30667289211494064328671445 718764590894392132703237)
              ·
                refine ⟨134768360792698524881857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718764590894392132703237 134768360792698524881857)
                ·
                  rfl

theorem cell20_885804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_885804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885804 prefixEnd_885804 := by exact prefixLift 885804
  have htrace : WordTrace (prefixWord ++ tailWord_885804) baseStart_885804 baseEnd_885804 := by
    simpa [prefixWord, tailWord_885804, baseEnd_885804] using wordTrace_append hprefix tailTrace_885804
  have hstable : (prefixWord ++ tailWord_885804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885804).length < 2 ^ (prefixWord ++ tailWord_885804).sum := by decide
  have hdescent : baseEnd_885804 < baseStart_885804 := by decide
  rcases family_descends (prefixWord ++ tailWord_885804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885856 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_885856 : Nat := 118140960795 + 885856 * 2 ^ 59
def prefixEnd_885856 : Nat := 4983230072969 + 3 ^ 40 * 885856 * 2
def baseEnd_885856 : Nat := 404328816595014504912025

theorem tailTrace_885856 : CollatzResearch.WordTrace tailWord_885856 prefixEnd_885856 404328816595014504912025 := by
  unfold tailWord_885856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16154911339351239502462711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21539881785801652669950281 16154911339351239502462711)
  ·
    refine ⟨24232367009026859253694067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16154911339351239502462711 24232367009026859253694067)
    ·
      refine ⟨36348550513540288880541101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24232367009026859253694067 36348550513540288880541101)
      ·
        refine ⟨13630706442577608330202913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36348550513540288880541101 13630706442577608330202913)
        ·
          refine ⟨10223029831933206247652185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13630706442577608330202913 10223029831933206247652185)
          ·
            refine ⟨7667272373949904685739139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10223029831933206247652185 7667272373949904685739139)
            ·
              refine ⟨11500908560924857028608709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667272373949904685739139 11500908560924857028608709)
              ·
                refine ⟨2156420355173410692864133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11500908560924857028608709 2156420355173410692864133)
                ·
                  refine ⟨404328816595014504912025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2156420355173410692864133 404328816595014504912025)
                  ·
                    rfl

theorem cell20_885856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_885856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885856 prefixEnd_885856 := by exact prefixLift 885856
  have htrace : WordTrace (prefixWord ++ tailWord_885856) baseStart_885856 baseEnd_885856 := by
    simpa [prefixWord, tailWord_885856, baseEnd_885856] using wordTrace_append hprefix tailTrace_885856
  have hstable : (prefixWord ++ tailWord_885856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885856).length < 2 ^ (prefixWord ++ tailWord_885856).sum := by decide
  have hdescent : baseEnd_885856 < baseStart_885856 := by decide
  rcases family_descends (prefixWord ++ tailWord_885856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885869 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 2]
def baseStart_885869 : Nat := 118140960795 + 885869 * 2 ^ 59
def prefixEnd_885869 : Nat := 4983230072969 + 3 ^ 40 * 885869 * 2
def baseEnd_885869 : Nat := 404334750149244237478639

theorem tailTrace_885869 : CollatzResearch.WordTrace tailWord_885869 prefixEnd_885869 404334750149244237478639 := by
  unfold tailWord_885869
  simp only [CollatzResearch.WordTrace]
  refine ⟨32310296827655382225148661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21540197885103588150099107 32310296827655382225148661)
  ·
    refine ⟨3029090327592692083607687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32310296827655382225148661 3029090327592692083607687)
    ·
      refine ⟨4543635491389038125411531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029090327592692083607687 4543635491389038125411531)
      ·
        refine ⟨6815453237083557188117297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543635491389038125411531 6815453237083557188117297)
        ·
          refine ⟨5111589927812667891087973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6815453237083557188117297 5111589927812667891087973)
          ·
            refine ⟨958423111464875229578995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5111589927812667891087973 958423111464875229578995)
            ·
              refine ⟨1437634667197312844368493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958423111464875229578995 1437634667197312844368493)
              ·
                refine ⟨539113000198992316638185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1437634667197312844368493 539113000198992316638185)
                ·
                  refine ⟨404334750149244237478639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539113000198992316638185 404334750149244237478639)
                  ·
                    rfl

theorem cell20_885869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_885869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885869 prefixEnd_885869 := by exact prefixLift 885869
  have htrace : WordTrace (prefixWord ++ tailWord_885869) baseStart_885869 baseEnd_885869 := by
    simpa [prefixWord, tailWord_885869, baseEnd_885869] using wordTrace_append hprefix tailTrace_885869
  have hstable : (prefixWord ++ tailWord_885869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885869).length < 2 ^ (prefixWord ++ tailWord_885869).sum := by decide
  have hdescent : baseEnd_885869 < baseStart_885869 := by decide
  rcases family_descends (prefixWord ++ tailWord_885869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885873 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 2]
def baseStart_885873 : Nat := 118140960795 + 885873 * 2 ^ 59
def prefixEnd_885873 : Nat := 4983230072969 + 3 ^ 40 * 885873 * 2
def baseEnd_885873 : Nat := 404336575858238001345289

theorem tailTrace_885873 : CollatzResearch.WordTrace tailWord_885873 prefixEnd_885873 404336575858238001345289 := by
  unfold tailWord_885873
  simp only [CollatzResearch.WordTrace]
  refine ⟨32310442719640890908294273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21540295146427260605529515 32310442719640890908294273)
  ·
    refine ⟨24232832039730668181220705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32310442719640890908294273 24232832039730668181220705)
    ·
      refine ⟨18174624029798001135915529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24232832039730668181220705 18174624029798001135915529)
      ·
        refine ⟨13630968022348500851936647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18174624029798001135915529 13630968022348500851936647)
        ·
          refine ⟨20446452033522751277904971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630968022348500851936647 20446452033522751277904971)
          ·
            refine ⟨30669678050284126916857457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446452033522751277904971 30669678050284126916857457)
            ·
              refine ⟨23002258537713095187643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30669678050284126916857457 23002258537713095187643093)
              ·
                refine ⟨539115434477650668460385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23002258537713095187643093 539115434477650668460385)
                ·
                  refine ⟨404336575858238001345289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539115434477650668460385 404336575858238001345289)
                  ·
                    rfl

theorem cell20_885873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_885873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885873 prefixEnd_885873 := by exact prefixLift 885873
  have htrace : WordTrace (prefixWord ++ tailWord_885873) baseStart_885873 baseEnd_885873 := by
    simpa [prefixWord, tailWord_885873, baseEnd_885873] using wordTrace_append hprefix tailTrace_885873
  have hstable : (prefixWord ++ tailWord_885873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885873).length < 2 ^ (prefixWord ++ tailWord_885873).sum := by decide
  have hdescent : baseEnd_885873 < baseStart_885873 := by decide
  rcases family_descends (prefixWord ++ tailWord_885873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885945 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 2]
def baseStart_885945 : Nat := 118140960795 + 885945 * 2 ^ 59
def prefixEnd_885945 : Nat := 4983230072969 + 3 ^ 40 * 885945 * 2
def baseEnd_885945 : Nat := 404369438620125750944995

theorem tailTrace_885945 : CollatzResearch.WordTrace tailWord_885945 prefixEnd_885945 404369438620125750944995 := by
  unfold tailWord_885945
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313068775380047204915289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21542045850253364803276859 32313068775380047204915289)
  ·
    refine ⟨24234801581535035403686467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32313068775380047204915289 24234801581535035403686467)
    ·
      refine ⟨36352202372302553105529701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24234801581535035403686467 36352202372302553105529701)
      ·
        refine ⟨6816037944806728707286819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36352202372302553105529701 6816037944806728707286819)
        ·
          refine ⟨10224056917210093060930229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816037944806728707286819 10224056917210093060930229)
          ·
            refine ⟨958505335988446224462209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10224056917210093060930229 958505335988446224462209)
            ·
              refine ⟨718879001991334668346657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958505335988446224462209 718879001991334668346657)
              ·
                refine ⟨539159251493501001259993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718879001991334668346657 539159251493501001259993)
                ·
                  refine ⟨404369438620125750944995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539159251493501001259993 404369438620125750944995)
                  ·
                    rfl

theorem cell20_885945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_885945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885945 prefixEnd_885945 := by exact prefixLift 885945
  have htrace : WordTrace (prefixWord ++ tailWord_885945) baseStart_885945 baseEnd_885945 := by
    simpa [prefixWord, tailWord_885945, baseEnd_885945] using wordTrace_append hprefix tailTrace_885945
  have hstable : (prefixWord ++ tailWord_885945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885945).length < 2 ^ (prefixWord ++ tailWord_885945).sum := by decide
  have hdescent : baseEnd_885945 < baseStart_885945 := by decide
  rcases family_descends (prefixWord ++ tailWord_885945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885973 : List Nat := [1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_885973 : Nat := 118140960795 + 885973 * 2 ^ 59
def prefixEnd_885973 : Nat := 4983230072969 + 3 ^ 40 * 885973 * 2
def baseEnd_885973 : Nat := 134794072861027366003849

theorem tailTrace_885973 : CollatzResearch.WordTrace tailWord_885973 prefixEnd_885973 134794072861027366003849 := by
  unfold tailWord_885973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314090019278607986934573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21542726679519071991289715 32314090019278607986934573)
  ·
    refine ⟨12117783757229477995100465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32314090019278607986934573 12117783757229477995100465)
    ·
      refine ⟨9088337817922108496325349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12117783757229477995100465 9088337817922108496325349)
      ·
        refine ⟨1704063340860395343061003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9088337817922108496325349 1704063340860395343061003)
        ·
          refine ⟨2556095011290593014591505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704063340860395343061003 2556095011290593014591505)
          ·
            refine ⟨1917071258467944760943629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2556095011290593014591505 1917071258467944760943629)
            ·
              refine ⟨718901721925479285353861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1917071258467944760943629 718901721925479285353861)
              ·
                refine ⟨134794072861027366003849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718901721925479285353861 134794072861027366003849)
                ·
                  rfl

theorem cell20_885973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_885973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885973 prefixEnd_885973 := by exact prefixLift 885973
  have htrace : WordTrace (prefixWord ++ tailWord_885973) baseStart_885973 baseEnd_885973 := by
    simpa [prefixWord, tailWord_885973, baseEnd_885973] using wordTrace_append hprefix tailTrace_885973
  have hstable : (prefixWord ++ tailWord_885973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885973).length < 2 ^ (prefixWord ++ tailWord_885973).sum := by decide
  have hdescent : baseEnd_885973 < baseStart_885973 := by decide
  rcases family_descends (prefixWord ++ tailWord_885973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885997 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_885997 : Nat := 118140960795 + 885997 * 2 ^ 59
def prefixEnd_885997 : Nat := 4983230072969 + 3 ^ 40 * 885997 * 2
def baseEnd_885997 : Nat := 404393172837044681211449

theorem tailTrace_885997 : CollatzResearch.WordTrace tailWord_885997 prefixEnd_885997 404393172837044681211449 := by
  unfold tailWord_885997
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314965371191660085808245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21543310247461106723872163 32314965371191660085808245)
  ·
    refine ⟨3029528003549218133044523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32314965371191660085808245 3029528003549218133044523)
    ·
      refine ⟨4544292005323827199566785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029528003549218133044523 4544292005323827199566785)
      ·
        refine ⟨3408219003992870399675089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4544292005323827199566785 3408219003992870399675089)
        ·
          refine ⟨2556164252994652799756317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3408219003992870399675089 2556164252994652799756317)
          ·
            refine ⟨958561594872994799908619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2556164252994652799756317 958561594872994799908619)
            ·
              refine ⟨1437842392309492199862929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958561594872994799908619 1437842392309492199862929)
              ·
                refine ⟨1078381794232119149897197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437842392309492199862929 1078381794232119149897197)
                ·
                  refine ⟨404393172837044681211449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078381794232119149897197 404393172837044681211449)
                  ·
                    rfl

theorem cell20_885997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_885997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_885997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_885997 prefixEnd_885997 := by exact prefixLift 885997
  have htrace : WordTrace (prefixWord ++ tailWord_885997) baseStart_885997 baseEnd_885997 := by
    simpa [prefixWord, tailWord_885997, baseEnd_885997] using wordTrace_append hprefix tailTrace_885997
  have hstable : (prefixWord ++ tailWord_885997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885997).length < 2 ^ (prefixWord ++ tailWord_885997).sum := by decide
  have hdescent : baseEnd_885997 < baseStart_885997 := by decide
  rcases family_descends (prefixWord ++ tailWord_885997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886042 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_886042 : Nat := 118140960795 + 886042 * 2 ^ 59
def prefixEnd_886042 : Nat := 4983230072969 + 3 ^ 40 * 886042 * 2
def baseEnd_886042 : Nat := 404413712063224524711265

theorem tailTrace_886042 : CollatzResearch.WordTrace tailWord_886042 prefixEnd_886042 404413712063224524711265 := by
  unfold tailWord_886042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8079151664007158192799095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21544404437352421847464253 8079151664007158192799095)
  ·
    refine ⟨12118727496010737289198643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8079151664007158192799095 12118727496010737289198643)
    ·
      refine ⟨18178091244016105933797965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12118727496010737289198643 18178091244016105933797965)
      ·
        refine ⟨6816784216506039725174237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18178091244016105933797965 6816784216506039725174237)
        ·
          refine ⟨2556294081189764896940339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6816784216506039725174237 2556294081189764896940339)
          ·
            refine ⟨3834441121784647345410509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556294081189764896940339 3834441121784647345410509)
            ·
              refine ⟨1437915420669242754528941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834441121784647345410509 1437915420669242754528941)
              ·
                refine ⟨539218282750966032948353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1437915420669242754528941 539218282750966032948353)
                ·
                  refine ⟨404413712063224524711265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539218282750966032948353 404413712063224524711265)
                  ·
                    rfl

theorem cell20_886042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_886042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886042 prefixEnd_886042 := by exact prefixLift 886042
  have htrace : WordTrace (prefixWord ++ tailWord_886042) baseStart_886042 baseEnd_886042 := by
    simpa [prefixWord, tailWord_886042, baseEnd_886042] using wordTrace_append hprefix tailTrace_886042
  have hstable : (prefixWord ++ tailWord_886042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886042).length < 2 ^ (prefixWord ++ tailWord_886042).sum := by decide
  have hdescent : baseEnd_886042 < baseStart_886042 := by decide
  rcases family_descends (prefixWord ++ tailWord_886042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886053 : List Nat := [1, 3, 1, 2, 4, 1, 8]
def baseStart_886053 : Nat := 118140960795 + 886053 * 2 ^ 59
def prefixEnd_886053 : Nat := 4983230072969 + 3 ^ 40 * 886053 * 2
def baseEnd_886053 : Nat := 44935414751439708371617

theorem tailTrace_886053 : CollatzResearch.WordTrace tailWord_886053 prefixEnd_886053 44935414751439708371617 := by
  unfold tailWord_886053
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317007858988781649846813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21544671905992521099897875 32317007858988781649846813)
  ·
    refine ⟨12118877947120793118692555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32317007858988781649846813 12118877947120793118692555)
    ·
      refine ⟨18178316920681189678038833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12118877947120793118692555 18178316920681189678038833)
      ·
        refine ⟨13633737690510892258529125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18178316920681189678038833 13633737690510892258529125)
        ·
          refine ⟨2556325816970792298474211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13633737690510892258529125 2556325816970792298474211)
          ·
            refine ⟨3834488725456188447711317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556325816970792298474211 3834488725456188447711317)
            ·
              refine ⟨44935414751439708371617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3834488725456188447711317 44935414751439708371617)
              ·
                rfl

theorem cell20_886053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_886053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886053 prefixEnd_886053 := by exact prefixLift 886053
  have htrace : WordTrace (prefixWord ++ tailWord_886053) baseStart_886053 baseEnd_886053 := by
    simpa [prefixWord, tailWord_886053, baseEnd_886053] using wordTrace_append hprefix tailTrace_886053
  have hstable : (prefixWord ++ tailWord_886053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886053).length < 2 ^ (prefixWord ++ tailWord_886053).sum := by decide
  have hdescent : baseEnd_886053 < baseStart_886053 := by decide
  rcases family_descends (prefixWord ++ tailWord_886053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886115 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_886115 : Nat := 118140960795 + 886115 * 2 ^ 59
def prefixEnd_886115 : Nat := 4983230072969 + 3 ^ 40 * 886115 * 2
def baseEnd_886115 : Nat := 404447031252360715277633

theorem tailTrace_886115 : CollatzResearch.WordTrace tailWord_886115 prefixEnd_886115 404447031252360715277633 := by
  unfold tailWord_886115
  simp only [CollatzResearch.WordTrace]
  refine ⟨32319269184764166238603799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21546179456509444159069199 32319269184764166238603799)
  ·
    refine ⟨48478903777146249357905699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32319269184764166238603799 48478903777146249357905699)
    ·
      refine ⟨72718355665719374036858549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48478903777146249357905699 72718355665719374036858549)
      ·
        refine ⟨6817345843661191315955489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72718355665719374036858549 6817345843661191315955489)
        ·
          refine ⟨5113009382745893486966617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6817345843661191315955489 5113009382745893486966617)
          ·
            refine ⟨3834757037059420115224963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5113009382745893486966617 3834757037059420115224963)
            ·
              refine ⟨5752135555589130172837445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834757037059420115224963 5752135555589130172837445)
              ·
                refine ⟨1078525416672961907407021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5752135555589130172837445 1078525416672961907407021)
                ·
                  refine ⟨404447031252360715277633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078525416672961907407021 404447031252360715277633)
                  ·
                    rfl

theorem cell20_886115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_886115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886115 prefixEnd_886115 := by exact prefixLift 886115
  have htrace : WordTrace (prefixWord ++ tailWord_886115) baseStart_886115 baseEnd_886115 := by
    simpa [prefixWord, tailWord_886115, baseEnd_886115] using wordTrace_append hprefix tailTrace_886115
  have hstable : (prefixWord ++ tailWord_886115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886115).length < 2 ^ (prefixWord ++ tailWord_886115).sum := by decide
  have hdescent : baseEnd_886115 < baseStart_886115 := by decide
  rcases family_descends (prefixWord ++ tailWord_886115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886129 : List Nat := [1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_886129 : Nat := 118140960795 + 886129 * 2 ^ 59
def prefixEnd_886129 : Nat := 4983230072969 + 3 ^ 40 * 886129 * 2
def baseEnd_886129 : Nat := 134817807077946296270303

theorem tailTrace_886129 : CollatzResearch.WordTrace tailWord_886129 prefixEnd_886129 134817807077946296270303 := by
  unfold tailWord_886129
  simp only [CollatzResearch.WordTrace]
  refine ⟨32319779806713446629613441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21546519871142297753075627 32319779806713446629613441)
  ·
    refine ⟨24239834855035084972210081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32319779806713446629613441 24239834855035084972210081)
    ·
      refine ⟨18179876141276313729157561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24239834855035084972210081 18179876141276313729157561)
      ·
        refine ⟨13634907105957235296868171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18179876141276313729157561 13634907105957235296868171)
        ·
          refine ⟨20452360658935852945302257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13634907105957235296868171 20452360658935852945302257)
          ·
            refine ⟨15339270494201889708976693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20452360658935852945302257 15339270494201889708976693)
            ·
              refine ⟨1438056608831427160216565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15339270494201889708976693 1438056608831427160216565)
              ·
                refine ⟨134817807077946296270303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1438056608831427160216565 134817807077946296270303)
                ·
                  rfl

theorem cell20_886129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_886129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886129 prefixEnd_886129 := by exact prefixLift 886129
  have htrace : WordTrace (prefixWord ++ tailWord_886129) baseStart_886129 baseEnd_886129 := by
    simpa [prefixWord, tailWord_886129, baseEnd_886129] using wordTrace_append hprefix tailTrace_886129
  have hstable : (prefixWord ++ tailWord_886129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886129).length < 2 ^ (prefixWord ++ tailWord_886129).sum := by decide
  have hdescent : baseEnd_886129 < baseStart_886129 := by decide
  rcases family_descends (prefixWord ++ tailWord_886129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886201 : List Nat := [1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_886201 : Nat := 118140960795 + 886201 * 2 ^ 59
def prefixEnd_886201 : Nat := 4983230072969 + 3 ^ 40 * 886201 * 2
def baseEnd_886201 : Nat := 134828761331908879470205

theorem tailTrace_886201 : CollatzResearch.WordTrace tailWord_886201 prefixEnd_886201 134828761331908879470205 := by
  unfold tailWord_886201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32322405862452602926234457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21548270574968401950822971 32322405862452602926234457)
  ·
    refine ⟨24241804396839452194675843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32322405862452602926234457 24241804396839452194675843)
    ·
      refine ⟨36362706595259178292013765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24241804396839452194675843 36362706595259178292013765)
      ·
        refine ⟨6818007486611095929752581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36362706595259178292013765 6818007486611095929752581)
        ·
          refine ⟨1278376403739580486828609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6818007486611095929752581 1278376403739580486828609)
          ·
            refine ⟨958782302804685365121457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278376403739580486828609 958782302804685365121457)
            ·
              refine ⟨719086727103514023841093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958782302804685365121457 719086727103514023841093)
              ·
                refine ⟨134828761331908879470205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719086727103514023841093 134828761331908879470205)
                ·
                  rfl

theorem cell20_886201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_886201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886201 prefixEnd_886201 := by exact prefixLift 886201
  have htrace : WordTrace (prefixWord ++ tailWord_886201) baseStart_886201 baseEnd_886201 := by
    simpa [prefixWord, tailWord_886201, baseEnd_886201] using wordTrace_append hprefix tailTrace_886201
  have hstable : (prefixWord ++ tailWord_886201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886201).length < 2 ^ (prefixWord ++ tailWord_886201).sum := by decide
  have hdescent : baseEnd_886201 < baseStart_886201 := by decide
  rcases family_descends (prefixWord ++ tailWord_886201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886205 : List Nat := [1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_886205 : Nat := 118140960795 + 886205 * 2 ^ 59
def prefixEnd_886205 : Nat := 4983230072969 + 3 ^ 40 * 886205 * 2
def baseEnd_886205 : Nat := 134829369901573467425755

theorem tailTrace_886205 : CollatzResearch.WordTrace tailWord_886205 prefixEnd_886205 134829369901573467425755 := by
  unfold tailWord_886205
  simp only [CollatzResearch.WordTrace]
  refine ⟨32322551754438111609380069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21548367836292074406253379 32322551754438111609380069)
  ·
    refine ⟨6060478453957145926758763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32322551754438111609380069 6060478453957145926758763)
    ·
      refine ⟨9090717680935718890138145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060478453957145926758763 9090717680935718890138145)
      ·
        refine ⟨6818038260701789167603609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9090717680935718890138145 6818038260701789167603609)
        ·
          refine ⟨5113528695526341875702707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6818038260701789167603609 5113528695526341875702707)
          ·
            refine ⟨7670293043289512813554061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113528695526341875702707 7670293043289512813554061)
            ·
              refine ⟨2876359891233567305082773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7670293043289512813554061 2876359891233567305082773)
              ·
                refine ⟨134829369901573467425755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2876359891233567305082773 134829369901573467425755)
                ·
                  rfl

theorem cell20_886205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_886205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886205 prefixEnd_886205 := by exact prefixLift 886205
  have htrace : WordTrace (prefixWord ++ tailWord_886205) baseStart_886205 baseEnd_886205 := by
    simpa [prefixWord, tailWord_886205, baseEnd_886205] using wordTrace_append hprefix tailTrace_886205
  have hstable : (prefixWord ++ tailWord_886205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886205).length < 2 ^ (prefixWord ++ tailWord_886205).sum := by decide
  have hdescent : baseEnd_886205 < baseStart_886205 := by decide
  rcases family_descends (prefixWord ++ tailWord_886205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886219 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_886219 : Nat := 118140960795 + 886219 * 2 ^ 59
def prefixEnd_886219 : Nat := 4983230072969 + 3 ^ 40 * 886219 * 2
def baseEnd_886219 : Nat := 404494499686198575810541

theorem tailTrace_886219 : CollatzResearch.WordTrace tailWord_886219 prefixEnd_886219 404494499686198575810541 := by
  unfold tailWord_886219
  simp only [CollatzResearch.WordTrace]
  refine ⟨32323062376387392000389711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21548708250924928000259807 32323062376387392000389711)
  ·
    refine ⟨48484593564581088000584567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32323062376387392000389711 48484593564581088000584567)
    ·
      refine ⟨72726890346871632000876851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48484593564581088000584567 72726890346871632000876851)
      ·
        refine ⟨109090335520307448001315277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72726890346871632000876851 109090335520307448001315277)
        ·
          refine ⟨40908875820115293000493229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109090335520307448001315277 40908875820115293000493229)
          ·
            refine ⟨15340828432543234875184961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40908875820115293000493229 15340828432543234875184961)
            ·
              refine ⟨11505621324407426156388721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15340828432543234875184961 11505621324407426156388721)
              ·
                refine ⟨8629215993305569617291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505621324407426156388721 8629215993305569617291541)
                ·
                  refine ⟨404494499686198575810541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8629215993305569617291541 404494499686198575810541)
                  ·
                    rfl

theorem cell20_886219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_886219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886219 prefixEnd_886219 := by exact prefixLift 886219
  have htrace : WordTrace (prefixWord ++ tailWord_886219) baseStart_886219 baseEnd_886219 := by
    simpa [prefixWord, tailWord_886219, baseEnd_886219] using wordTrace_append hprefix tailTrace_886219
  have hstable : (prefixWord ++ tailWord_886219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886219).length < 2 ^ (prefixWord ++ tailWord_886219).sum := by decide
  have hdescent : baseEnd_886219 < baseStart_886219 := by decide
  rcases family_descends (prefixWord ++ tailWord_886219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886229 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_886229 : Nat := 118140960795 + 886229 * 2 ^ 59
def prefixEnd_886229 : Nat := 4983230072969 + 3 ^ 40 * 886229 * 2
def baseEnd_886229 : Nat := 404499063958682985477167

theorem tailTrace_886229 : CollatzResearch.WordTrace tailWord_886229 prefixEnd_886229 404499063958682985477167 := by
  unfold tailWord_886229
  simp only [CollatzResearch.WordTrace]
  refine ⟨32323427106351163708253741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21548951404234109138835827 32323427106351163708253741)
  ·
    refine ⟨12121285164881686390595153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32323427106351163708253741 12121285164881686390595153)
    ·
      refine ⟨9090963873661264792946365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12121285164881686390595153 9090963873661264792946365)
      ·
        refine ⟨3409111452622974297354887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9090963873661264792946365 3409111452622974297354887)
        ·
          refine ⟨5113667178934461446032331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409111452622974297354887 5113667178934461446032331)
          ·
            refine ⟨7670500768401692169048497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113667178934461446032331 7670500768401692169048497)
            ·
              refine ⟨5752875576301269126786373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7670500768401692169048497 5752875576301269126786373)
              ·
                refine ⟨1078664170556487961272445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5752875576301269126786373 1078664170556487961272445)
                ·
                  refine ⟨404499063958682985477167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078664170556487961272445 404499063958682985477167)
                  ·
                    rfl

theorem cell20_886229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_886229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886229 prefixEnd_886229 := by exact prefixLift 886229
  have htrace : WordTrace (prefixWord ++ tailWord_886229) baseStart_886229 baseEnd_886229 := by
    simpa [prefixWord, tailWord_886229, baseEnd_886229] using wordTrace_append hprefix tailTrace_886229
  have hstable : (prefixWord ++ tailWord_886229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886229).length < 2 ^ (prefixWord ++ tailWord_886229).sum := by decide
  have hdescent : baseEnd_886229 < baseStart_886229 := by decide
  rcases family_descends (prefixWord ++ tailWord_886229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886243 : List Nat := [1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_886243 : Nat := 118140960795 + 886243 * 2 ^ 59
def prefixEnd_886243 : Nat := 4983230072969 + 3 ^ 40 * 886243 * 2
def baseEnd_886243 : Nat := 134835151313387053003481

theorem tailTrace_886243 : CollatzResearch.WordTrace tailWord_886243 prefixEnd_886243 134835151313387053003481 := by
  unfold tailWord_886243
  simp only [CollatzResearch.WordTrace]
  refine ⟨32323937728300444099263383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21549291818866962732842255 32323937728300444099263383)
  ·
    refine ⟨48485906592450666148895075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32323937728300444099263383 48485906592450666148895075)
    ·
      refine ⟨72728859888675999223342613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48485906592450666148895075 72728859888675999223342613)
      ·
        refine ⟨3409165307281687463594185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72728859888675999223342613 3409165307281687463594185)
        ·
          refine ⟨2556873980461265597695639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409165307281687463594185 2556873980461265597695639)
          ·
            refine ⟨3835310970691898396543459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556873980461265597695639 3835310970691898396543459)
            ·
              refine ⟨5752966456037847594815189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835310970691898396543459 5752966456037847594815189)
              ·
                refine ⟨134835151313387053003481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5752966456037847594815189 134835151313387053003481)
                ·
                  rfl

theorem cell20_886243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_886243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886243 prefixEnd_886243 := by exact prefixLift 886243
  have htrace : WordTrace (prefixWord ++ tailWord_886243) baseStart_886243 baseEnd_886243 := by
    simpa [prefixWord, tailWord_886243, baseEnd_886243] using wordTrace_append hprefix tailTrace_886243
  have hstable : (prefixWord ++ tailWord_886243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886243).length < 2 ^ (prefixWord ++ tailWord_886243).sum := by decide
  have hdescent : baseEnd_886243 < baseStart_886243 := by decide
  rcases family_descends (prefixWord ++ tailWord_886243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886284 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_886284 : Nat := 118140960795 + 886284 * 2 ^ 59
def prefixEnd_886284 : Nat := 4983230072969 + 3 ^ 40 * 886284 * 2
def baseEnd_886284 : Nat := 404524167457347238643609

theorem tailTrace_886284 : CollatzResearch.WordTrace tailWord_886284 prefixEnd_886284 404524167457347238643609 := by
  unfold tailWord_886284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16162716560575954050752953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21550288747434605401003937 16162716560575954050752953)
  ·
    refine ⟨12122037420431965538064715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16162716560575954050752953 12122037420431965538064715)
    ·
      refine ⟨18183056130647948307097073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12122037420431965538064715 18183056130647948307097073)
      ·
        refine ⟨13637292097985961230322805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18183056130647948307097073 13637292097985961230322805)
        ·
          refine ⟨1278496134186183865342763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13637292097985961230322805 1278496134186183865342763)
          ·
            refine ⟨1917744201279275798014145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278496134186183865342763 1917744201279275798014145)
            ·
              refine ⟨1438308150959456848510609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917744201279275798014145 1438308150959456848510609)
              ·
                refine ⟨1078731113219592636382957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438308150959456848510609 1078731113219592636382957)
                ·
                  refine ⟨404524167457347238643609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078731113219592636382957 404524167457347238643609)
                  ·
                    rfl

theorem cell20_886284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_886284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886284 prefixEnd_886284 := by exact prefixLift 886284
  have htrace : WordTrace (prefixWord ++ tailWord_886284) baseStart_886284 baseEnd_886284 := by
    simpa [prefixWord, tailWord_886284, baseEnd_886284] using wordTrace_append hprefix tailTrace_886284
  have hstable : (prefixWord ++ tailWord_886284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886284).length < 2 ^ (prefixWord ++ tailWord_886284).sum := by decide
  have hdescent : baseEnd_886284 < baseStart_886284 := by decide
  rcases family_descends (prefixWord ++ tailWord_886284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886291 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 2]
def baseStart_886291 : Nat := 118140960795 + 886291 * 2 ^ 59
def prefixEnd_886291 : Nat := 4983230072969 + 3 ^ 40 * 886291 * 2
def baseEnd_886291 : Nat := 404527362448086325410247

theorem tailTrace_886291 : CollatzResearch.WordTrace tailWord_886291 prefixEnd_886291 404527362448086325410247 := by
  unfold tailWord_886291
  simp only [CollatzResearch.WordTrace]
  refine ⟨32325688432126548297010727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21550458954751032198007151 32325688432126548297010727)
  ·
    refine ⟨48488532648189822445516091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32325688432126548297010727 48488532648189822445516091)
    ·
      refine ⟨72732798972284733668274137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48488532648189822445516091 72732798972284733668274137)
      ·
        refine ⟨54549599229213550251205603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72732798972284733668274137 54549599229213550251205603)
        ·
          refine ⟨81824398843820325376808405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54549599229213550251205603 81824398843820325376808405)
          ·
            refine ⟨1917759347902038876018947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81824398843820325376808405 1917759347902038876018947)
            ·
              refine ⟨2876639021853058314028421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917759347902038876018947 2876639021853058314028421)
              ·
                refine ⟨539369816597448433880329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2876639021853058314028421 539369816597448433880329)
                ·
                  refine ⟨404527362448086325410247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539369816597448433880329 404527362448086325410247)
                  ·
                    rfl

theorem cell20_886291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 2].length) (baseStart_886291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886291 prefixEnd_886291 := by exact prefixLift 886291
  have htrace : WordTrace (prefixWord ++ tailWord_886291) baseStart_886291 baseEnd_886291 := by
    simpa [prefixWord, tailWord_886291, baseEnd_886291] using wordTrace_append hprefix tailTrace_886291
  have hstable : (prefixWord ++ tailWord_886291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886291).length < 2 ^ (prefixWord ++ tailWord_886291).sum := by decide
  have hdescent : baseEnd_886291 < baseStart_886291 := by decide
  rcases family_descends (prefixWord ++ tailWord_886291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886305 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_886305 : Nat := 118140960795 + 886305 * 2 ^ 59
def prefixEnd_886305 : Nat := 4983230072969 + 3 ^ 40 * 886305 * 2
def baseEnd_886305 : Nat := 404533752429564498943523

theorem tailTrace_886305 : CollatzResearch.WordTrace tailWord_886305 prefixEnd_886305 404533752429564498943523 := by
  unfold tailWord_886305
  simp only [CollatzResearch.WordTrace]
  refine ⟨32326199054075828688020369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21550799369383885792013579 32326199054075828688020369)
  ·
    refine ⟨24244649290556871516015277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32326199054075828688020369 24244649290556871516015277)
    ·
      refine ⟨9091743483958826818505729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24244649290556871516015277 9091743483958826818505729)
      ·
        refine ⟨6818807612969120113879297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091743483958826818505729 6818807612969120113879297)
        ·
          refine ⟨5114105709726840085409473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6818807612969120113879297 5114105709726840085409473)
          ·
            refine ⟨3835579282295130064057105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114105709726840085409473 3835579282295130064057105)
            ·
              refine ⟨2876684461721347548042829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835579282295130064057105 2876684461721347548042829)
              ·
                refine ⟨1078756673145505330516061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2876684461721347548042829 1078756673145505330516061)
                ·
                  refine ⟨404533752429564498943523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078756673145505330516061 404533752429564498943523)
                  ·
                    rfl

theorem cell20_886305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_886305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886305 prefixEnd_886305 := by exact prefixLift 886305
  have htrace : WordTrace (prefixWord ++ tailWord_886305) baseStart_886305 baseEnd_886305 := by
    simpa [prefixWord, tailWord_886305, baseEnd_886305] using wordTrace_append hprefix tailTrace_886305
  have hstable : (prefixWord ++ tailWord_886305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886305).length < 2 ^ (prefixWord ++ tailWord_886305).sum := by decide
  have hdescent : baseEnd_886305 < baseStart_886305 := by decide
  rcases family_descends (prefixWord ++ tailWord_886305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886329 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 2]
def baseStart_886329 : Nat := 118140960795 + 886329 * 2 ^ 59
def prefixEnd_886329 : Nat := 4983230072969 + 3 ^ 40 * 886329 * 2
def baseEnd_886329 : Nat := 404544706683527082143425

theorem tailTrace_886329 : CollatzResearch.WordTrace tailWord_886329 prefixEnd_886329 404544706683527082143425 := by
  unfold tailWord_886329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32327074405988880786894041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21551382937325920524596027 32327074405988880786894041)
  ·
    refine ⟨24245305804491660590170531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32327074405988880786894041 24245305804491660590170531)
    ·
      refine ⟨36367958706737490885255797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24245305804491660590170531 36367958706737490885255797)
      ·
        refine ⟨3409496128756639770492731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36367958706737490885255797 3409496128756639770492731)
        ·
          refine ⟨5114244193134959655739097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409496128756639770492731 5114244193134959655739097)
          ·
            refine ⟨3835683144851219741804323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114244193134959655739097 3835683144851219741804323)
            ·
              refine ⟨5753524717276829612706485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835683144851219741804323 5753524717276829612706485)
              ·
                refine ⟨539392942244702776191233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5753524717276829612706485 539392942244702776191233)
                ·
                  refine ⟨404544706683527082143425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539392942244702776191233 404544706683527082143425)
                  ·
                    rfl

theorem cell20_886329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_886329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886329 prefixEnd_886329 := by exact prefixLift 886329
  have htrace : WordTrace (prefixWord ++ tailWord_886329) baseStart_886329 baseEnd_886329 := by
    simpa [prefixWord, tailWord_886329, baseEnd_886329] using wordTrace_append hprefix tailTrace_886329
  have hstable : (prefixWord ++ tailWord_886329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886329).length < 2 ^ (prefixWord ++ tailWord_886329).sum := by decide
  have hdescent : baseEnd_886329 < baseStart_886329 := by decide
  rcases family_descends (prefixWord ++ tailWord_886329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886343 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_886343 : Nat := 118140960795 + 886343 * 2 ^ 59
def prefixEnd_886343 : Nat := 4983230072969 + 3 ^ 40 * 886343 * 2
def baseEnd_886343 : Nat := 404551096665005255676701

theorem tailTrace_886343 : CollatzResearch.WordTrace tailWord_886343 prefixEnd_886343 404551096665005255676701 := by
  unfold tailWord_886343
  simp only [CollatzResearch.WordTrace]
  refine ⟨32327585027938161177903683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21551723351958774118602455 32327585027938161177903683)
  ·
    refine ⟨48491377541907241766855525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32327585027938161177903683 48491377541907241766855525)
    ·
      refine ⟨9092133289107607831285411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48491377541907241766855525 9092133289107607831285411)
      ·
        refine ⟨13638199933661411746928117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9092133289107607831285411 13638199933661411746928117)
        ·
          refine ⟨1278581243780757351274511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13638199933661411746928117 1278581243780757351274511)
          ·
            refine ⟨1917871865671136026911767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278581243780757351274511 1917871865671136026911767)
            ·
              refine ⟨2876807798506704040367651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917871865671136026911767 2876807798506704040367651)
              ·
                refine ⟨4315211697760056060551477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876807798506704040367651 4315211697760056060551477)
                ·
                  refine ⟨404551096665005255676701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4315211697760056060551477 404551096665005255676701)
                  ·
                    rfl

theorem cell20_886343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_886343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886343 prefixEnd_886343 := by exact prefixLift 886343
  have htrace : WordTrace (prefixWord ++ tailWord_886343) baseStart_886343 baseEnd_886343 := by
    simpa [prefixWord, tailWord_886343, baseEnd_886343] using wordTrace_append hprefix tailTrace_886343
  have hstable : (prefixWord ++ tailWord_886343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886343).length < 2 ^ (prefixWord ++ tailWord_886343).sum := by decide
  have hdescent : baseEnd_886343 < baseStart_886343 := by decide
  rcases family_descends (prefixWord ++ tailWord_886343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886384 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_886384 : Nat := 118140960795 + 886384 * 2 ^ 59
def prefixEnd_886384 : Nat := 4983230072969 + 3 ^ 40 * 886384 * 2
def baseEnd_886384 : Nat := 404569810182191335309867

theorem tailTrace_886384 : CollatzResearch.WordTrace tailWord_886384 prefixEnd_886384 404569810182191335309867 := by
  unfold tailWord_886384
  simp only [CollatzResearch.WordTrace]
  refine ⟨16164540210394812590073103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21552720280526416786764137 16164540210394812590073103)
  ·
    refine ⟨24246810315592218885109655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16164540210394812590073103 24246810315592218885109655)
    ·
      refine ⟨36370215473388328327664483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24246810315592218885109655 36370215473388328327664483)
      ·
        refine ⟨54555323210082492491496725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36370215473388328327664483 54555323210082492491496725)
        ·
          refine ⟨2557280775472616835538909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54555323210082492491496725 2557280775472616835538909)
          ·
            refine ⟨958980290802231313327091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2557280775472616835538909 958980290802231313327091)
            ·
              refine ⟨1438470436203346969990637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958980290802231313327091 1438470436203346969990637)
              ·
                refine ⟨539426413576255113746489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438470436203346969990637 539426413576255113746489)
                ·
                  refine ⟨404569810182191335309867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539426413576255113746489 404569810182191335309867)
                  ·
                    rfl

theorem cell20_886384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_886384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886384 prefixEnd_886384 := by exact prefixLift 886384
  have htrace : WordTrace (prefixWord ++ tailWord_886384) baseStart_886384 baseEnd_886384 := by
    simpa [prefixWord, tailWord_886384, baseEnd_886384] using wordTrace_append hprefix tailTrace_886384
  have hstable : (prefixWord ++ tailWord_886384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886384).length < 2 ^ (prefixWord ++ tailWord_886384).sum := by decide
  have hdescent : baseEnd_886384 < baseStart_886384 := by decide
  rcases family_descends (prefixWord ++ tailWord_886384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886433 : List Nat := [1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_886433 : Nat := 118140960795 + 886433 * 2 ^ 59
def prefixEnd_886433 : Nat := 4983230072969 + 3 ^ 40 * 886433 * 2
def baseEnd_886433 : Nat := 134864058372454980892111

theorem tailTrace_886433 : CollatzResearch.WordTrace tailWord_886433 prefixEnd_886433 134864058372454980892111 := by
  unfold tailWord_886433
  simp only [CollatzResearch.WordTrace]
  refine ⟨32330867597612106548679953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21553911731741404365786635 32330867597612106548679953)
  ·
    refine ⟨24248150698209079911509965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32330867597612106548679953 24248150698209079911509965)
    ·
      refine ⟨9093056511828404966816237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24248150698209079911509965 9093056511828404966816237)
      ·
        refine ⟨3409896191935651862556089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9093056511828404966816237 3409896191935651862556089)
        ·
          refine ⟨2557422143951738896917067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409896191935651862556089 2557422143951738896917067)
          ·
            refine ⟨3836133215927608345375601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557422143951738896917067 3836133215927608345375601)
            ·
              refine ⟨2877099911945706259031701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836133215927608345375601 2877099911945706259031701)
              ·
                refine ⟨134864058372454980892111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2877099911945706259031701 134864058372454980892111)
                ·
                  rfl

theorem cell20_886433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_886433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886433 prefixEnd_886433 := by exact prefixLift 886433
  have htrace : WordTrace (prefixWord ++ tailWord_886433) baseStart_886433 baseEnd_886433 := by
    simpa [prefixWord, tailWord_886433, baseEnd_886433] using wordTrace_append hprefix tailTrace_886433
  have hstable : (prefixWord ++ tailWord_886433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886433).length < 2 ^ (prefixWord ++ tailWord_886433).sum := by decide
  have hdescent : baseEnd_886433 < baseStart_886433 := by decide
  rcases family_descends (prefixWord ++ tailWord_886433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886460 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_886460 : Nat := 118140960795 + 886460 * 2 ^ 59
def prefixEnd_886460 : Nat := 4983230072969 + 3 ^ 40 * 886460 * 2
def baseEnd_886460 : Nat := 404604498653072848776223

theorem tailTrace_886460 : CollatzResearch.WordTrace tailWord_886460 prefixEnd_886460 404604498653072848776223 := by
  unfold tailWord_886460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165926184257145079956417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21554568245676193439941889 16165926184257145079956417)
  ·
    refine ⟨12124444638192858809967313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16165926184257145079956417 12124444638192858809967313)
    ·
      refine ⟨9093333478644644107475485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12124444638192858809967313 9093333478644644107475485)
      ·
        refine ⟨3410000054491741540303307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9093333478644644107475485 3410000054491741540303307)
        ·
          refine ⟨5115000081737612310454961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410000054491741540303307 5115000081737612310454961)
          ·
            refine ⟨3836250061303209232841221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5115000081737612310454961 3836250061303209232841221)
            ·
              refine ⟨719296886494351731157729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3836250061303209232841221 719296886494351731157729)
              ·
                refine ⟨539472664870763798368297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719296886494351731157729 539472664870763798368297)
                ·
                  refine ⟨404604498653072848776223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539472664870763798368297 404604498653072848776223)
                  ·
                    rfl

theorem cell20_886460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_886460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886460 prefixEnd_886460 := by exact prefixLift 886460
  have htrace : WordTrace (prefixWord ++ tailWord_886460) baseStart_886460 baseEnd_886460 := by
    simpa [prefixWord, tailWord_886460, baseEnd_886460] using wordTrace_append hprefix tailTrace_886460
  have hstable : (prefixWord ++ tailWord_886460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886460).length < 2 ^ (prefixWord ++ tailWord_886460).sum := by decide
  have hdescent : baseEnd_886460 < baseStart_886460 := by decide
  rcases family_descends (prefixWord ++ tailWord_886460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886509 : List Nat := [1, 5, 1, 2, 1, 3, 7]
def baseStart_886509 : Nat := 118140960795 + 886509 * 2 ^ 59
def prefixEnd_886509 : Nat := 4983230072969 + 3 ^ 40 * 886509 * 2
def baseEnd_886509 : Nat := 44958540398694050682521

theorem tailTrace_886509 : CollatzResearch.WordTrace tailWord_886509 prefixEnd_886509 44958540398694050682521 := by
  unfold tailWord_886509
  simp only [CollatzResearch.WordTrace]
  refine ⟨32333639545336771528446581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21555759696891181018964387 32333639545336771528446581)
  ·
    refine ⟨3031278707375322330791867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32333639545336771528446581 3031278707375322330791867)
    ·
      refine ⟨4546918061062983496187801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031278707375322330791867 4546918061062983496187801)
      ·
        refine ⟨3410188545797237622140851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546918061062983496187801 3410188545797237622140851)
        ·
          refine ⟨5115282818695856433211277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410188545797237622140851 5115282818695856433211277)
          ·
            refine ⟨1918231057010946162454229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5115282818695856433211277 1918231057010946162454229)
            ·
              refine ⟨44958540398694050682521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1918231057010946162454229 44958540398694050682521)
              ·
                rfl

theorem cell20_886509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_886509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886509 prefixEnd_886509 := by exact prefixLift 886509
  have htrace : WordTrace (prefixWord ++ tailWord_886509) baseStart_886509 baseEnd_886509 := by
    simpa [prefixWord, tailWord_886509, baseEnd_886509] using wordTrace_append hprefix tailTrace_886509
  have hstable : (prefixWord ++ tailWord_886509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886509).length < 2 ^ (prefixWord ++ tailWord_886509).sum := by decide
  have hdescent : baseEnd_886509 < baseStart_886509 := by decide
  rcases family_descends (prefixWord ++ tailWord_886509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886554 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_886554 : Nat := 118140960795 + 886554 * 2 ^ 59
def prefixEnd_886554 : Nat := 4983230072969 + 3 ^ 40 * 886554 * 2
def baseEnd_886554 : Nat := 404647402814426299642505

theorem tailTrace_886554 : CollatzResearch.WordTrace tailWord_886554 prefixEnd_886554 404647402814426299642505 := by
  unfold tailWord_886554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8083820207543436053458679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21556853886782496142556477 8083820207543436053458679)
  ·
    refine ⟨12125730311315154080188019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8083820207543436053458679 12125730311315154080188019)
    ·
      refine ⟨18188595466972731120282029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12125730311315154080188019 18188595466972731120282029)
      ·
        refine ⟨6820723300114774170105761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18188595466972731120282029 6820723300114774170105761)
        ·
          refine ⟨5115542475086080627579321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6820723300114774170105761 5115542475086080627579321)
          ·
            refine ⟨3836656856314560470684491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5115542475086080627579321 3836656856314560470684491)
            ·
              refine ⟨5754985284471840706026737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836656856314560470684491 5754985284471840706026737)
              ·
                refine ⟨4316238963353880529520053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5754985284471840706026737 4316238963353880529520053)
                ·
                  refine ⟨404647402814426299642505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4316238963353880529520053 404647402814426299642505)
                  ·
                    rfl

theorem cell20_886554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_886554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886554 prefixEnd_886554 := by exact prefixLift 886554
  have htrace : WordTrace (prefixWord ++ tailWord_886554) baseStart_886554 baseEnd_886554 := by
    simpa [prefixWord, tailWord_886554, baseEnd_886554] using wordTrace_append hprefix tailTrace_886554
  have hstable : (prefixWord ++ tailWord_886554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886554).length < 2 ^ (prefixWord ++ tailWord_886554).sum := by decide
  have hdescent : baseEnd_886554 < baseStart_886554 := by decide
  rcases family_descends (prefixWord ++ tailWord_886554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886574 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_886574 : Nat := 118140960795 + 886574 * 2 ^ 59
def prefixEnd_886574 : Nat := 4983230072969 + 3 ^ 40 * 886574 * 2
def baseEnd_886574 : Nat := 404656531359395118975757

theorem tailTrace_886574 : CollatzResearch.WordTrace tailWord_886574 prefixEnd_886574 404656531359395118975757 := by
  unfold tailWord_886574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042001286262660953695347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21557340193400858419708517 4042001286262660953695347)
  ·
    refine ⟨6063001929393991430543021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042001286262660953695347 6063001929393991430543021)
    ·
      refine ⟨2273625723522746786453633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6063001929393991430543021 2273625723522746786453633)
      ·
        refine ⟨1705219292642060089840225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2273625723522746786453633 1705219292642060089840225)
        ·
          refine ⟨1278914469481545067380169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705219292642060089840225 1278914469481545067380169)
          ·
            refine ⟨959185852111158800535127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278914469481545067380169 959185852111158800535127)
            ·
              refine ⟨1438778778166738200802691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959185852111158800535127 1438778778166738200802691)
              ·
                refine ⟨2158168167250107301204037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438778778166738200802691 2158168167250107301204037)
                ·
                  refine ⟨404656531359395118975757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158168167250107301204037 404656531359395118975757)
                  ·
                    rfl

theorem cell20_886574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_886574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886574 prefixEnd_886574 := by exact prefixLift 886574
  have htrace : WordTrace (prefixWord ++ tailWord_886574) baseStart_886574 baseEnd_886574 := by
    simpa [prefixWord, tailWord_886574, baseEnd_886574] using wordTrace_append hprefix tailTrace_886574
  have hstable : (prefixWord ++ tailWord_886574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886574).length < 2 ^ (prefixWord ++ tailWord_886574).sum := by decide
  have hdescent : baseEnd_886574 < baseStart_886574 := by decide
  rcases family_descends (prefixWord ++ tailWord_886574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886578 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_886578 : Nat := 118140960795 + 886578 * 2 ^ 59
def prefixEnd_886578 : Nat := 4983230072969 + 3 ^ 40 * 886578 * 2
def baseEnd_886578 : Nat := 404658357068388882842407

theorem tailTrace_886578 : CollatzResearch.WordTrace tailWord_886578 prefixEnd_886578 404658357068388882842407 := by
  unfold tailWord_886578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8084039045521699078177097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21557437454724530875138925 8084039045521699078177097)
  ·
    refine ⟨6063029284141274308632823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8084039045521699078177097 6063029284141274308632823)
    ·
      refine ⟨9094543926211911462949235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063029284141274308632823 9094543926211911462949235)
      ·
        refine ⟨13641815889317867194423853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9094543926211911462949235 13641815889317867194423853)
        ·
          refine ⟨5115680958494200197908945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13641815889317867194423853 5115680958494200197908945)
          ·
            refine ⟨3836760718870650148431709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5115680958494200197908945 3836760718870650148431709)
            ·
              refine ⟨1438785269576493805661891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3836760718870650148431709 1438785269576493805661891)
              ·
                refine ⟨2158177904364740708492837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438785269576493805661891 2158177904364740708492837)
                ·
                  refine ⟨404658357068388882842407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158177904364740708492837 404658357068388882842407)
                  ·
                    rfl

theorem cell20_886578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_886578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886578 prefixEnd_886578 := by exact prefixLift 886578
  have htrace : WordTrace (prefixWord ++ tailWord_886578) baseStart_886578 baseEnd_886578 := by
    simpa [prefixWord, tailWord_886578, baseEnd_886578] using wordTrace_append hprefix tailTrace_886578
  have hstable : (prefixWord ++ tailWord_886578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886578).length < 2 ^ (prefixWord ++ tailWord_886578).sum := by decide
  have hdescent : baseEnd_886578 < baseStart_886578 := by decide
  rcases family_descends (prefixWord ++ tailWord_886578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886599 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_886599 : Nat := 118140960795 + 886599 * 2 ^ 59
def prefixEnd_886599 : Nat := 4983230072969 + 3 ^ 40 * 886599 * 2
def baseEnd_886599 : Nat := 404667942040606143142321

theorem tailTrace_886599 : CollatzResearch.WordTrace tailWord_886599 prefixEnd_886599 404667942040606143142321 := by
  unfold tailWord_886599
  simp only [CollatzResearch.WordTrace]
  refine ⟨32336922115010716899222851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21557948076673811266148567 32336922115010716899222851)
  ·
    refine ⟨48505383172516075348834277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32336922115010716899222851 48505383172516075348834277)
    ·
      refine ⟨9094759344846764127906427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48505383172516075348834277 9094759344846764127906427)
      ·
        refine ⟨13642139017270146191859641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9094759344846764127906427 13642139017270146191859641)
        ·
          refine ⟨10231604262952609643894731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13642139017270146191859641 10231604262952609643894731)
          ·
            refine ⟨15347406394428914465842097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10231604262952609643894731 15347406394428914465842097)
            ·
              refine ⟨11510554795821685849381573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15347406394428914465842097 11510554795821685849381573)
              ·
                refine ⟨2158229024216566096759045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11510554795821685849381573 2158229024216566096759045)
                ·
                  refine ⟨404667942040606143142321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158229024216566096759045 404667942040606143142321)
                  ·
                    rfl

theorem cell20_886599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_886599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886599 prefixEnd_886599 := by exact prefixLift 886599
  have htrace : WordTrace (prefixWord ++ tailWord_886599) baseStart_886599 baseEnd_886599 := by
    simpa [prefixWord, tailWord_886599, baseEnd_886599] using wordTrace_append hprefix tailTrace_886599
  have hstable : (prefixWord ++ tailWord_886599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886599).length < 2 ^ (prefixWord ++ tailWord_886599).sum := by decide
  have hdescent : baseEnd_886599 < baseStart_886599 := by decide
  rcases family_descends (prefixWord ++ tailWord_886599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886626 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_886626 : Nat := 118140960795 + 886626 * 2 ^ 59
def prefixEnd_886626 : Nat := 4983230072969 + 3 ^ 40 * 886626 * 2
def baseEnd_886626 : Nat := 404680265576314049242211

theorem tailTrace_886626 : CollatzResearch.WordTrace tailWord_886626 prefixEnd_886626 404680265576314049242211 := by
  unfold tailWord_886626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8084476721478225127613933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21558604590608600340303821 8084476721478225127613933)
  ·
    refine ⟨3031678770554334422855225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8084476721478225127613933 3031678770554334422855225)
    ·
      refine ⟨2273759077915750817141419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3031678770554334422855225 2273759077915750817141419)
      ·
        refine ⟨3410638616873626225712129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273759077915750817141419 3410638616873626225712129)
        ·
          refine ⟨2557978962655219669284097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3410638616873626225712129 2557978962655219669284097)
          ·
            refine ⟨1918484221991414751963073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2557978962655219669284097 1918484221991414751963073)
            ·
              refine ⟨1438863166493561063972305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918484221991414751963073 1438863166493561063972305)
              ·
                refine ⟨1079147374870170797979229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438863166493561063972305 1079147374870170797979229)
                ·
                  refine ⟨404680265576314049242211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079147374870170797979229 404680265576314049242211)
                  ·
                    rfl

theorem cell20_886626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_886626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886626 prefixEnd_886626 := by exact prefixLift 886626
  have htrace : WordTrace (prefixWord ++ tailWord_886626) baseStart_886626 baseEnd_886626 := by
    simpa [prefixWord, tailWord_886626, baseEnd_886626] using wordTrace_append hprefix tailTrace_886626
  have hstable : (prefixWord ++ tailWord_886626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886626).length < 2 ^ (prefixWord ++ tailWord_886626).sum := by decide
  have hdescent : baseEnd_886626 < baseStart_886626 := by decide
  rcases family_descends (prefixWord ++ tailWord_886626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886651 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_886651 : Nat := 118140960795 + 886651 * 2 ^ 59
def prefixEnd_886651 : Nat := 4983230072969 + 3 ^ 40 * 886651 * 2
def baseEnd_886651 : Nat := 404691676257525073408775

theorem tailTrace_886651 : CollatzResearch.WordTrace tailWord_886651 prefixEnd_886651 404691676257525073408775 := by
  unfold tailWord_886651
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338818710822329780115807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21559212473881553186743871 32338818710822329780115807)
  ·
    refine ⟨48508228066233494670173711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32338818710822329780115807 48508228066233494670173711)
    ·
      refine ⟨72762342099350242005260567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48508228066233494670173711 72762342099350242005260567)
      ·
        refine ⟨109143513149025363007890851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72762342099350242005260567 109143513149025363007890851)
        ·
          refine ⟨163715269723538044511836277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109143513149025363007890851 163715269723538044511836277)
          ·
            refine ⟨15348306536581691672984651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163715269723538044511836277 15348306536581691672984651)
            ·
              refine ⟨23022459804872537509476977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15348306536581691672984651 23022459804872537509476977)
              ·
                refine ⟨17266844853654403132107733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23022459804872537509476977 17266844853654403132107733)
                ·
                  refine ⟨404691676257525073408775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17266844853654403132107733 404691676257525073408775)
                  ·
                    rfl

theorem cell20_886651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_886651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886651 prefixEnd_886651 := by exact prefixLift 886651
  have htrace : WordTrace (prefixWord ++ tailWord_886651) baseStart_886651 baseEnd_886651 := by
    simpa [prefixWord, tailWord_886651, baseEnd_886651] using wordTrace_append hprefix tailTrace_886651
  have hstable : (prefixWord ++ tailWord_886651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886651).length < 2 ^ (prefixWord ++ tailWord_886651).sum := by decide
  have hdescent : baseEnd_886651 < baseStart_886651 := by decide
  rcases family_descends (prefixWord ++ tailWord_886651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886657 : List Nat := [1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_886657 : Nat := 118140960795 + 886657 * 2 ^ 59
def prefixEnd_886657 : Nat := 4983230072969 + 3 ^ 40 * 886657 * 2
def baseEnd_886657 : Nat := 134898138273671906402917

theorem tailTrace_886657 : CollatzResearch.WordTrace tailWord_886657 prefixEnd_886657 134898138273671906402917 := by
  unfold tailWord_886657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32339037548800592804834225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21559358365867061869889483 32339037548800592804834225)
  ·
    refine ⟨24254278161600444603625669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32339037548800592804834225 24254278161600444603625669)
    ·
      refine ⟨4547677155300083363179813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24254278161600444603625669 4547677155300083363179813)
      ·
        refine ⟨852689466618765630596215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4547677155300083363179813 852689466618765630596215)
        ·
          refine ⟨1279034199928148445894323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852689466618765630596215 1279034199928148445894323)
          ·
            refine ⟨1918551299892222668841485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279034199928148445894323 1918551299892222668841485)
            ·
              refine ⟨719456737459583500815557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918551299892222668841485 719456737459583500815557)
              ·
                refine ⟨134898138273671906402917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719456737459583500815557 134898138273671906402917)
                ·
                  rfl

theorem cell20_886657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_886657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886657 prefixEnd_886657 := by exact prefixLift 886657
  have htrace : WordTrace (prefixWord ++ tailWord_886657) baseStart_886657 baseEnd_886657 := by
    simpa [prefixWord, tailWord_886657, baseEnd_886657] using wordTrace_append hprefix tailTrace_886657
  have hstable : (prefixWord ++ tailWord_886657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886657).length < 2 ^ (prefixWord ++ tailWord_886657).sum := by decide
  have hdescent : baseEnd_886657 < baseStart_886657 := by decide
  rcases family_descends (prefixWord ++ tailWord_886657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886661 : List Nat := [1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_886661 : Nat := 118140960795 + 886661 * 2 ^ 59
def prefixEnd_886661 : Nat := 4983230072969 + 3 ^ 40 * 886661 * 2
def baseEnd_886661 : Nat := 134898746843336494358467

theorem tailTrace_886661 : CollatzResearch.WordTrace tailWord_886661 prefixEnd_886661 134898746843336494358467 := by
  unfold tailWord_886661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32339183440786101487979837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21559455627190734325319891 32339183440786101487979837)
  ·
    refine ⟨12127193790294788057992439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32339183440786101487979837 12127193790294788057992439)
    ·
      refine ⟨18190790685442182086988659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127193790294788057992439 18190790685442182086988659)
      ·
        refine ⟨27286186028163273130482989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18190790685442182086988659 27286186028163273130482989)
        ·
          refine ⟨10232319760561227423931121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27286186028163273130482989 10232319760561227423931121)
          ·
            refine ⟨7674239820420920567948341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10232319760561227423931121 7674239820420920567948341)
            ·
              refine ⟨719459983164461303245157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7674239820420920567948341 719459983164461303245157)
              ·
                refine ⟨134898746843336494358467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719459983164461303245157 134898746843336494358467)
                ·
                  rfl

theorem cell20_886661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_886661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886661 prefixEnd_886661 := by exact prefixLift 886661
  have htrace : WordTrace (prefixWord ++ tailWord_886661) baseStart_886661 baseEnd_886661 := by
    simpa [prefixWord, tailWord_886661, baseEnd_886661] using wordTrace_append hprefix tailTrace_886661
  have hstable : (prefixWord ++ tailWord_886661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886661).length < 2 ^ (prefixWord ++ tailWord_886661).sum := by decide
  have hdescent : baseEnd_886661 < baseStart_886661 := by decide
  rcases family_descends (prefixWord ++ tailWord_886661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886685 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_886685 : Nat := 118140960795 + 886685 * 2 ^ 59
def prefixEnd_886685 : Nat := 4983230072969 + 3 ^ 40 * 886685 * 2
def baseEnd_886685 : Nat := 404707194783972066275303

theorem tailTrace_886685 : CollatzResearch.WordTrace tailWord_886685 prefixEnd_886685 404707194783972066275303 := by
  unfold tailWord_886685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32340058792699153586853509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21560039195132769057902339 32340058792699153586853509)
  ·
    refine ⟨6063761023631091297535033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32340058792699153586853509 6063761023631091297535033)
    ·
      refine ⟨4547820767723318473151275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6063761023631091297535033 4547820767723318473151275)
      ·
        refine ⟨6821731151584977709726913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547820767723318473151275 6821731151584977709726913)
        ·
          refine ⟨5116298363688733282295185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6821731151584977709726913 5116298363688733282295185)
          ·
            refine ⟨3837223772766549961721389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5116298363688733282295185 3837223772766549961721389)
            ·
              refine ⟨1438958914787456235645521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837223772766549961721389 1438958914787456235645521)
              ·
                refine ⟨1079219186090592176734141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438958914787456235645521 1079219186090592176734141)
                ·
                  refine ⟨404707194783972066275303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079219186090592176734141 404707194783972066275303)
                  ·
                    rfl

theorem cell20_886685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_886685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886685 prefixEnd_886685 := by exact prefixLift 886685
  have htrace : WordTrace (prefixWord ++ tailWord_886685) baseStart_886685 baseEnd_886685 := by
    simpa [prefixWord, tailWord_886685, baseEnd_886685] using wordTrace_append hprefix tailTrace_886685
  have hstable : (prefixWord ++ tailWord_886685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886685).length < 2 ^ (prefixWord ++ tailWord_886685).sum := by decide
  have hdescent : baseEnd_886685 < baseStart_886685 := by decide
  rcases family_descends (prefixWord ++ tailWord_886685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886692 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_886692 : Nat := 118140960795 + 886692 * 2 ^ 59
def prefixEnd_886692 : Nat := 4983230072969 + 3 ^ 40 * 886692 * 2
def baseEnd_886692 : Nat := 404710389774711153041941

theorem tailTrace_886692 : CollatzResearch.WordTrace tailWord_886692 prefixEnd_886692 404710389774711153041941 := by
  unfold tailWord_886692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170157051836896891179165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21560209402449195854905553 16170157051836896891179165)
  ·
    refine ⟨6063808894438836334192187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16170157051836896891179165 6063808894438836334192187)
    ·
      refine ⟨9095713341658254501288281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063808894438836334192187 9095713341658254501288281)
      ·
        refine ⟨6821785006243690875966211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9095713341658254501288281 6821785006243690875966211)
        ·
          refine ⟨10232677509365536313949317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821785006243690875966211 10232677509365536313949317)
          ·
            refine ⟨1918627033006038058865497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10232677509365536313949317 1918627033006038058865497)
            ·
              refine ⟨1438970274754528544149123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918627033006038058865497 1438970274754528544149123)
              ·
                refine ⟨2158455412131792816223685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438970274754528544149123 2158455412131792816223685)
                ·
                  refine ⟨404710389774711153041941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158455412131792816223685 404710389774711153041941)
                  ·
                    rfl

theorem cell20_886692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_886692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886692 prefixEnd_886692 := by exact prefixLift 886692
  have htrace : WordTrace (prefixWord ++ tailWord_886692) baseStart_886692 baseEnd_886692 := by
    simpa [prefixWord, tailWord_886692, baseEnd_886692] using wordTrace_append hprefix tailTrace_886692
  have hstable : (prefixWord ++ tailWord_886692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886692).length < 2 ^ (prefixWord ++ tailWord_886692).sum := by decide
  have hdescent : baseEnd_886692 < baseStart_886692 := by decide
  rcases family_descends (prefixWord ++ tailWord_886692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886706 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_886706 : Nat := 118140960795 + 886706 * 2 ^ 59
def prefixEnd_886706 : Nat := 4983230072969 + 3 ^ 40 * 886706 * 2
def baseEnd_886706 : Nat := 404716779756189326575217

theorem tailTrace_886706 : CollatzResearch.WordTrace tailWord_886706 prefixEnd_886706 404716779756189326575217 := by
  unfold tailWord_886706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085206181405768543341993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21560549817082049448911981 8085206181405768543341993)
  ·
    refine ⟨6063904636054326407506495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8085206181405768543341993 6063904636054326407506495)
    ·
      refine ⟨9095856954081489611259743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063904636054326407506495 9095856954081489611259743)
      ·
        refine ⟨13643785431122234416889615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9095856954081489611259743 13643785431122234416889615)
        ·
          refine ⟨20465678146683351625334423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13643785431122234416889615 20465678146683351625334423)
          ·
            refine ⟨30698517220025027438001635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20465678146683351625334423 30698517220025027438001635)
            ·
              refine ⟨46047775830037541157002453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30698517220025027438001635 46047775830037541157002453)
              ·
                refine ⟨1079244746016504870867245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46047775830037541157002453 1079244746016504870867245)
                ·
                  refine ⟨404716779756189326575217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079244746016504870867245 404716779756189326575217)
                  ·
                    rfl

theorem cell20_886706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_886706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886706 prefixEnd_886706 := by exact prefixLift 886706
  have htrace : WordTrace (prefixWord ++ tailWord_886706) baseStart_886706 baseEnd_886706 := by
    simpa [prefixWord, tailWord_886706, baseEnd_886706] using wordTrace_append hprefix tailTrace_886706
  have hstable : (prefixWord ++ tailWord_886706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886706).length < 2 ^ (prefixWord ++ tailWord_886706).sum := by decide
  have hdescent : baseEnd_886706 < baseStart_886706 := by decide
  rcases family_descends (prefixWord ++ tailWord_886706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886713 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_886713 : Nat := 118140960795 + 886713 * 2 ^ 59
def prefixEnd_886713 : Nat := 4983230072969 + 3 ^ 40 * 886713 * 2
def baseEnd_886713 : Nat := 404719974746928413341855

theorem tailTrace_886713 : CollatzResearch.WordTrace tailWord_886713 prefixEnd_886713 404719974746928413341855 := by
  unfold tailWord_886713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32341080036597714368872793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21560720024398476245915195 32341080036597714368872793)
  ·
    refine ⟨24255810027448285776654595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32341080036597714368872793 24255810027448285776654595)
    ·
      refine ⟨36383715041172428664981893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24255810027448285776654595 36383715041172428664981893)
      ·
        refine ⟨6821946570219830374684105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36383715041172428664981893 6821946570219830374684105)
        ·
          refine ⟨5116459927664872781013079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6821946570219830374684105 5116459927664872781013079)
          ·
            refine ⟨7674689891497309171519619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116459927664872781013079 7674689891497309171519619)
            ·
              refine ⟨11512034837245963757279429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674689891497309171519619 11512034837245963757279429)
              ·
                refine ⟨2158506531983618204489893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11512034837245963757279429 2158506531983618204489893)
                ·
                  refine ⟨404719974746928413341855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158506531983618204489893 404719974746928413341855)
                  ·
                    rfl

theorem cell20_886713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_886713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886713 prefixEnd_886713 := by exact prefixLift 886713
  have htrace : WordTrace (prefixWord ++ tailWord_886713) baseStart_886713 baseEnd_886713 := by
    simpa [prefixWord, tailWord_886713, baseEnd_886713] using wordTrace_append hprefix tailTrace_886713
  have hstable : (prefixWord ++ tailWord_886713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886713).length < 2 ^ (prefixWord ++ tailWord_886713).sum := by decide
  have hdescent : baseEnd_886713 < baseStart_886713 := by decide
  rcases family_descends (prefixWord ++ tailWord_886713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886716 : List Nat := [2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_886716 : Nat := 118140960795 + 886716 * 2 ^ 59
def prefixEnd_886716 : Nat := 4983230072969 + 3 ^ 40 * 886716 * 2
def baseEnd_886716 : Nat := 134907114676224578747281

theorem tailTrace_886716 : CollatzResearch.WordTrace tailWord_886716 prefixEnd_886716 134907114676224578747281 := by
  unfold tailWord_886716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170594727793422940616001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21560792970391230587488001 16170594727793422940616001)
  ·
    refine ⟨12127946045845067205462001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16170594727793422940616001 12127946045845067205462001)
    ·
      refine ⟨9095959534383800404096501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12127946045845067205462001 9095959534383800404096501)
      ·
        refine ⟨852746206348481287884047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9095959534383800404096501 852746206348481287884047)
        ·
          refine ⟨1279119309522721931826071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852746206348481287884047 1279119309522721931826071)
          ·
            refine ⟨1918678964284082897739107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279119309522721931826071 1918678964284082897739107)
            ·
              refine ⟨2878018446426124346608661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918678964284082897739107 2878018446426124346608661)
              ·
                refine ⟨134907114676224578747281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2878018446426124346608661 134907114676224578747281)
                ·
                  rfl

theorem cell20_886716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_886716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886716 prefixEnd_886716 := by exact prefixLift 886716
  have htrace : WordTrace (prefixWord ++ tailWord_886716) baseStart_886716 baseEnd_886716 := by
    simpa [prefixWord, tailWord_886716, baseEnd_886716] using wordTrace_append hprefix tailTrace_886716
  have hstable : (prefixWord ++ tailWord_886716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886716).length < 2 ^ (prefixWord ++ tailWord_886716).sum := by decide
  have hdescent : baseEnd_886716 < baseStart_886716 := by decide
  rcases family_descends (prefixWord ++ tailWord_886716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886720 : List Nat := [2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_886720 : Nat := 118140960795 + 886720 * 2 ^ 59
def prefixEnd_886720 : Nat := 4983230072969 + 3 ^ 40 * 886720 * 2
def baseEnd_886720 : Nat := 134907723245889166702831

theorem tailTrace_886720 : CollatzResearch.WordTrace tailWord_886720 prefixEnd_886720 134907723245889166702831 := by
  unfold tailWord_886720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170667673786177282188807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21560890231714903042918409 16170667673786177282188807)
  ·
    refine ⟨24256001510679265923283211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170667673786177282188807 24256001510679265923283211)
    ·
      refine ⟨36384002266018898884924817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24256001510679265923283211 36384002266018898884924817)
      ·
        refine ⟨27288001699514174163693613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36384002266018898884924817 27288001699514174163693613)
        ·
          refine ⟨10233000637317815311385105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27288001699514174163693613 10233000637317815311385105)
          ·
            refine ⟨7674750477988361483538829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10233000637317815311385105 7674750477988361483538829)
            ·
              refine ⟨2878031429245635556327061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7674750477988361483538829 2878031429245635556327061)
              ·
                refine ⟨134907723245889166702831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2878031429245635556327061 134907723245889166702831)
                ·
                  rfl

theorem cell20_886720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_886720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886720 prefixEnd_886720 := by exact prefixLift 886720
  have htrace : WordTrace (prefixWord ++ tailWord_886720) baseStart_886720 baseEnd_886720 := by
    simpa [prefixWord, tailWord_886720, baseEnd_886720] using wordTrace_append hprefix tailTrace_886720
  have hstable : (prefixWord ++ tailWord_886720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886720).length < 2 ^ (prefixWord ++ tailWord_886720).sum := by decide
  have hdescent : baseEnd_886720 < baseStart_886720 := by decide
  rcases family_descends (prefixWord ++ tailWord_886720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886744 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_886744 : Nat := 118140960795 + 886744 * 2 ^ 59
def prefixEnd_886744 : Nat := 4983230072969 + 3 ^ 40 * 886744 * 2
def baseEnd_886744 : Nat := 404734123991630083308395

theorem tailTrace_886744 : CollatzResearch.WordTrace tailWord_886744 prefixEnd_886744 404734123991630083308395 := by
  unfold tailWord_886744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171105349742703331625643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21561473799656937775500857 16171105349742703331625643)
  ·
    refine ⟨24256658024614054997438465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16171105349742703331625643 24256658024614054997438465)
    ·
      refine ⟨18192493518460541248078849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24256658024614054997438465 18192493518460541248078849)
      ·
        refine ⟨13644370138845405936059137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18192493518460541248078849 13644370138845405936059137)
        ·
          refine ⟨10233277604134054452044353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13644370138845405936059137 10233277604134054452044353)
          ·
            refine ⟨7674958203100540839033265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10233277604134054452044353 7674958203100540839033265)
            ·
              refine ⟨5756218652325405629274949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7674958203100540839033265 5756218652325405629274949)
              ·
                refine ⟨1079290997311013555489053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5756218652325405629274949 1079290997311013555489053)
                ·
                  refine ⟨404734123991630083308395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079290997311013555489053 404734123991630083308395)
                  ·
                    rfl

theorem cell20_886744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_886744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886744 prefixEnd_886744 := by exact prefixLift 886744
  have htrace : WordTrace (prefixWord ++ tailWord_886744) baseStart_886744 baseEnd_886744 := by
    simpa [prefixWord, tailWord_886744, baseEnd_886744] using wordTrace_append hprefix tailTrace_886744
  have hstable : (prefixWord ++ tailWord_886744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886744).length < 2 ^ (prefixWord ++ tailWord_886744).sum := by decide
  have hdescent : baseEnd_886744 < baseStart_886744 := by decide
  rcases family_descends (prefixWord ++ tailWord_886744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886803 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_886803 : Nat := 118140960795 + 886803 * 2 ^ 59
def prefixEnd_886803 : Nat := 4983230072969 + 3 ^ 40 * 886803 * 2
def baseEnd_886803 : Nat := 404761053199288100341487

theorem tailTrace_886803 : CollatzResearch.WordTrace tailWord_886803 prefixEnd_886803 404761053199288100341487 := by
  unfold tailWord_886803
  simp only [CollatzResearch.WordTrace]
  refine ⟨32344362606271659739649063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21562908404181106493099375 32344362606271659739649063)
  ·
    refine ⟨48516543909407489609473595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32344362606271659739649063 48516543909407489609473595)
    ·
      refine ⟨72774815864111234414210393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48516543909407489609473595 72774815864111234414210393)
      ·
        refine ⟨54581111898083425810657795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72774815864111234414210393 54581111898083425810657795)
        ·
          refine ⟨81871667847125138715986693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54581111898083425810657795 81871667847125138715986693)
          ·
            refine ⟨15350937721335963509247505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81871667847125138715986693 15350937721335963509247505)
            ·
              refine ⟨11513203291001972631935629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15350937721335963509247505 11513203291001972631935629)
              ·
                refine ⟨4317451234125739736975861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11513203291001972631935629 4317451234125739736975861)
                ·
                  refine ⟨404761053199288100341487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4317451234125739736975861 404761053199288100341487)
                  ·
                    rfl

theorem cell20_886803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_886803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886803 prefixEnd_886803 := by exact prefixLift 886803
  have htrace : WordTrace (prefixWord ++ tailWord_886803) baseStart_886803 baseEnd_886803 := by
    simpa [prefixWord, tailWord_886803, baseEnd_886803] using wordTrace_append hprefix tailTrace_886803
  have hstable : (prefixWord ++ tailWord_886803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886803).length < 2 ^ (prefixWord ++ tailWord_886803).sum := by decide
  have hdescent : baseEnd_886803 < baseStart_886803 := by decide
  rcases family_descends (prefixWord ++ tailWord_886803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886813 : List Nat := [1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_886813 : Nat := 118140960795 + 886813 * 2 ^ 59
def prefixEnd_886813 : Nat := 4983230072969 + 3 ^ 40 * 886813 * 2
def baseEnd_886813 : Nat := 134921872490590836669371

theorem tailTrace_886813 : CollatzResearch.WordTrace tailWord_886813 prefixEnd_886813 134921872490590836669371 := by
  unfold tailWord_886813
  simp only [CollatzResearch.WordTrace]
  refine ⟨32344727336235431447513093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21563151557490287631675395 32344727336235431447513093)
  ·
    refine ⟨6064636375544143396408705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32344727336235431447513093 6064636375544143396408705)
    ·
      refine ⟨4548477281658107547306529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6064636375544143396408705 4548477281658107547306529)
      ·
        refine ⟨3411357961243580660479897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4548477281658107547306529 3411357961243580660479897)
        ·
          refine ⟨2558518470932685495359923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411357961243580660479897 2558518470932685495359923)
          ·
            refine ⟨3837777706399028243039885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558518470932685495359923 3837777706399028243039885)
            ·
              refine ⟨1439166639899635591139957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837777706399028243039885 1439166639899635591139957)
              ·
                refine ⟨134921872490590836669371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439166639899635591139957 134921872490590836669371)
                ·
                  rfl

theorem cell20_886813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_886813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886813 prefixEnd_886813 := by exact prefixLift 886813
  have htrace : WordTrace (prefixWord ++ tailWord_886813) baseStart_886813 baseEnd_886813 := by
    simpa [prefixWord, tailWord_886813, baseEnd_886813] using wordTrace_append hprefix tailTrace_886813
  have hstable : (prefixWord ++ tailWord_886813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886813).length < 2 ^ (prefixWord ++ tailWord_886813).sum := by decide
  have hdescent : baseEnd_886813 < baseStart_886813 := by decide
  rcases family_descends (prefixWord ++ tailWord_886813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886823 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_886823 : Nat := 118140960795 + 886823 * 2 ^ 59
def prefixEnd_886823 : Nat := 4983230072969 + 3 ^ 40 * 886823 * 2
def baseEnd_886823 : Nat := 404770181744256919674739

theorem tailTrace_886823 : CollatzResearch.WordTrace tailWord_886823 prefixEnd_886823 404770181744256919674739 := by
  unfold tailWord_886823
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345092066199203155377123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21563394710799468770251415 32345092066199203155377123)
  ·
    refine ⟨48517638099298804733065685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32345092066199203155377123 48517638099298804733065685)
    ·
      refine ⟨1137132142952315735931227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48517638099298804733065685 1137132142952315735931227)
      ·
        refine ⟨1705698214428473603896841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137132142952315735931227 1705698214428473603896841)
        ·
          refine ⟨1279273660821355202922631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705698214428473603896841 1279273660821355202922631)
          ·
            refine ⟨1918910491232032804383947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279273660821355202922631 1918910491232032804383947)
            ·
              refine ⟨2878365736848049206575921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918910491232032804383947 2878365736848049206575921)
              ·
                refine ⟨2158774302636036904931941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878365736848049206575921 2158774302636036904931941)
                ·
                  refine ⟨404770181744256919674739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2158774302636036904931941 404770181744256919674739)
                  ·
                    rfl

theorem cell20_886823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_886823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886823 prefixEnd_886823 := by exact prefixLift 886823
  have htrace : WordTrace (prefixWord ++ tailWord_886823) baseStart_886823 baseEnd_886823 := by
    simpa [prefixWord, tailWord_886823, baseEnd_886823] using wordTrace_append hprefix tailTrace_886823
  have hstable : (prefixWord ++ tailWord_886823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886823).length < 2 ^ (prefixWord ++ tailWord_886823).sum := by decide
  have hdescent : baseEnd_886823 < baseStart_886823 := by decide
  rcases family_descends (prefixWord ++ tailWord_886823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886830 : List Nat := [4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_886830 : Nat := 118140960795 + 886830 * 2 ^ 59
def prefixEnd_886830 : Nat := 4983230072969 + 3 ^ 40 * 886830 * 2
def baseEnd_886830 : Nat := 134924458911665335480459

theorem tailTrace_886830 : CollatzResearch.WordTrace tailWord_886830 prefixEnd_886830 134924458911665335480459 := by
  unfold tailWord_886830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043168422146730418860243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21563564918115895567254629 4043168422146730418860243)
  ·
    refine ⟨6064752633220095628290365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4043168422146730418860243 6064752633220095628290365)
    ·
      refine ⟨2274282237457535860608887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6064752633220095628290365 2274282237457535860608887)
      ·
        refine ⟨3411423356186303790913331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274282237457535860608887 3411423356186303790913331)
        ·
          refine ⟨5117135034279455686369997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411423356186303790913331 5117135034279455686369997)
          ·
            refine ⟨1918925637854795882388749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5117135034279455686369997 1918925637854795882388749)
            ·
              refine ⟨719597114195548455895781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918925637854795882388749 719597114195548455895781)
              ·
                refine ⟨134924458911665335480459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719597114195548455895781 134924458911665335480459)
                ·
                  rfl

theorem cell20_886830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_886830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886830 prefixEnd_886830 := by exact prefixLift 886830
  have htrace : WordTrace (prefixWord ++ tailWord_886830) baseStart_886830 baseEnd_886830 := by
    simpa [prefixWord, tailWord_886830, baseEnd_886830] using wordTrace_append hprefix tailTrace_886830
  have hstable : (prefixWord ++ tailWord_886830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886830).length < 2 ^ (prefixWord ++ tailWord_886830).sum := by decide
  have hdescent : baseEnd_886830 < baseStart_886830 := by decide
  rcases family_descends (prefixWord ++ tailWord_886830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886861 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 2]
def baseStart_886861 : Nat := 118140960795 + 886861 * 2 ^ 59
def prefixEnd_886861 : Nat := 4983230072969 + 3 ^ 40 * 886861 * 2
def baseEnd_886861 : Nat := 404787525979697676407917

theorem tailTrace_886861 : CollatzResearch.WordTrace tailWord_886861 prefixEnd_886861 404787525979697676407917 := by
  unfold tailWord_886861
  simp only [CollatzResearch.WordTrace]
  refine ⟨32346478040061535645260437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21564318693374357096840291 32346478040061535645260437)
  ·
    refine ⟨1516241158127884483371583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32346478040061535645260437 1516241158127884483371583)
    ·
      refine ⟨2274361737191826725057375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516241158127884483371583 2274361737191826725057375)
      ·
        refine ⟨3411542605787740087586063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274361737191826725057375 3411542605787740087586063)
        ·
          refine ⟨5117313908681610131379095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411542605787740087586063 5117313908681610131379095)
          ·
            refine ⟨7675970863022415197068643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117313908681610131379095 7675970863022415197068643)
            ·
              refine ⟨11513956294533622795602965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675970863022415197068643 11513956294533622795602965)
              ·
                refine ⟨539716701306263568543889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11513956294533622795602965 539716701306263568543889)
                ·
                  refine ⟨404787525979697676407917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539716701306263568543889 404787525979697676407917)
                  ·
                    rfl

theorem cell20_886861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_886861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886861 prefixEnd_886861 := by exact prefixLift 886861
  have htrace : WordTrace (prefixWord ++ tailWord_886861) baseStart_886861 baseEnd_886861 := by
    simpa [prefixWord, tailWord_886861, baseEnd_886861] using wordTrace_append hprefix tailTrace_886861
  have hstable : (prefixWord ++ tailWord_886861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886861).length < 2 ^ (prefixWord ++ tailWord_886861).sum := by decide
  have hdescent : baseEnd_886861 < baseStart_886861 := by decide
  rcases family_descends (prefixWord ++ tailWord_886861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886920 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_886920 : Nat := 118140960795 + 886920 * 2 ^ 59
def prefixEnd_886920 : Nat := 4983230072969 + 3 ^ 40 * 886920 * 2
def baseEnd_886920 : Nat := 404814455187355693441009

theorem tailTrace_886920 : CollatzResearch.WordTrace tailWord_886920 prefixEnd_886920 404814455187355693441009 := by
  unfold tailWord_886920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174314973423894360829107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21565753297898525814438809 16174314973423894360829107)
  ·
    refine ⟨24261472460135841541243661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16174314973423894360829107 24261472460135841541243661)
    ·
      refine ⟨9098052172550940577966373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24261472460135841541243661 9098052172550940577966373)
      ·
        refine ⟨1705884782353301358368695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9098052172550940577966373 1705884782353301358368695)
        ·
          refine ⟨2558827173529952037553043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705884782353301358368695 2558827173529952037553043)
          ·
            refine ⟨3838240760294928056329565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558827173529952037553043 3838240760294928056329565)
            ·
              refine ⟨1439340285110598021123587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3838240760294928056329565 1439340285110598021123587)
              ·
                refine ⟨2159010427665897031685381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439340285110598021123587 2159010427665897031685381)
                ·
                  refine ⟨404814455187355693441009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159010427665897031685381 404814455187355693441009)
                  ·
                    rfl

theorem cell20_886920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_886920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886920 prefixEnd_886920 := by exact prefixLift 886920
  have htrace : WordTrace (prefixWord ++ tailWord_886920) baseStart_886920 baseEnd_886920 := by
    simpa [prefixWord, tailWord_886920, baseEnd_886920] using wordTrace_append hprefix tailTrace_886920
  have hstable : (prefixWord ++ tailWord_886920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886920).length < 2 ^ (prefixWord ++ tailWord_886920).sum := by decide
  have hdescent : baseEnd_886920 < baseStart_886920 := by decide
  rcases family_descends (prefixWord ++ tailWord_886920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886964 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_886964 : Nat := 118140960795 + 886964 * 2 ^ 59
def prefixEnd_886964 : Nat := 4983230072969 + 3 ^ 40 * 886964 * 2
def baseEnd_886964 : Nat := 404834537986287095974163

theorem tailTrace_886964 : CollatzResearch.WordTrace tailWord_886964 prefixEnd_886964 404834537986287095974163 := by
  unfold tailWord_886964
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175117379344192118129973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21566823172458922824173297 16175117379344192118129973)
  ·
    refine ⟨1516417254313518011074685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16175117379344192118129973 1516417254313518011074685)
    ·
      refine ⟨568656470367569254153007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1516417254313518011074685 568656470367569254153007)
      ·
        refine ⟨852984705551353881229511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568656470367569254153007 852984705551353881229511)
        ·
          refine ⟨1279477058327030821844267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852984705551353881229511 1279477058327030821844267)
          ·
            refine ⟨1919215587490546232766401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279477058327030821844267 1919215587490546232766401)
            ·
              refine ⟨1439411690617909674574801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919215587490546232766401 1439411690617909674574801)
              ·
                refine ⟨1079558767963432255931101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439411690617909674574801 1079558767963432255931101)
                ·
                  refine ⟨404834537986287095974163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079558767963432255931101 404834537986287095974163)
                  ·
                    rfl

theorem cell20_886964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_886964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886964 prefixEnd_886964 := by exact prefixLift 886964
  have htrace : WordTrace (prefixWord ++ tailWord_886964) baseStart_886964 baseEnd_886964 := by
    simpa [prefixWord, tailWord_886964, baseEnd_886964] using wordTrace_append hprefix tailTrace_886964
  have hstable : (prefixWord ++ tailWord_886964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886964).length < 2 ^ (prefixWord ++ tailWord_886964).sum := by decide
  have hdescent : baseEnd_886964 < baseStart_886964 := by decide
  rcases family_descends (prefixWord ++ tailWord_886964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886965 : List Nat := [1, 3, 3, 4, 1, 8]
def baseStart_886965 : Nat := 118140960795 + 886965 * 2 ^ 59
def prefixEnd_886965 : Nat := 4983230072969 + 3 ^ 40 * 886965 * 2
def baseEnd_886965 : Nat := 14993888681982797664475

theorem tailTrace_886965 : CollatzResearch.WordTrace tailWord_886965 prefixEnd_886965 14993888681982797664475 := by
  unfold tailWord_886965
  simp only [CollatzResearch.WordTrace]
  refine ⟨32350271231684761407046349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21566847487789840938030899 32350271231684761407046349)
  ·
    refine ⟨12131351711881785527642381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32350271231684761407046349 12131351711881785527642381)
    ·
      refine ⟨4549256891955669572865893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12131351711881785527642381 4549256891955669572865893)
      ·
        refine ⟨852985667241688044912355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4549256891955669572865893 852985667241688044912355)
        ·
          refine ⟨1279478500862532067368533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852985667241688044912355 1279478500862532067368533)
          ·
            refine ⟨14993888681982797664475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1279478500862532067368533 14993888681982797664475)
            ·
              rfl

theorem cell20_886965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 8].length) (baseStart_886965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_886965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_886965 prefixEnd_886965 := by exact prefixLift 886965
  have htrace : WordTrace (prefixWord ++ tailWord_886965) baseStart_886965 baseEnd_886965 := by
    simpa [prefixWord, tailWord_886965, baseEnd_886965] using wordTrace_append hprefix tailTrace_886965
  have hstable : (prefixWord ++ tailWord_886965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886965).length < 2 ^ (prefixWord ++ tailWord_886965).sum := by decide
  have hdescent : baseEnd_886965 < baseStart_886965 := by decide
  rcases family_descends (prefixWord ++ tailWord_886965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887013 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 2]
def baseStart_887013 : Nat := 118140960795 + 887013 * 2 ^ 59
def prefixEnd_887013 : Nat := 4983230072969 + 3 ^ 40 * 887013 * 2
def baseEnd_887013 : Nat := 404856902921460703340629

theorem tailTrace_887013 : CollatzResearch.WordTrace tailWord_887013 prefixEnd_887013 404856902921460703340629 := by
  unfold tailWord_887013
  simp only [CollatzResearch.WordTrace]
  refine ⟨32352021935510865604793693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21568014623673910403195795 32352021935510865604793693)
  ·
    refine ⟨12132008225816574601797635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32352021935510865604793693 12132008225816574601797635)
    ·
      refine ⟨18198012338724861902696453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132008225816574601797635 18198012338724861902696453)
      ·
        refine ⟨3412127313510911606755585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18198012338724861902696453 3412127313510911606755585)
        ·
          refine ⟨2559095485133183705066689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3412127313510911606755585 2559095485133183705066689)
          ·
            refine ⟨1919321613849887778800017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559095485133183705066689 1919321613849887778800017)
            ·
              refine ⟨1439491210387415834100013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919321613849887778800017 1439491210387415834100013)
              ·
                refine ⟨539809203895280937787505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439491210387415834100013 539809203895280937787505)
                ·
                  refine ⟨404856902921460703340629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539809203895280937787505 404856902921460703340629)
                  ·
                    rfl

theorem cell20_887013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_887013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887013 prefixEnd_887013 := by exact prefixLift 887013
  have htrace : WordTrace (prefixWord ++ tailWord_887013) baseStart_887013 baseEnd_887013 := by
    simpa [prefixWord, tailWord_887013, baseEnd_887013] using wordTrace_append hprefix tailTrace_887013
  have hstable : (prefixWord ++ tailWord_887013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887013).length < 2 ^ (prefixWord ++ tailWord_887013).sum := by decide
  have hdescent : baseEnd_887013 < baseStart_887013 := by decide
  rcases family_descends (prefixWord ++ tailWord_887013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887034 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_887034 : Nat := 118140960795 + 887034 * 2 ^ 59
def prefixEnd_887034 : Nat := 4983230072969 + 3 ^ 40 * 887034 * 2
def baseEnd_887034 : Nat := 404866487893677963640543

theorem tailTrace_887034 : CollatzResearch.WordTrace tailWord_887034 prefixEnd_887034 404866487893677963640543 := by
  unfold tailWord_887034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088196967108696547827039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21568525245623190794205437 8088196967108696547827039)
  ·
    refine ⟨12132295450663044821740559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088196967108696547827039 12132295450663044821740559)
    ·
      refine ⟨18198443175994567232610839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132295450663044821740559 18198443175994567232610839)
      ·
        refine ⟨27297664763991850848916259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18198443175994567232610839 27297664763991850848916259)
        ·
          refine ⟨40946497145987776273374389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27297664763991850848916259 40946497145987776273374389)
          ·
            refine ⟨3838734107436354025628849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40946497145987776273374389 3838734107436354025628849)
            ·
              refine ⟨2879050580577265519221637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838734107436354025628849 2879050580577265519221637)
              ·
                refine ⟨539821983858237284854057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2879050580577265519221637 539821983858237284854057)
                ·
                  refine ⟨404866487893677963640543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539821983858237284854057 404866487893677963640543)
                  ·
                    rfl

theorem cell20_887034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_887034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887034 prefixEnd_887034 := by exact prefixLift 887034
  have htrace : WordTrace (prefixWord ++ tailWord_887034) baseStart_887034 baseEnd_887034 := by
    simpa [prefixWord, tailWord_887034, baseEnd_887034] using wordTrace_append hprefix tailTrace_887034
  have hstable : (prefixWord ++ tailWord_887034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887034).length < 2 ^ (prefixWord ++ tailWord_887034).sum := by decide
  have hdescent : baseEnd_887034 < baseStart_887034 := by decide
  rcases family_descends (prefixWord ++ tailWord_887034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887044 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_887044 : Nat := 118140960795 + 887044 * 2 ^ 59
def prefixEnd_887044 : Nat := 4983230072969 + 3 ^ 40 * 887044 * 2
def baseEnd_887044 : Nat := 404871052166162373307169

theorem tailTrace_887044 : CollatzResearch.WordTrace tailWord_887044 prefixEnd_887044 404871052166162373307169 := by
  unfold tailWord_887044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176576299199278949586093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21568768398932371932781457 16176576299199278949586093)
  ·
    refine ⟨6066216112199729606094785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16176576299199278949586093 6066216112199729606094785)
    ·
      refine ⟨4549662084149797204571089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6066216112199729606094785 4549662084149797204571089)
      ·
        refine ⟨3412246563112347903428317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4549662084149797204571089 3412246563112347903428317)
        ·
          refine ⟨1279592461167130463785619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3412246563112347903428317 1279592461167130463785619)
          ·
            refine ⟨1919388691750695695678429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279592461167130463785619 1919388691750695695678429)
            ·
              refine ⟨719770759406510885879411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919388691750695695678429 719770759406510885879411)
              ·
                refine ⟨1079656139109766328819117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719770759406510885879411 1079656139109766328819117)
                ·
                  refine ⟨404871052166162373307169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079656139109766328819117 404871052166162373307169)
                  ·
                    rfl

theorem cell20_887044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_887044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887044 prefixEnd_887044 := by exact prefixLift 887044
  have htrace : WordTrace (prefixWord ++ tailWord_887044) baseStart_887044 baseEnd_887044 := by
    simpa [prefixWord, tailWord_887044, baseEnd_887044] using wordTrace_append hprefix tailTrace_887044
  have hstable : (prefixWord ++ tailWord_887044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887044).length < 2 ^ (prefixWord ++ tailWord_887044).sum := by decide
  have hdescent : baseEnd_887044 < baseStart_887044 := by decide
  rcases family_descends (prefixWord ++ tailWord_887044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887085 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 2]
def baseStart_887085 : Nat := 118140960795 + 887085 * 2 ^ 59
def prefixEnd_887085 : Nat := 4983230072969 + 3 ^ 40 * 887085 * 2
def baseEnd_887085 : Nat := 404889765683348452940335

theorem tailTrace_887085 : CollatzResearch.WordTrace tailWord_887085 prefixEnd_887085 404889765683348452940335 := by
  unfold tailWord_887085
  simp only [CollatzResearch.WordTrace]
  refine ⟨32354647991250021901414709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21569765327500014600943139 32354647991250021901414709)
  ·
    refine ⟨3033248249179689553257629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32354647991250021901414709 3033248249179689553257629)
    ·
      refine ⟨1137468093442383582471611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3033248249179689553257629 1137468093442383582471611)
      ·
        refine ⟨1706202140163575373707417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137468093442383582471611 1706202140163575373707417)
        ·
          refine ⟨1279651605122681530280563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706202140163575373707417 1279651605122681530280563)
          ·
            refine ⟨1919477407684022295420845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279651605122681530280563 1919477407684022295420845)
            ·
              refine ⟨719804027881508360782817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919477407684022295420845 719804027881508360782817)
              ·
                refine ⟨539853020911131270587113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719804027881508360782817 539853020911131270587113)
                ·
                  refine ⟨404889765683348452940335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539853020911131270587113 404889765683348452940335)
                  ·
                    rfl

theorem cell20_887085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_887085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887085 prefixEnd_887085 := by exact prefixLift 887085
  have htrace : WordTrace (prefixWord ++ tailWord_887085) baseStart_887085 baseEnd_887085 := by
    simpa [prefixWord, tailWord_887085, baseEnd_887085] using wordTrace_append hprefix tailTrace_887085
  have hstable : (prefixWord ++ tailWord_887085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887085).length < 2 ^ (prefixWord ++ tailWord_887085).sum := by decide
  have hdescent : baseEnd_887085 < baseStart_887085 := by decide
  rcases family_descends (prefixWord ++ tailWord_887085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887089 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 4]
def baseStart_887089 : Nat := 118140960795 + 887089 * 2 ^ 59
def prefixEnd_887089 : Nat := 4983230072969 + 3 ^ 40 * 887089 * 2
def baseEnd_887089 : Nat := 404891591392342216806985

theorem tailTrace_887089 : CollatzResearch.WordTrace tailWord_887089 prefixEnd_887089 404891591392342216806985 := by
  unfold tailWord_887089
  simp only [CollatzResearch.WordTrace]
  refine ⟨32354793883235530584560321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21569862588823687056373547 32354793883235530584560321)
  ·
    refine ⟨24266095412426647938420241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32354793883235530584560321 24266095412426647938420241)
    ·
      refine ⟨18199571559319985953815181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24266095412426647938420241 18199571559319985953815181)
      ·
        refine ⟨6824839334744994732680693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18199571559319985953815181 6824839334744994732680693)
        ·
          refine ⟨639828687632343256188815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6824839334744994732680693 639828687632343256188815)
          ·
            refine ⟨959743031448514884283223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639828687632343256188815 959743031448514884283223)
            ·
              refine ⟨1439614547172772326424835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959743031448514884283223 1439614547172772326424835)
              ·
                refine ⟨2159421820759158489637253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439614547172772326424835 2159421820759158489637253)
                ·
                  refine ⟨404891591392342216806985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159421820759158489637253 404891591392342216806985)
                  ·
                    rfl

theorem cell20_887089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_887089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887089 prefixEnd_887089 := by exact prefixLift 887089
  have htrace : WordTrace (prefixWord ++ tailWord_887089) baseStart_887089 baseEnd_887089 := by
    simpa [prefixWord, tailWord_887089, baseEnd_887089] using wordTrace_append hprefix tailTrace_887089
  have hstable : (prefixWord ++ tailWord_887089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887089).length < 2 ^ (prefixWord ++ tailWord_887089).sum := by decide
  have hdescent : baseEnd_887089 < baseStart_887089 := by decide
  rcases family_descends (prefixWord ++ tailWord_887089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887100 : List Nat := [2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_887100 : Nat := 118140960795 + 887100 * 2 ^ 59
def prefixEnd_887100 : Nat := 4983230072969 + 3 ^ 40 * 887100 * 2
def baseEnd_887100 : Nat := 134965537364025022480091

theorem tailTrace_887100 : CollatzResearch.WordTrace tailWord_887100 prefixEnd_887100 134965537364025022480091 := by
  unfold tailWord_887100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16177597543097839731605377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21570130057463786308807169 16177597543097839731605377)
  ·
    refine ⟨12133198157323379798704033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16177597543097839731605377 12133198157323379798704033)
    ·
      refine ⟨9099898617992534849028025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12133198157323379798704033 9099898617992534849028025)
      ·
        refine ⟨6824923963494401136771019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9099898617992534849028025 6824923963494401136771019)
        ·
          refine ⟨10237385945241601705156529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824923963494401136771019 10237385945241601705156529)
          ·
            refine ⟨7678039458931201278867397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10237385945241601705156529 7678039458931201278867397)
            ·
              refine ⟨1439632398549600239787637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7678039458931201278867397 1439632398549600239787637)
              ·
                refine ⟨134965537364025022480091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439632398549600239787637 134965537364025022480091)
                ·
                  rfl

theorem cell20_887100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_887100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887100 prefixEnd_887100 := by exact prefixLift 887100
  have htrace : WordTrace (prefixWord ++ tailWord_887100) baseStart_887100 baseEnd_887100 := by
    simpa [prefixWord, tailWord_887100, baseEnd_887100] using wordTrace_append hprefix tailTrace_887100
  have hstable : (prefixWord ++ tailWord_887100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887100).length < 2 ^ (prefixWord ++ tailWord_887100).sum := by decide
  have hdescent : baseEnd_887100 < baseStart_887100 := by decide
  rcases family_descends (prefixWord ++ tailWord_887100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887138 : List Nat := [3, 3, 2, 1, 1, 10]
def baseStart_887138 : Nat := 118140960795 + 887138 * 2 ^ 59
def prefixEnd_887138 : Nat := 4983230072969 + 3 ^ 40 * 887138 * 2
def baseEnd_887138 : Nat := 14996813197315400895313

theorem tailTrace_887138 : CollatzResearch.WordTrace tailWord_887138 prefixEnd_887138 14996813197315400895313 := by
  unfold tailWord_887138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089145265014502988273517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21571054040038674635396045 8089145265014502988273517)
  ·
    refine ⟨3033429474380438620602569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8089145265014502988273517 3033429474380438620602569)
    ·
      refine ⟨2275072105785328965451927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3033429474380438620602569 2275072105785328965451927)
      ·
        refine ⟨3412608158677993448177891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275072105785328965451927 3412608158677993448177891)
        ·
          refine ⟨5118912238016990172266837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412608158677993448177891 5118912238016990172266837)
          ·
            refine ⟨14996813197315400895313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5118912238016990172266837 14996813197315400895313)
            ·
              rfl

theorem cell20_887138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 10].length) (baseStart_887138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887138 prefixEnd_887138 := by exact prefixLift 887138
  have htrace : WordTrace (prefixWord ++ tailWord_887138) baseStart_887138 baseEnd_887138 := by
    simpa [prefixWord, tailWord_887138, baseEnd_887138] using wordTrace_append hprefix tailTrace_887138
  have hstable : (prefixWord ++ tailWord_887138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887138).length < 2 ^ (prefixWord ++ tailWord_887138).sum := by decide
  have hdescent : baseEnd_887138 < baseStart_887138 := by decide
  rcases family_descends (prefixWord ++ tailWord_887138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887144 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_887144 : Nat := 118140960795 + 887144 * 2 ^ 59
def prefixEnd_887144 : Nat := 4983230072969 + 3 ^ 40 * 887144 * 2
def baseEnd_887144 : Nat := 404916694891006469973427

theorem tailTrace_887144 : CollatzResearch.WordTrace tailWord_887144 prefixEnd_887144 404916694891006469973427 := by
  unfold tailWord_887144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16178399949018137488906243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21571199932024183318541657 16178399949018137488906243)
  ·
    refine ⟨24267599923527206233359365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16178399949018137488906243 24267599923527206233359365)
    ·
      refine ⟨4550174985661351168754881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24267599923527206233359365 4550174985661351168754881)
      ·
        refine ⟨3412631239246013376566161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550174985661351168754881 3412631239246013376566161)
        ·
          refine ⟨2559473429434510032424621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3412631239246013376566161 2559473429434510032424621)
          ·
            refine ⟨959802536037941262159233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2559473429434510032424621 959802536037941262159233)
            ·
              refine ⟨719851902028455946619425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959802536037941262159233 719851902028455946619425)
              ·
                refine ⟨539888926521341959964569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719851902028455946619425 539888926521341959964569)
                ·
                  refine ⟨404916694891006469973427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539888926521341959964569 404916694891006469973427)
                  ·
                    rfl

theorem cell20_887144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_887144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887144 prefixEnd_887144 := by exact prefixLift 887144
  have htrace : WordTrace (prefixWord ++ tailWord_887144) baseStart_887144 baseEnd_887144 := by
    simpa [prefixWord, tailWord_887144, baseEnd_887144] using wordTrace_append hprefix tailTrace_887144
  have hstable : (prefixWord ++ tailWord_887144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887144).length < 2 ^ (prefixWord ++ tailWord_887144).sum := by decide
  have hdescent : baseEnd_887144 < baseStart_887144 := by decide
  rcases family_descends (prefixWord ++ tailWord_887144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887159 : List Nat := [1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_887159 : Nat := 118140960795 + 887159 * 2 ^ 59
def prefixEnd_887159 : Nat := 4983230072969 + 3 ^ 40 * 887159 * 2
def baseEnd_887159 : Nat := 134974513766577694824455

theorem tailTrace_887159 : CollatzResearch.WordTrace tailWord_887159 prefixEnd_887159 134974513766577694824455 := by
  unfold tailWord_887159
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357346992981932539608531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21571564661987955026405687 32357346992981932539608531)
  ·
    refine ⟨48536020489472898809412797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32357346992981932539608531 48536020489472898809412797)
    ·
      refine ⟨18201007683552337053529799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48536020489472898809412797 18201007683552337053529799)
      ·
        refine ⟨27301511525328505580294699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18201007683552337053529799 27301511525328505580294699)
        ·
          refine ⟨40952267287992758370442049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27301511525328505580294699 40952267287992758370442049)
          ·
            refine ⟨30714200465994568777831537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40952267287992758370442049 30714200465994568777831537)
            ·
              refine ⟨23035650349495926583373653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30714200465994568777831537 23035650349495926583373653)
              ·
                refine ⟨134974513766577694824455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23035650349495926583373653 134974513766577694824455)
                ·
                  rfl

theorem cell20_887159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_887159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887159 prefixEnd_887159 := by exact prefixLift 887159
  have htrace : WordTrace (prefixWord ++ tailWord_887159) baseStart_887159 baseEnd_887159 := by
    simpa [prefixWord, tailWord_887159, baseEnd_887159] using wordTrace_append hprefix tailTrace_887159
  have hstable : (prefixWord ++ tailWord_887159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887159).length < 2 ^ (prefixWord ++ tailWord_887159).sum := by decide
  have hdescent : baseEnd_887159 < baseStart_887159 := by decide
  rcases family_descends (prefixWord ++ tailWord_887159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887169 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_887169 : Nat := 118140960795 + 887169 * 2 ^ 59
def prefixEnd_887169 : Nat := 4983230072969 + 3 ^ 40 * 887169 * 2
def baseEnd_887169 : Nat := 404928105572217494139991

theorem tailTrace_887169 : CollatzResearch.WordTrace tailWord_887169 prefixEnd_887169 404928105572217494139991 := by
  unfold tailWord_887169
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357711722945704247472561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21571807815297136164981707 32357711722945704247472561)
  ·
    refine ⟨24268283792209278185604421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32357711722945704247472561 24268283792209278185604421)
    ·
      refine ⟨4550303211039239659800829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24268283792209278185604421 4550303211039239659800829)
      ·
        refine ⟨1706363704139714872425311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4550303211039239659800829 1706363704139714872425311)
        ·
          refine ⟨2559545556209572308637967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706363704139714872425311 2559545556209572308637967)
          ·
            refine ⟨3839318334314358462956951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559545556209572308637967 3839318334314358462956951)
            ·
              refine ⟨5758977501471537694435427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839318334314358462956951 5758977501471537694435427)
              ·
                refine ⟨8638466252207306541653141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758977501471537694435427 8638466252207306541653141)
                ·
                  refine ⟨404928105572217494139991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8638466252207306541653141 404928105572217494139991)
                  ·
                    rfl

theorem cell20_887169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_887169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887169 prefixEnd_887169 := by exact prefixLift 887169
  have htrace : WordTrace (prefixWord ++ tailWord_887169) baseStart_887169 baseEnd_887169 := by
    simpa [prefixWord, tailWord_887169, baseEnd_887169] using wordTrace_append hprefix tailTrace_887169
  have hstable : (prefixWord ++ tailWord_887169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887169).length < 2 ^ (prefixWord ++ tailWord_887169).sum := by decide
  have hdescent : baseEnd_887169 < baseStart_887169 := by decide
  rcases family_descends (prefixWord ++ tailWord_887169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887200 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_887200 : Nat := 118140960795 + 887200 * 2 ^ 59
def prefixEnd_887200 : Nat := 4983230072969 + 3 ^ 40 * 887200 * 2
def baseEnd_887200 : Nat := 404942254816919164106531

theorem tailTrace_887200 : CollatzResearch.WordTrace tailWord_887200 prefixEnd_887200 404942254816919164106531 := by
  unfold tailWord_887200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179421192916698270925527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21572561590555597694567369 16179421192916698270925527)
  ·
    refine ⟨24269131789375047406388291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16179421192916698270925527 24269131789375047406388291)
    ·
      refine ⟨36403697684062571109582437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24269131789375047406388291 36403697684062571109582437)
      ·
        refine ⟨6825693315761732083046707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36403697684062571109582437 6825693315761732083046707)
        ·
          refine ⟨10238539973642598124570061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825693315761732083046707 10238539973642598124570061)
          ·
            refine ⟨3839452490115974296713773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10238539973642598124570061 3839452490115974296713773)
            ·
              refine ⟨1439794683793490361267665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3839452490115974296713773 1439794683793490361267665)
              ·
                refine ⟨1079846012845117770950749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439794683793490361267665 1079846012845117770950749)
                ·
                  refine ⟨404942254816919164106531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079846012845117770950749 404942254816919164106531)
                  ·
                    rfl

theorem cell20_887200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_887200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887200 prefixEnd_887200 := by exact prefixLift 887200
  have htrace : WordTrace (prefixWord ++ tailWord_887200) baseStart_887200 baseEnd_887200 := by
    simpa [prefixWord, tailWord_887200, baseEnd_887200] using wordTrace_append hprefix tailTrace_887200
  have hstable : (prefixWord ++ tailWord_887200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887200).length < 2 ^ (prefixWord ++ tailWord_887200).sum := by decide
  have hdescent : baseEnd_887200 < baseStart_887200 := by decide
  rcases family_descends (prefixWord ++ tailWord_887200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887207 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_887207 : Nat := 118140960795 + 887207 * 2 ^ 59
def prefixEnd_887207 : Nat := 4983230072969 + 3 ^ 40 * 887207 * 2
def baseEnd_887207 : Nat := 404945449807658250873169

theorem tailTrace_887207 : CollatzResearch.WordTrace tailWord_887207 prefixEnd_887207 404945449807658250873169 := by
  unfold tailWord_887207
  simp only [CollatzResearch.WordTrace]
  refine ⟨32359097696808036737355875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21572731797872024491570583 32359097696808036737355875)
  ·
    refine ⟨48538646545212055106033813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32359097696808036737355875 48538646545212055106033813)
    ·
      refine ⟨2275249056806815083095335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48538646545212055106033813 2275249056806815083095335)
      ·
        refine ⟨3412873585210222624643003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275249056806815083095335 3412873585210222624643003)
        ·
          refine ⟨5119310377815333936964505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412873585210222624643003 5119310377815333936964505)
          ·
            refine ⟨3839482783361500452723379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119310377815333936964505 3839482783361500452723379)
            ·
              refine ⟨5759224175042250679085069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839482783361500452723379 5759224175042250679085069)
              ·
                refine ⟨2159709065640844004656901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5759224175042250679085069 2159709065640844004656901)
                ·
                  refine ⟨404945449807658250873169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2159709065640844004656901 404945449807658250873169)
                  ·
                    rfl

theorem cell20_887207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_887207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887207 prefixEnd_887207 := by exact prefixLift 887207
  have htrace : WordTrace (prefixWord ++ tailWord_887207) baseStart_887207 baseEnd_887207 := by
    simpa [prefixWord, tailWord_887207, baseEnd_887207] using wordTrace_append hprefix tailTrace_887207
  have hstable : (prefixWord ++ tailWord_887207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887207).length < 2 ^ (prefixWord ++ tailWord_887207).sum := by decide
  have hdescent : baseEnd_887207 < baseStart_887207 := by decide
  rcases family_descends (prefixWord ++ tailWord_887207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887217 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 3]
def baseStart_887217 : Nat := 118140960795 + 887217 * 2 ^ 59
def prefixEnd_887217 : Nat := 4983230072969 + 3 ^ 40 * 887217 * 2
def baseEnd_887217 : Nat := 404950014080142660539795

theorem tailTrace_887217 : CollatzResearch.WordTrace tailWord_887217 prefixEnd_887217 404950014080142660539795 := by
  unfold tailWord_887217
  simp only [CollatzResearch.WordTrace]
  refine ⟨32359462426771808445219905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21572974951181205630146603 32359462426771808445219905)
  ·
    refine ⟨24269596820078856333914929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32359462426771808445219905 24269596820078856333914929)
    ·
      refine ⟨18202197615059142250436197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24269596820078856333914929 18202197615059142250436197)
      ·
        refine ⟨3412912052823589171956787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18202197615059142250436197 3412912052823589171956787)
        ·
          refine ⟨5119368079235383757935181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412912052823589171956787 5119368079235383757935181)
          ·
            refine ⟨1919763029713268909225693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5119368079235383757935181 1919763029713268909225693)
            ·
              refine ⟨719911136142475840959635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919763029713268909225693 719911136142475840959635)
              ·
                refine ⟨1079866704213713761439453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719911136142475840959635 1079866704213713761439453)
                ·
                  refine ⟨404950014080142660539795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079866704213713761439453 404950014080142660539795)
                  ·
                    rfl

theorem cell20_887217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_887217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887217 prefixEnd_887217 := by exact prefixLift 887217
  have htrace : WordTrace (prefixWord ++ tailWord_887217) baseStart_887217 baseEnd_887217 := by
    simpa [prefixWord, tailWord_887217, baseEnd_887217] using wordTrace_append hprefix tailTrace_887217
  have hstable : (prefixWord ++ tailWord_887217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887217).length < 2 ^ (prefixWord ++ tailWord_887217).sum := by decide
  have hdescent : baseEnd_887217 < baseStart_887217 := by decide
  rcases family_descends (prefixWord ++ tailWord_887217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887252 : List Nat := [2, 4, 1, 2, 2, 1, 8]
def baseStart_887252 : Nat := 118140960795 + 887252 * 2 ^ 59
def prefixEnd_887252 : Nat := 4983230072969 + 3 ^ 40 * 887252 * 2
def baseEnd_887252 : Nat := 44996221003759788263665

theorem tailTrace_887252 : CollatzResearch.WordTrace tailWord_887252 prefixEnd_887252 44996221003759788263665 := by
  unfold tailWord_887252
  simp only [CollatzResearch.WordTrace]
  refine ⟨16180369490822504711372005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21573825987763339615162673 16180369490822504711372005)
  ·
    refine ⟨3033819279529219633382251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16180369490822504711372005 3033819279529219633382251)
    ·
      refine ⟨4550728919293829450073377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033819279529219633382251 4550728919293829450073377)
      ·
        refine ⟨3413046689470372087555033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550728919293829450073377 3413046689470372087555033)
        ·
          refine ⟨2559785017102779065666275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413046689470372087555033 2559785017102779065666275)
          ·
            refine ⟨3839677525654168598499413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559785017102779065666275 3839677525654168598499413)
            ·
              refine ⟨44996221003759788263665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3839677525654168598499413 44996221003759788263665)
              ·
                rfl

theorem cell20_887252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_887252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887252 prefixEnd_887252 := by exact prefixLift 887252
  have htrace : WordTrace (prefixWord ++ tailWord_887252) baseStart_887252 baseEnd_887252 := by
    simpa [prefixWord, tailWord_887252, baseEnd_887252] using wordTrace_append hprefix tailTrace_887252
  have hstable : (prefixWord ++ tailWord_887252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887252).length < 2 ^ (prefixWord ++ tailWord_887252).sum := by decide
  have hdescent : baseEnd_887252 < baseStart_887252 := by decide
  rcases family_descends (prefixWord ++ tailWord_887252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887269 : List Nat := [1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_887269 : Nat := 118140960795 + 887269 * 2 ^ 59
def prefixEnd_887269 : Nat := 4983230072969 + 3 ^ 40 * 887269 * 2
def baseEnd_887269 : Nat := 134991249432353863602083

theorem tailTrace_887269 : CollatzResearch.WordTrace tailWord_887269 prefixEnd_887269 134991249432353863602083 := by
  unfold tailWord_887269
  simp only [CollatzResearch.WordTrace]
  refine ⟨32361359022583421326112861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21574239348388947550741907 32361359022583421326112861)
  ·
    refine ⟨12135509633468782997292323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32361359022583421326112861 12135509633468782997292323)
    ·
      refine ⟨18203264450203174495938485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12135509633468782997292323 18203264450203174495938485)
      ·
        refine ⟨1706556042206547608994233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18203264450203174495938485 1706556042206547608994233)
        ·
          refine ⟨1279917031654910706745675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706556042206547608994233 1279917031654910706745675)
          ·
            refine ⟨1919875547482366060118513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279917031654910706745675 1919875547482366060118513)
            ·
              refine ⟨1439906660611774545088885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919875547482366060118513 1439906660611774545088885)
              ·
                refine ⟨134991249432353863602083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1439906660611774545088885 134991249432353863602083)
                ·
                  rfl

theorem cell20_887269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_887269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887269 prefixEnd_887269 := by exact prefixLift 887269
  have htrace : WordTrace (prefixWord ++ tailWord_887269) baseStart_887269 baseEnd_887269 := by
    simpa [prefixWord, tailWord_887269, baseEnd_887269] using wordTrace_append hprefix tailTrace_887269
  have hstable : (prefixWord ++ tailWord_887269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887269).length < 2 ^ (prefixWord ++ tailWord_887269).sum := by decide
  have hdescent : baseEnd_887269 < baseStart_887269 := by decide
  rcases family_descends (prefixWord ++ tailWord_887269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887321 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 2]
def baseStart_887321 : Nat := 118140960795 + 887321 * 2 ^ 59
def prefixEnd_887321 : Nat := 4983230072969 + 3 ^ 40 * 887321 * 2
def baseEnd_887321 : Nat := 404997482513980521072703

theorem tailTrace_887321 : CollatzResearch.WordTrace tailWord_887321 prefixEnd_887321 404997482513980521072703 := by
  unfold tailWord_887321
  simp only [CollatzResearch.WordTrace]
  refine ⟨32363255618395034207005817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21575503745596689471337211 32363255618395034207005817)
  ·
    refine ⟨24272441713796275655254363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32363255618395034207005817 24272441713796275655254363)
    ·
      refine ⟨36408662570694413482881545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24272441713796275655254363 36408662570694413482881545)
      ·
        refine ⟨27306496928020810112161159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36408662570694413482881545 27306496928020810112161159)
        ·
          refine ⟨40959745392031215168241739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27306496928020810112161159 40959745392031215168241739)
          ·
            refine ⟨61439618088046822752362609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40959745392031215168241739 61439618088046822752362609)
            ·
              refine ⟨46079713566035117064271957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61439618088046822752362609 46079713566035117064271957)
              ·
                refine ⟨539996643351974028096937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46079713566035117064271957 539996643351974028096937)
                ·
                  refine ⟨404997482513980521072703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539996643351974028096937 404997482513980521072703)
                  ·
                    rfl

theorem cell20_887321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_887321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887321 prefixEnd_887321 := by exact prefixLift 887321
  have htrace : WordTrace (prefixWord ++ tailWord_887321) baseStart_887321 baseEnd_887321 := by
    simpa [prefixWord, tailWord_887321, baseEnd_887321] using wordTrace_append hprefix tailTrace_887321
  have hstable : (prefixWord ++ tailWord_887321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887321).length < 2 ^ (prefixWord ++ tailWord_887321).sum := by decide
  have hdescent : baseEnd_887321 < baseStart_887321 := by decide
  rcases family_descends (prefixWord ++ tailWord_887321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887400 : List Nat := [2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_887400 : Nat := 118140960795 + 887400 * 2 ^ 59
def prefixEnd_887400 : Nat := 4983230072969 + 3 ^ 40 * 887400 * 2
def baseEnd_887400 : Nat := 135011180088869119146349

theorem tailTrace_887400 : CollatzResearch.WordTrace tailWord_887400 prefixEnd_887400 135011180088869119146349 := by
  unfold tailWord_887400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183068492554415349565827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21577424656739220466087769 16183068492554415349565827)
  ·
    refine ⟨24274602738831623024348741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16183068492554415349565827 24274602738831623024348741)
    ·
      refine ⟨4551488013530929317065389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24274602738831623024348741 4551488013530929317065389)
      ·
        refine ⟨1706808005074098493899521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4551488013530929317065389 1706808005074098493899521)
        ·
          refine ⟨1280106003805573870424641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706808005074098493899521 1280106003805573870424641)
          ·
            refine ⟨960079502854180402818481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280106003805573870424641 960079502854180402818481)
            ·
              refine ⟨720059627140635302113861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960079502854180402818481 720059627140635302113861)
              ·
                refine ⟨135011180088869119146349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720059627140635302113861 135011180088869119146349)
                ·
                  rfl

theorem cell20_887400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_887400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887400 prefixEnd_887400 := by exact prefixLift 887400
  have htrace : WordTrace (prefixWord ++ tailWord_887400) baseStart_887400 baseEnd_887400 := by
    simpa [prefixWord, tailWord_887400, baseEnd_887400] using wordTrace_append hprefix tailTrace_887400
  have hstable : (prefixWord ++ tailWord_887400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887400).length < 2 ^ (prefixWord ++ tailWord_887400).sum := by decide
  have hdescent : baseEnd_887400 < baseStart_887400 := by decide
  rcases family_descends (prefixWord ++ tailWord_887400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887404 : List Nat := [2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_887404 : Nat := 118140960795 + 887404 * 2 ^ 59
def prefixEnd_887404 : Nat := 4983230072969 + 3 ^ 40 * 887404 * 2
def baseEnd_887404 : Nat := 135011788658533707101899

theorem tailTrace_887404 : CollatzResearch.WordTrace tailWord_887404 prefixEnd_887404 135011788658533707101899 := by
  unfold tailWord_887404
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183141438547169691138633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21577521918062892921518177 16183141438547169691138633)
  ·
    refine ⟨12137356078910377268353975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16183141438547169691138633 12137356078910377268353975)
    ·
      refine ⟨18206034118365565902530963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12137356078910377268353975 18206034118365565902530963)
      ·
        refine ⟨27309051177548348853796445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18206034118365565902530963 27309051177548348853796445)
        ·
          refine ⟨10240894191580630820173667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27309051177548348853796445 10240894191580630820173667)
          ·
            refine ⟨15361341287370946230260501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240894191580630820173667 15361341287370946230260501)
            ·
              refine ⟨720062872845513104543461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15361341287370946230260501 720062872845513104543461)
              ·
                refine ⟨135011788658533707101899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720062872845513104543461 135011788658533707101899)
                ·
                  rfl

theorem cell20_887404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_887404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887404 prefixEnd_887404 := by exact prefixLift 887404
  have htrace : WordTrace (prefixWord ++ tailWord_887404) baseStart_887404 baseEnd_887404 := by
    simpa [prefixWord, tailWord_887404, baseEnd_887404] using wordTrace_append hprefix tailTrace_887404
  have hstable : (prefixWord ++ tailWord_887404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887404).length < 2 ^ (prefixWord ++ tailWord_887404).sum := by decide
  have hdescent : baseEnd_887404 < baseStart_887404 := by decide
  rcases family_descends (prefixWord ++ tailWord_887404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887410 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_887410 : Nat := 118140960795 + 887410 * 2 ^ 59
def prefixEnd_887410 : Nat := 4983230072969 + 3 ^ 40 * 887410 * 2
def baseEnd_887410 : Nat := 405038104539091767105673

theorem tailTrace_887410 : CollatzResearch.WordTrace tailWord_887410 prefixEnd_887410 405038104539091767105673 := by
  unfold tailWord_887410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091625428768150601748921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21577667810048401604663789 8091625428768150601748921)
  ·
    refine ⟨6068719071576112951311691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8091625428768150601748921 6068719071576112951311691)
    ·
      refine ⟨9103078607364169426967537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068719071576112951311691 9103078607364169426967537)
      ·
        refine ⟨6827308955523127070225653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103078607364169426967537 6827308955523127070225653)
        ·
          refine ⟨640060214580293162833655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6827308955523127070225653 640060214580293162833655)
          ·
            refine ⟨960090321870439744250483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640060214580293162833655 960090321870439744250483)
            ·
              refine ⟨1440135482805659616375725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960090321870439744250483 1440135482805659616375725)
              ·
                refine ⟨540050806052122356140897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1440135482805659616375725 540050806052122356140897)
                ·
                  refine ⟨405038104539091767105673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540050806052122356140897 405038104539091767105673)
                  ·
                    rfl

theorem cell20_887410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_887410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887410 prefixEnd_887410 := by exact prefixLift 887410
  have htrace : WordTrace (prefixWord ++ tailWord_887410) baseStart_887410 baseEnd_887410 := by
    simpa [prefixWord, tailWord_887410, baseEnd_887410] using wordTrace_append hprefix tailTrace_887410
  have hstable : (prefixWord ++ tailWord_887410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887410).length < 2 ^ (prefixWord ++ tailWord_887410).sum := by decide
  have hdescent : baseEnd_887410 < baseStart_887410 := by decide
  rcases family_descends (prefixWord ++ tailWord_887410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887421 : List Nat := [1, 4, 1, 1, 6, 1, 6]
def baseStart_887421 : Nat := 118140960795 + 887421 * 2 ^ 59
def prefixEnd_887421 : Nat := 4983230072969 + 3 ^ 40 * 887421 * 2
def baseEnd_887421 : Nat := 45004791693202735304329

theorem tailTrace_887421 : CollatzResearch.WordTrace tailWord_887421 prefixEnd_887421 45004791693202735304329 := by
  unfold tailWord_887421
  simp only [CollatzResearch.WordTrace]
  refine ⟨32366902918032751285646117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21577935278688500857097411 32366902918032751285646117)
  ·
    refine ⟨6068794297131140866058647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32366902918032751285646117 6068794297131140866058647)
    ·
      refine ⟨9103191445696711299087971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068794297131140866058647 9103191445696711299087971)
      ·
        refine ⟨13654787168545066948631957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103191445696711299087971 13654787168545066948631957)
        ·
          refine ⟨640068148525550013217123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13654787168545066948631957 640068148525550013217123)
          ·
            refine ⟨960102222788325019825685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640068148525550013217123 960102222788325019825685)
            ·
              refine ⟨45004791693202735304329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 960102222788325019825685 45004791693202735304329)
              ·
                rfl

theorem cell20_887421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 6].length) (baseStart_887421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887421 prefixEnd_887421 := by exact prefixLift 887421
  have htrace : WordTrace (prefixWord ++ tailWord_887421) baseStart_887421 baseEnd_887421 := by
    simpa [prefixWord, tailWord_887421, baseEnd_887421] using wordTrace_append hprefix tailTrace_887421
  have hstable : (prefixWord ++ tailWord_887421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887421).length < 2 ^ (prefixWord ++ tailWord_887421).sum := by decide
  have hdescent : baseEnd_887421 < baseStart_887421 := by decide
  rcases family_descends (prefixWord ++ tailWord_887421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887442 : List Nat := [3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_887442 : Nat := 118140960795 + 887442 * 2 ^ 59
def prefixEnd_887442 : Nat := 4983230072969 + 3 ^ 40 * 887442 * 2
def baseEnd_887442 : Nat := 135017570070347292679625

theorem tailTrace_887442 : CollatzResearch.WordTrace tailWord_887442 prefixEnd_887442 135017570070347292679625 := by
  unfold tailWord_887442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091917212739167968040145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21578445900637781248107053 8091917212739167968040145)
  ·
    refine ⟨6068937909554375976030109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8091917212739167968040145 6068937909554375976030109)
    ·
      refine ⟨2275851716082890991011291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6068937909554375976030109 2275851716082890991011291)
      ·
        refine ⟨3413777574124336486516937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275851716082890991011291 3413777574124336486516937)
        ·
          refine ⟨2560333180593252364887703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413777574124336486516937 2560333180593252364887703)
          ·
            refine ⟨3840499770889878547331555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560333180593252364887703 3840499770889878547331555)
            ·
              refine ⟨5760749656334817820997333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840499770889878547331555 5760749656334817820997333)
              ·
                refine ⟨135017570070347292679625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5760749656334817820997333 135017570070347292679625)
                ·
                  rfl

theorem cell20_887442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_887442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887442 prefixEnd_887442 := by exact prefixLift 887442
  have htrace : WordTrace (prefixWord ++ tailWord_887442) baseStart_887442 baseEnd_887442 := by
    simpa [prefixWord, tailWord_887442, baseEnd_887442] using wordTrace_append hprefix tailTrace_887442
  have hstable : (prefixWord ++ tailWord_887442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887442).length < 2 ^ (prefixWord ++ tailWord_887442).sum := by decide
  have hdescent : baseEnd_887442 < baseStart_887442 := by decide
  rcases family_descends (prefixWord ++ tailWord_887442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887449 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_887449 : Nat := 118140960795 + 887449 * 2 ^ 59
def prefixEnd_887449 : Nat := 4983230072969 + 3 ^ 40 * 887449 * 2
def baseEnd_887449 : Nat := 405055905201780964805513

theorem tailTrace_887449 : CollatzResearch.WordTrace tailWord_887449 prefixEnd_887449 405055905201780964805513 := by
  unfold tailWord_887449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367924161931312067665401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21578616107954208045110267 32367924161931312067665401)
  ·
    refine ⟨24275943121448484050749051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32367924161931312067665401 24275943121448484050749051)
    ·
      refine ⟨36413914682172726076123577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24275943121448484050749051 36413914682172726076123577)
      ·
        refine ⟨27310436011629544557092683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36413914682172726076123577 27310436011629544557092683)
        ·
          refine ⟨40965654017444316835639025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27310436011629544557092683 40965654017444316835639025)
          ·
            refine ⟨30724240513083237626729269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40965654017444316835639025 30724240513083237626729269)
            ·
              refine ⟨2880397548101553527505869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30724240513083237626729269 2880397548101553527505869)
              ·
                refine ⟨1080149080538082572814701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2880397548101553527505869 1080149080538082572814701)
                ·
                  refine ⟨405055905201780964805513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080149080538082572814701 405055905201780964805513)
                  ·
                    rfl

theorem cell20_887449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_887449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887449 prefixEnd_887449 := by exact prefixLift 887449
  have htrace : WordTrace (prefixWord ++ tailWord_887449) baseStart_887449 baseEnd_887449 := by
    simpa [prefixWord, tailWord_887449, baseEnd_887449] using wordTrace_append hprefix tailTrace_887449
  have hstable : (prefixWord ++ tailWord_887449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887449).length < 2 ^ (prefixWord ++ tailWord_887449).sum := by decide
  have hdescent : baseEnd_887449 < baseStart_887449 := by decide
  rcases family_descends (prefixWord ++ tailWord_887449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887487 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_887487 : Nat := 118140960795 + 887487 * 2 ^ 59
def prefixEnd_887487 : Nat := 4983230072969 + 3 ^ 40 * 887487 * 2
def baseEnd_887487 : Nat := 405073249437221721538691

theorem tailTrace_887487 : CollatzResearch.WordTrace tailWord_887487 prefixEnd_887487 405073249437221721538691 := by
  unfold tailWord_887487
  simp only [CollatzResearch.WordTrace]
  refine ⟨32369310135793644557548715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21579540090529096371699143 32369310135793644557548715)
  ·
    refine ⟨48553965203690466836323073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32369310135793644557548715 48553965203690466836323073)
    ·
      refine ⟨36415473902767850127242305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48553965203690466836323073 36415473902767850127242305)
      ·
        refine ⟨27311605427075887595431729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36415473902767850127242305 27311605427075887595431729)
        ·
          refine ⟨20483704070306915696573797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27311605427075887595431729 20483704070306915696573797)
          ·
            refine ⟨3840694513182546693107587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20483704070306915696573797 3840694513182546693107587)
            ·
              refine ⟨5761041769773820039661381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840694513182546693107587 5761041769773820039661381)
              ·
                refine ⟨1080195331832591257436509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5761041769773820039661381 1080195331832591257436509)
                ·
                  refine ⟨405073249437221721538691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080195331832591257436509 405073249437221721538691)
                  ·
                    rfl

theorem cell20_887487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_887487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887487 prefixEnd_887487 := by exact prefixLift 887487
  have htrace : WordTrace (prefixWord ++ tailWord_887487) baseStart_887487 baseEnd_887487 := by
    simpa [prefixWord, tailWord_887487, baseEnd_887487] using wordTrace_append hprefix tailTrace_887487
  have hstable : (prefixWord ++ tailWord_887487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887487).length < 2 ^ (prefixWord ++ tailWord_887487).sum := by decide
  have hdescent : baseEnd_887487 < baseStart_887487 := by decide
  rcases family_descends (prefixWord ++ tailWord_887487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887549 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 2]
def baseStart_887549 : Nat := 118140960795 + 887549 * 2 ^ 59
def prefixEnd_887549 : Nat := 4983230072969 + 3 ^ 40 * 887549 * 2
def baseEnd_887549 : Nat := 405101547926625061471771

theorem tailTrace_887549 : CollatzResearch.WordTrace tailWord_887549 prefixEnd_887549 405101547926625061471771 := by
  unfold tailWord_887549
  simp only [CollatzResearch.WordTrace]
  refine ⟨32371571461569029146305701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21581047641046019430870467 32371571461569029146305701)
  ·
    refine ⟨6069669649044192964932319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32371571461569029146305701 6069669649044192964932319)
    ·
      refine ⟨9104504473566289447398479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069669649044192964932319 9104504473566289447398479)
      ·
        refine ⟨13656756710349434171097719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9104504473566289447398479 13656756710349434171097719)
        ·
          refine ⟨20485135065524151256646579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13656756710349434171097719 20485135065524151256646579)
          ·
            refine ⟨30727702598286226884969869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20485135065524151256646579 30727702598286226884969869)
            ·
              refine ⟨11522888474357335081863701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30727702598286226884969869 11522888474357335081863701)
              ·
                refine ⟨540135397235500081962361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11522888474357335081863701 540135397235500081962361)
                ·
                  refine ⟨405101547926625061471771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540135397235500081962361 405101547926625061471771)
                  ·
                    rfl

theorem cell20_887549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_887549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887549 prefixEnd_887549 := by exact prefixLift 887549
  have htrace : WordTrace (prefixWord ++ tailWord_887549) baseStart_887549 baseEnd_887549 := by
    simpa [prefixWord, tailWord_887549, baseEnd_887549] using wordTrace_append hprefix tailTrace_887549
  have hstable : (prefixWord ++ tailWord_887549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887549).length < 2 ^ (prefixWord ++ tailWord_887549).sum := by decide
  have hdescent : baseEnd_887549 < baseStart_887549 := by decide
  rcases family_descends (prefixWord ++ tailWord_887549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887559 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 3]
def baseStart_887559 : Nat := 118140960795 + 887559 * 2 ^ 59
def prefixEnd_887559 : Nat := 4983230072969 + 3 ^ 40 * 887559 * 2
def baseEnd_887559 : Nat := 405106112199109471138397

theorem tailTrace_887559 : CollatzResearch.WordTrace tailWord_887559 prefixEnd_887559 405106112199109471138397 := by
  unfold tailWord_887559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32371936191532800854169731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21581290794355200569446487 32371936191532800854169731)
  ·
    refine ⟨48557904287299201281254597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32371936191532800854169731 48557904287299201281254597)
    ·
      refine ⟨9104607053868600240235237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48557904287299201281254597 9104607053868600240235237)
      ·
        refine ⟨1707113822600362545044107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9104607053868600240235237 1707113822600362545044107)
        ·
          refine ⟨2560670733900543817566161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707113822600362545044107 2560670733900543817566161)
          ·
            refine ⟨1920503050425407863174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2560670733900543817566161 1920503050425407863174621)
            ·
              refine ⟨720188643909527948690483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920503050425407863174621 720188643909527948690483)
              ·
                refine ⟨1080282965864291923035725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720188643909527948690483 1080282965864291923035725)
                ·
                  refine ⟨405106112199109471138397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080282965864291923035725 405106112199109471138397)
                  ·
                    rfl

theorem cell20_887559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_887559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887559 prefixEnd_887559 := by exact prefixLift 887559
  have htrace : WordTrace (prefixWord ++ tailWord_887559) baseStart_887559 baseEnd_887559 := by
    simpa [prefixWord, tailWord_887559, baseEnd_887559] using wordTrace_append hprefix tailTrace_887559
  have hstable : (prefixWord ++ tailWord_887559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887559).length < 2 ^ (prefixWord ++ tailWord_887559).sum := by decide
  have hdescent : baseEnd_887559 < baseStart_887559 := by decide
  rcases family_descends (prefixWord ++ tailWord_887559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887601 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_887601 : Nat := 118140960795 + 887601 * 2 ^ 59
def prefixEnd_887601 : Nat := 4983230072969 + 3 ^ 40 * 887601 * 2
def baseEnd_887601 : Nat := 405125282143543991738225

theorem tailTrace_887601 : CollatzResearch.WordTrace tailWord_887601 prefixEnd_887601 405125282143543991738225 := by
  unfold tailWord_887601
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373468057380642027198657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21582312038253761351465771 32373468057380642027198657)
  ·
    refine ⟨24280101043035481520398993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32373468057380642027198657 24280101043035481520398993)
    ·
      refine ⟨18210075782276611140299245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24280101043035481520398993 18210075782276611140299245)
      ·
        refine ⟨6828778418353729177612217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18210075782276611140299245 6828778418353729177612217)
        ·
          refine ⟨5121583813765296883209163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6828778418353729177612217 5121583813765296883209163)
          ·
            refine ⟨7682375720647945324813745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121583813765296883209163 7682375720647945324813745)
            ·
              refine ⟨5761781790485958993610309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7682375720647945324813745 5761781790485958993610309)
              ·
                refine ⟨1080334085716117311301933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5761781790485958993610309 1080334085716117311301933)
                ·
                  refine ⟨405125282143543991738225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080334085716117311301933 405125282143543991738225)
                  ·
                    rfl

theorem cell20_887601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_887601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887601 prefixEnd_887601 := by exact prefixLift 887601
  have htrace : WordTrace (prefixWord ++ tailWord_887601) baseStart_887601 baseEnd_887601 := by
    simpa [prefixWord, tailWord_887601, baseEnd_887601] using wordTrace_append hprefix tailTrace_887601
  have hstable : (prefixWord ++ tailWord_887601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887601).length < 2 ^ (prefixWord ++ tailWord_887601).sum := by decide
  have hdescent : baseEnd_887601 < baseStart_887601 := by decide
  rcases family_descends (prefixWord ++ tailWord_887601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887614 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_887614 : Nat := 118140960795 + 887614 * 2 ^ 59
def prefixEnd_887614 : Nat := 4983230072969 + 3 ^ 40 * 887614 * 2
def baseEnd_887614 : Nat := 405131215697773724304839

theorem tailTrace_887614 : CollatzResearch.WordTrace tailWord_887614 prefixEnd_887614 405131215697773724304839 := by
  unfold tailWord_887614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046742775791693155927737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21582628137555696831614597 4046742775791693155927737)
  ·
    refine ⟨3035057081843769866945803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4046742775791693155927737 3035057081843769866945803)
    ·
      refine ⟨4552585622765654800418705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035057081843769866945803 4552585622765654800418705)
      ·
        refine ⟨3414439217074241100314029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4552585622765654800418705 3414439217074241100314029)
        ·
          refine ⟨1280414706402840412617761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3414439217074241100314029 1280414706402840412617761)
          ·
            refine ⟨960311029802130309463321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280414706402840412617761 960311029802130309463321)
            ·
              refine ⟨720233272351597732097491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960311029802130309463321 720233272351597732097491)
              ·
                refine ⟨1080349908527396598146237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720233272351597732097491 1080349908527396598146237)
                ·
                  refine ⟨405131215697773724304839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080349908527396598146237 405131215697773724304839)
                  ·
                    rfl

theorem cell20_887614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_887614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887614 prefixEnd_887614 := by exact prefixLift 887614
  have htrace : WordTrace (prefixWord ++ tailWord_887614) baseStart_887614 baseEnd_887614 := by
    simpa [prefixWord, tailWord_887614, baseEnd_887614] using wordTrace_append hprefix tailTrace_887614
  have hstable : (prefixWord ++ tailWord_887614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887614).length < 2 ^ (prefixWord ++ tailWord_887614).sum := by decide
  have hdescent : baseEnd_887614 < baseStart_887614 := by decide
  rcases family_descends (prefixWord ++ tailWord_887614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887615 : List Nat := [1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_887615 : Nat := 118140960795 + 887615 * 2 ^ 59
def prefixEnd_887615 : Nat := 4983230072969 + 3 ^ 40 * 887615 * 2
def baseEnd_887615 : Nat := 135043890708340721757167

theorem tailTrace_887615 : CollatzResearch.WordTrace tailWord_887615 prefixEnd_887615 135043890708340721757167 := by
  unfold tailWord_887615
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373978679329922418208299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21582652452886614945472199 32373978679329922418208299)
  ·
    refine ⟨48560968018994883627312449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32373978679329922418208299 48560968018994883627312449)
    ·
      refine ⟨36420726014246162720484337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48560968018994883627312449 36420726014246162720484337)
      ·
        refine ⟨27315544510684622040363253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36420726014246162720484337 27315544510684622040363253)
        ·
          refine ⟨2560832297876683316284055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27315544510684622040363253 2560832297876683316284055)
          ·
            refine ⟨3841248446815024974426083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560832297876683316284055 3841248446815024974426083)
            ·
              refine ⟨5761872670222537461639125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841248446815024974426083 5761872670222537461639125)
              ·
                refine ⟨135043890708340721757167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5761872670222537461639125 135043890708340721757167)
                ·
                  rfl

theorem cell20_887615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_887615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887615 prefixEnd_887615 := by exact prefixLift 887615
  have htrace : WordTrace (prefixWord ++ tailWord_887615) baseStart_887615 baseEnd_887615 := by
    simpa [prefixWord, tailWord_887615, baseEnd_887615] using wordTrace_append hprefix tailTrace_887615
  have hstable : (prefixWord ++ tailWord_887615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887615).length < 2 ^ (prefixWord ++ tailWord_887615).sum := by decide
  have hdescent : baseEnd_887615 < baseStart_887615 := by decide
  rcases family_descends (prefixWord ++ tailWord_887615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887656 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_887656 : Nat := 118140960795 + 887656 * 2 ^ 59
def prefixEnd_887656 : Nat := 4983230072969 + 3 ^ 40 * 887656 * 2
def baseEnd_887656 : Nat := 405150385642208244904667

theorem tailTrace_887656 : CollatzResearch.WordTrace tailWord_887656 prefixEnd_887656 405150385642208244904667 := by
  unfold tailWord_887656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16187737036090693210225411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21583649381454257613633881 16187737036090693210225411)
  ·
    refine ⟨24281605554136039815338117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16187737036090693210225411 24281605554136039815338117)
    ·
      refine ⟨4552801041400507465375897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24281605554136039815338117 4552801041400507465375897)
      ·
        refine ⟨3414600781050380599031923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4552801041400507465375897 3414600781050380599031923)
        ·
          refine ⟨5121901171575570898547885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414600781050380599031923 5121901171575570898547885)
          ·
            refine ⟨1920712939340839086955457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5121901171575570898547885 1920712939340839086955457)
            ·
              refine ⟨1440534704505629315216593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920712939340839086955457 1440534704505629315216593)
              ·
                refine ⟨1080401028379221986412445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440534704505629315216593 1080401028379221986412445)
                ·
                  refine ⟨405150385642208244904667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080401028379221986412445 405150385642208244904667)
                  ·
                    rfl

theorem cell20_887656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_887656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887656 prefixEnd_887656 := by exact prefixLift 887656
  have htrace : WordTrace (prefixWord ++ tailWord_887656) baseStart_887656 baseEnd_887656 := by
    simpa [prefixWord, tailWord_887656, baseEnd_887656] using wordTrace_append hprefix tailTrace_887656
  have hstable : (prefixWord ++ tailWord_887656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887656).length < 2 ^ (prefixWord ++ tailWord_887656).sum := by decide
  have hdescent : baseEnd_887656 < baseStart_887656 := by decide
  rcases family_descends (prefixWord ++ tailWord_887656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887677 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_887677 : Nat := 118140960795 + 887677 * 2 ^ 59
def prefixEnd_887677 : Nat := 4983230072969 + 3 ^ 40 * 887677 * 2
def baseEnd_887677 : Nat := 405159970614425505204581

theorem tailTrace_887677 : CollatzResearch.WordTrace tailWord_887677 prefixEnd_887677 405159970614425505204581 := by
  unfold tailWord_887677
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376240005105307006965285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21584160003403538004643523 32376240005105307006965285)
  ·
    refine ⟨6070545000957245063805991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32376240005105307006965285 6070545000957245063805991)
    ·
      refine ⟨9105817501435867595708987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6070545000957245063805991 9105817501435867595708987)
      ·
        refine ⟨13658726252153801393563481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9105817501435867595708987 13658726252153801393563481)
        ·
          refine ⟨10244044689115351045172611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13658726252153801393563481 10244044689115351045172611)
          ·
            refine ⟨15366067033673026567758917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244044689115351045172611 15366067033673026567758917)
            ·
              refine ⟨2881137568813692481454797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15366067033673026567758917 2881137568813692481454797)
              ·
                refine ⟨1080426588305134680545549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2881137568813692481454797 1080426588305134680545549)
                ·
                  refine ⟨405159970614425505204581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080426588305134680545549 405159970614425505204581)
                  ·
                    rfl

theorem cell20_887677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_887677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887677 prefixEnd_887677 := by exact prefixLift 887677
  have htrace : WordTrace (prefixWord ++ tailWord_887677) baseStart_887677 baseEnd_887677 := by
    simpa [prefixWord, tailWord_887677, baseEnd_887677] using wordTrace_append hprefix tailTrace_887677
  have hstable : (prefixWord ++ tailWord_887677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887677).length < 2 ^ (prefixWord ++ tailWord_887677).sum := by decide
  have hdescent : baseEnd_887677 < baseStart_887677 := by decide
  rcases family_descends (prefixWord ++ tailWord_887677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887701 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 2]
def baseStart_887701 : Nat := 118140960795 + 887701 * 2 ^ 59
def prefixEnd_887701 : Nat := 4983230072969 + 3 ^ 40 * 887701 * 2
def baseEnd_887701 : Nat := 405170924868388088404483

theorem tailTrace_887701 : CollatzResearch.WordTrace tailWord_887701 prefixEnd_887701 405170924868388088404483 := by
  unfold tailWord_887701
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377115357018359105838957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21584743571345572737225971 32377115357018359105838957)
  ·
    refine ⟨12141418258881884664689609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32377115357018359105838957 12141418258881884664689609)
    ·
      refine ⟨9106063694161413498517207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12141418258881884664689609 9106063694161413498517207)
      ·
        refine ⟨13659095541242120247775811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106063694161413498517207 13659095541242120247775811)
        ·
          refine ⟨20488643311863180371663717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13659095541242120247775811 20488643311863180371663717)
          ·
            refine ⟨3841620620974346319686947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20488643311863180371663717 3841620620974346319686947)
            ·
              refine ⟨5762430931461519479530421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841620620974346319686947 5762430931461519479530421)
              ·
                refine ⟨540227899824517451205977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5762430931461519479530421 540227899824517451205977)
                ·
                  refine ⟨405170924868388088404483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540227899824517451205977 405170924868388088404483)
                  ·
                    rfl

theorem cell20_887701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_887701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887701 prefixEnd_887701 := by exact prefixLift 887701
  have htrace : WordTrace (prefixWord ++ tailWord_887701) baseStart_887701 baseEnd_887701 := by
    simpa [prefixWord, tailWord_887701, baseEnd_887701] using wordTrace_append hprefix tailTrace_887701
  have hstable : (prefixWord ++ tailWord_887701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887701).length < 2 ^ (prefixWord ++ tailWord_887701).sum := by decide
  have hdescent : baseEnd_887701 < baseStart_887701 := by decide
  rcases family_descends (prefixWord ++ tailWord_887701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887705 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_887705 : Nat := 118140960795 + 887705 * 2 ^ 59
def prefixEnd_887705 : Nat := 4983230072969 + 3 ^ 40 * 887705 * 2
def baseEnd_887705 : Nat := 405172750577381852271133

theorem tailTrace_887705 : CollatzResearch.WordTrace tailWord_887705 prefixEnd_887705 405172750577381852271133 := by
  unfold tailWord_887705
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377261249003867788984569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21584840832669245192656379 32377261249003867788984569)
  ·
    refine ⟨24282945936752900841738427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32377261249003867788984569 24282945936752900841738427)
    ·
      refine ⟨36424418905129351262607641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24282945936752900841738427 36424418905129351262607641)
      ·
        refine ⟨27318314178847013446955731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36424418905129351262607641 27318314178847013446955731)
        ·
          refine ⟨40977471268270520170433597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27318314178847013446955731 40977471268270520170433597)
          ·
            refine ⟨15366551725601445063912599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40977471268270520170433597 15366551725601445063912599)
            ·
              refine ⟨23049827588402167595868899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366551725601445063912599 23049827588402167595868899)
              ·
                refine ⟨34574741382603251393803349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23049827588402167595868899 34574741382603251393803349)
                ·
                  refine ⟨405172750577381852271133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34574741382603251393803349 405172750577381852271133)
                  ·
                    rfl

theorem cell20_887705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_887705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887705 prefixEnd_887705 := by exact prefixLift 887705
  have htrace : WordTrace (prefixWord ++ tailWord_887705) baseStart_887705 baseEnd_887705 := by
    simpa [prefixWord, tailWord_887705, baseEnd_887705] using wordTrace_append hprefix tailTrace_887705
  have hstable : (prefixWord ++ tailWord_887705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887705).length < 2 ^ (prefixWord ++ tailWord_887705).sum := by decide
  have hdescent : baseEnd_887705 < baseStart_887705 := by decide
  rcases family_descends (prefixWord ++ tailWord_887705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887708 : List Nat := [2, 2, 3, 3, 2, 1, 7]
def baseStart_887708 : Nat := 118140960795 + 887708 * 2 ^ 59
def prefixEnd_887708 : Nat := 4983230072969 + 3 ^ 40 * 887708 * 2
def baseEnd_887708 : Nat := 45019346651014130574569

theorem tailTrace_887708 : CollatzResearch.WordTrace tailWord_887708 prefixEnd_887708 45019346651014130574569 := by
  unfold tailWord_887708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16188685333996499650671889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21584913778661999534229185 16188685333996499650671889)
  ·
    refine ⟨12141514000497374738003917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16188685333996499650671889 12141514000497374738003917)
    ·
      refine ⟨4553067750186515526751469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12141514000497374738003917 4553067750186515526751469)
      ·
        refine ⟨1707400406319943322531801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4553067750186515526751469 1707400406319943322531801)
        ·
          refine ⟨1280550304739957491898851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707400406319943322531801 1280550304739957491898851)
          ·
            refine ⟨1920825457109936237848277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280550304739957491898851 1920825457109936237848277)
            ·
              refine ⟨45019346651014130574569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1920825457109936237848277 45019346651014130574569)
              ·
                rfl

theorem cell20_887708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_887708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887708 prefixEnd_887708 := by exact prefixLift 887708
  have htrace : WordTrace (prefixWord ++ tailWord_887708) baseStart_887708 baseEnd_887708 := by
    simpa [prefixWord, tailWord_887708, baseEnd_887708] using wordTrace_append hprefix tailTrace_887708
  have hstable : (prefixWord ++ tailWord_887708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887708).length < 2 ^ (prefixWord ++ tailWord_887708).sum := by decide
  have hdescent : baseEnd_887708 < baseStart_887708 := by decide
  rcases family_descends (prefixWord ++ tailWord_887708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887715 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_887715 : Nat := 118140960795 + 887715 * 2 ^ 59
def prefixEnd_887715 : Nat := 4983230072969 + 3 ^ 40 * 887715 * 2
def baseEnd_887715 : Nat := 405177314849866261937759

theorem tailTrace_887715 : CollatzResearch.WordTrace tailWord_887715 prefixEnd_887715 405177314849866261937759 := by
  unfold tailWord_887715
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377625978967639496848599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21585083985978426331232399 32377625978967639496848599)
  ·
    refine ⟨48566438968451459245272899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32377625978967639496848599 48566438968451459245272899)
    ·
      refine ⟨72849658452677188867909349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48566438968451459245272899 72849658452677188867909349)
      ·
        refine ⟨13659310959876972912733003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72849658452677188867909349 13659310959876972912733003)
        ·
          refine ⟨20488966439815459369099505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13659310959876972912733003 20488966439815459369099505)
          ·
            refine ⟨15366724829861594526824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20488966439815459369099505 15366724829861594526824629)
            ·
              refine ⟨1440630452799524486889809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15366724829861594526824629 1440630452799524486889809)
              ·
                refine ⟨1080472839599643365167357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440630452799524486889809 1080472839599643365167357)
                ·
                  refine ⟨405177314849866261937759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080472839599643365167357 405177314849866261937759)
                  ·
                    rfl

theorem cell20_887715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_887715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887715 prefixEnd_887715 := by exact prefixLift 887715
  have htrace : WordTrace (prefixWord ++ tailWord_887715) baseStart_887715 baseEnd_887715 := by
    simpa [prefixWord, tailWord_887715, baseEnd_887715] using wordTrace_append hprefix tailTrace_887715
  have hstable : (prefixWord ++ tailWord_887715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887715).length < 2 ^ (prefixWord ++ tailWord_887715).sum := by decide
  have hdescent : baseEnd_887715 < baseStart_887715 := by decide
  rcases family_descends (prefixWord ++ tailWord_887715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887743 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_887743 : Nat := 118140960795 + 887743 * 2 ^ 59
def prefixEnd_887743 : Nat := 4983230072969 + 3 ^ 40 * 887743 * 2
def baseEnd_887743 : Nat := 405190094812822609004311

theorem tailTrace_887743 : CollatzResearch.WordTrace tailWord_887743 prefixEnd_887743 405190094812822609004311 := by
  unfold tailWord_887743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32378647222866200278867883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21585764815244133519245255 32378647222866200278867883)
  ·
    refine ⟨48567970834299300418301825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32378647222866200278867883 48567970834299300418301825)
    ·
      refine ⟨36425978125724475313726369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48567970834299300418301825 36425978125724475313726369)
      ·
        refine ⟨27319483594293356485294777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36425978125724475313726369 27319483594293356485294777)
        ·
          refine ⟨20489612695720017363971083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27319483594293356485294777 20489612695720017363971083)
          ·
            refine ⟨30734419043580026045956625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489612695720017363971083 30734419043580026045956625)
            ·
              refine ⟨23050814282685019534467469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30734419043580026045956625 23050814282685019534467469)
              ·
                refine ⟨8644055356006882325425301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23050814282685019534467469 8644055356006882325425301)
                ·
                  refine ⟨405190094812822609004311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8644055356006882325425301 405190094812822609004311)
                  ·
                    rfl

theorem cell20_887743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_887743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887743 prefixEnd_887743 := by exact prefixLift 887743
  have htrace : WordTrace (prefixWord ++ tailWord_887743) baseStart_887743 baseEnd_887743 := by
    simpa [prefixWord, tailWord_887743, baseEnd_887743] using wordTrace_append hprefix tailTrace_887743
  have hstable : (prefixWord ++ tailWord_887743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887743).length < 2 ^ (prefixWord ++ tailWord_887743).sum := by decide
  have hdescent : baseEnd_887743 < baseStart_887743 := by decide
  rcases family_descends (prefixWord ++ tailWord_887743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887773 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 2]
def baseStart_887773 : Nat := 118140960795 + 887773 * 2 ^ 59
def prefixEnd_887773 : Nat := 4983230072969 + 3 ^ 40 * 887773 * 2
def baseEnd_887773 : Nat := 405203787630275838004189

theorem tailTrace_887773 : CollatzResearch.WordTrace tailWord_887773 prefixEnd_887773 405203787630275838004189 := by
  unfold tailWord_887773
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379741412757515402459973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21586494275171676934973315 32379741412757515402459973)
  ·
    refine ⟨6071201514892034137961245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32379741412757515402459973 6071201514892034137961245)
    ·
      refine ⟨2276700568084512801735467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6071201514892034137961245 2276700568084512801735467)
      ·
        refine ⟨3415050852126769202603201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276700568084512801735467 3415050852126769202603201)
        ·
          refine ⟨2561288139095076901952401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3415050852126769202603201 2561288139095076901952401)
          ·
            refine ⟨1920966104321307676464301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2561288139095076901952401 1920966104321307676464301)
            ·
              refine ⟨720362289120490378674113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920966104321307676464301 720362289120490378674113)
              ·
                refine ⟨540271716840367784005585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720362289120490378674113 540271716840367784005585)
                ·
                  refine ⟨405203787630275838004189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540271716840367784005585 405203787630275838004189)
                  ·
                    rfl

theorem cell20_887773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_887773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887773 prefixEnd_887773 := by exact prefixLift 887773
  have htrace : WordTrace (prefixWord ++ tailWord_887773) baseStart_887773 baseEnd_887773 := by
    simpa [prefixWord, tailWord_887773, baseEnd_887773] using wordTrace_append hprefix tailTrace_887773
  have hstable : (prefixWord ++ tailWord_887773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887773).length < 2 ^ (prefixWord ++ tailWord_887773).sum := by decide
  have hdescent : baseEnd_887773 < baseStart_887773 := by decide
  rcases family_descends (prefixWord ++ tailWord_887773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887791 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_887791 : Nat := 118140960795 + 887791 * 2 ^ 59
def prefixEnd_887791 : Nat := 4983230072969 + 3 ^ 40 * 887791 * 2
def baseEnd_887791 : Nat := 405212003320747775404115

theorem tailTrace_887791 : CollatzResearch.WordTrace tailWord_887791 prefixEnd_887791 405212003320747775404115 := by
  unfold tailWord_887791
  simp only [CollatzResearch.WordTrace]
  refine ⟨32380397926692304476615227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21586931951128202984410151 32380397926692304476615227)
  ·
    refine ⟨48570596890038456714922841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32380397926692304476615227 48570596890038456714922841)
    ·
      refine ⟨36427947667528842536192131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48570596890038456714922841 36427947667528842536192131)
      ·
        refine ⟨54641921501293263804288197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36427947667528842536192131 54641921501293263804288197)
        ·
          refine ⟨10245360281492486963304037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54641921501293263804288197 10245360281492486963304037)
          ·
            refine ⟨1921005052779841305619507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10245360281492486963304037 1921005052779841305619507)
            ·
              refine ⟨2881507579169761958429261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921005052779841305619507 2881507579169761958429261)
              ·
                refine ⟨1080565342188660734410973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2881507579169761958429261 1080565342188660734410973)
                ·
                  refine ⟨405212003320747775404115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080565342188660734410973 405212003320747775404115)
                  ·
                    rfl

theorem cell20_887791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_887791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887791 prefixEnd_887791 := by exact prefixLift 887791
  have htrace : WordTrace (prefixWord ++ tailWord_887791) baseStart_887791 baseEnd_887791 := by
    simpa [prefixWord, tailWord_887791, baseEnd_887791] using wordTrace_append hprefix tailTrace_887791
  have hstable : (prefixWord ++ tailWord_887791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887791).length < 2 ^ (prefixWord ++ tailWord_887791).sum := by decide
  have hdescent : baseEnd_887791 < baseStart_887791 := by decide
  rcases family_descends (prefixWord ++ tailWord_887791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887815 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 2]
def baseStart_887815 : Nat := 118140960795 + 887815 * 2 ^ 59
def prefixEnd_887815 : Nat := 4983230072969 + 3 ^ 40 * 887815 * 2
def baseEnd_887815 : Nat := 405222957574710358604017

theorem tailTrace_887815 : CollatzResearch.WordTrace tailWord_887815 prefixEnd_887815 405222957574710358604017 := by
  unfold tailWord_887815
  simp only [CollatzResearch.WordTrace]
  refine ⟨32381273278605356575488899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21587515519070237716992599 32381273278605356575488899)
  ·
    refine ⟨48571909917908034863233349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32381273278605356575488899 48571909917908034863233349)
    ·
      refine ⟨9107233109607756536856253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48571909917908034863233349 9107233109607756536856253)
      ·
        refine ⟨3415212416102908701321095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9107233109607756536856253 3415212416102908701321095)
        ·
          refine ⟨5122818624154363051981643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415212416102908701321095 5122818624154363051981643)
          ·
            refine ⟨7684227936231544577972465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122818624154363051981643 7684227936231544577972465)
            ·
              refine ⟨5763170952173658433479349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7684227936231544577972465 5763170952173658433479349)
              ·
                refine ⟨540297276766280478138689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5763170952173658433479349 540297276766280478138689)
                ·
                  refine ⟨405222957574710358604017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540297276766280478138689 405222957574710358604017)
                  ·
                    rfl

theorem cell20_887815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2].length) (baseStart_887815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887815 prefixEnd_887815 := by exact prefixLift 887815
  have htrace : WordTrace (prefixWord ++ tailWord_887815) baseStart_887815 baseEnd_887815 := by
    simpa [prefixWord, tailWord_887815, baseEnd_887815] using wordTrace_append hprefix tailTrace_887815
  have hstable : (prefixWord ++ tailWord_887815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887815).length < 2 ^ (prefixWord ++ tailWord_887815).sum := by decide
  have hdescent : baseEnd_887815 < baseStart_887815 := by decide
  rcases family_descends (prefixWord ++ tailWord_887815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887829 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_887829 : Nat := 118140960795 + 887829 * 2 ^ 59
def prefixEnd_887829 : Nat := 4983230072969 + 3 ^ 40 * 887829 * 2
def baseEnd_887829 : Nat := 405229347556188532137293

theorem tailTrace_887829 : CollatzResearch.WordTrace tailWord_887829 prefixEnd_887829 405229347556188532137293 := by
  unfold tailWord_887829
  simp only [CollatzResearch.WordTrace]
  refine ⟨32381783900554636966498541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21587855933703091310999027 32381783900554636966498541)
  ·
    refine ⟨12143168962707988862436953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32381783900554636966498541 12143168962707988862436953)
    ·
      refine ⟨9107376722030991646827715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12143168962707988862436953 9107376722030991646827715)
      ·
        refine ⟨13661065083046487470241573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107376722030991646827715 13661065083046487470241573)
        ·
          refine ⟨2561449703071216400670295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13661065083046487470241573 2561449703071216400670295)
          ·
            refine ⟨3842174554606824601005443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561449703071216400670295 3842174554606824601005443)
            ·
              refine ⟨5763261831910236901508165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842174554606824601005443 5763261831910236901508165)
              ·
                refine ⟨1080611593483169419032781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5763261831910236901508165 1080611593483169419032781)
                ·
                  refine ⟨405229347556188532137293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080611593483169419032781 405229347556188532137293)
                  ·
                    rfl

theorem cell20_887829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_887829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887829 prefixEnd_887829 := by exact prefixLift 887829
  have htrace : WordTrace (prefixWord ++ tailWord_887829) baseStart_887829 baseEnd_887829 := by
    simpa [prefixWord, tailWord_887829, baseEnd_887829] using wordTrace_append hprefix tailTrace_887829
  have hstable : (prefixWord ++ tailWord_887829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887829).length < 2 ^ (prefixWord ++ tailWord_887829).sum := by decide
  have hdescent : baseEnd_887829 < baseStart_887829 := by decide
  rcases family_descends (prefixWord ++ tailWord_887829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887832 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_887832 : Nat := 118140960795 + 887832 * 2 ^ 59
def prefixEnd_887832 : Nat := 4983230072969 + 3 ^ 40 * 887832 * 2
def baseEnd_887832 : Nat := 405230716837933855037281

theorem tailTrace_887832 : CollatzResearch.WordTrace tailWord_887832 prefixEnd_887832 405230716837933855037281 := by
  unfold tailWord_887832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16190946659771884239428875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21587928879695845652571833 16190946659771884239428875)
  ·
    refine ⟨24286419989657826359143313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16190946659771884239428875 24286419989657826359143313)
    ·
      refine ⟨18214814992243369769357485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24286419989657826359143313 18214814992243369769357485)
      ·
        refine ⟨6830555622091263663509057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18214814992243369769357485 6830555622091263663509057)
        ·
          refine ⟨5122916716568447747631793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6830555622091263663509057 5122916716568447747631793)
          ·
            refine ⟨3842187537426335810723845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122916716568447747631793 3842187537426335810723845)
            ·
              refine ⟨720410163267437964510721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3842187537426335810723845 720410163267437964510721)
              ·
                refine ⟨540307622450578473383041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720410163267437964510721 540307622450578473383041)
                ·
                  refine ⟨405230716837933855037281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540307622450578473383041 405230716837933855037281)
                  ·
                    rfl

theorem cell20_887832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_887832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887832 prefixEnd_887832 := by exact prefixLift 887832
  have htrace : WordTrace (prefixWord ++ tailWord_887832) baseStart_887832 baseEnd_887832 := by
    simpa [prefixWord, tailWord_887832, baseEnd_887832] using wordTrace_append hprefix tailTrace_887832
  have hstable : (prefixWord ++ tailWord_887832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887832).length < 2 ^ (prefixWord ++ tailWord_887832).sum := by decide
  have hdescent : baseEnd_887832 < baseStart_887832 := by decide
  rcases family_descends (prefixWord ++ tailWord_887832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887843 : List Nat := [1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_887843 : Nat := 118140960795 + 887843 * 2 ^ 59
def prefixEnd_887843 : Nat := 4983230072969 + 3 ^ 40 * 887843 * 2
def baseEnd_887843 : Nat := 135078579179222235223523

theorem tailTrace_887843 : CollatzResearch.WordTrace tailWord_887843 prefixEnd_887843 135078579179222235223523 := by
  unfold tailWord_887843
  simp only [CollatzResearch.WordTrace]
  refine ⟨32382294522503917357508183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21588196348335944905005455 32382294522503917357508183)
  ·
    refine ⟨48573441783755876036262275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32382294522503917357508183 48573441783755876036262275)
    ·
      refine ⟨72860162675633814054393413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48573441783755876036262275 72860162675633814054393413)
      ·
        refine ⟨13661280501681340135198765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72860162675633814054393413 13661280501681340135198765)
        ·
          refine ⟨5122980188130502550699537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13661280501681340135198765 5122980188130502550699537)
          ·
            refine ⟨3842235141097876913024653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122980188130502550699537 3842235141097876913024653)
            ·
              refine ⟨1440838177911703842384245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3842235141097876913024653 1440838177911703842384245)
              ·
                refine ⟨135078579179222235223523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1440838177911703842384245 135078579179222235223523)
                ·
                  rfl

theorem cell20_887843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_887843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887843 prefixEnd_887843 := by exact prefixLift 887843
  have htrace : WordTrace (prefixWord ++ tailWord_887843) baseStart_887843 baseEnd_887843 := by
    simpa [prefixWord, tailWord_887843, baseEnd_887843] using wordTrace_append hprefix tailTrace_887843
  have hstable : (prefixWord ++ tailWord_887843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887843).length < 2 ^ (prefixWord ++ tailWord_887843).sum := by decide
  have hdescent : baseEnd_887843 < baseStart_887843 := by decide
  rcases family_descends (prefixWord ++ tailWord_887843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887870 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_887870 : Nat := 118140960795 + 887870 * 2 ^ 59
def prefixEnd_887870 : Nat := 4983230072969 + 3 ^ 40 * 887870 * 2
def baseEnd_887870 : Nat := 405248061073374611770459

theorem tailTrace_887870 : CollatzResearch.WordTrace tailWord_887870 prefixEnd_887870 405248061073374611770459 := by
  unfold tailWord_887870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047909911675762621092633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21588852862270733979160709 4047909911675762621092633)
  ·
    refine ⟨3035932433756821965819475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4047909911675762621092633 3035932433756821965819475)
    ·
      refine ⟨4553898650635232948729213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035932433756821965819475 4553898650635232948729213)
      ·
        refine ⟨1707711993988212355773455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4553898650635232948729213 1707711993988212355773455)
        ·
          refine ⟨2561567990982318533660183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707711993988212355773455 2561567990982318533660183)
          ·
            refine ⟨3842351986473477800490275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561567990982318533660183 3842351986473477800490275)
            ·
              refine ⟨5763527979710216700735413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842351986473477800490275 5763527979710216700735413)
              ·
                refine ⟨540330748097832815693945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5763527979710216700735413 540330748097832815693945)
                ·
                  refine ⟨405248061073374611770459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540330748097832815693945 405248061073374611770459)
                  ·
                    rfl

theorem cell20_887870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_887870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887870 prefixEnd_887870 := by exact prefixLift 887870
  have htrace : WordTrace (prefixWord ++ tailWord_887870) baseStart_887870 baseEnd_887870 := by
    simpa [prefixWord, tailWord_887870, baseEnd_887870] using wordTrace_append hprefix tailTrace_887870
  have hstable : (prefixWord ++ tailWord_887870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887870).length < 2 ^ (prefixWord ++ tailWord_887870).sum := by decide
  have hdescent : baseEnd_887870 < baseStart_887870 := by decide
  rcases family_descends (prefixWord ++ tailWord_887870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887946 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_887946 : Nat := 118140960795 + 887946 * 2 ^ 59
def prefixEnd_887946 : Nat := 4983230072969 + 3 ^ 40 * 887946 * 2
def baseEnd_887946 : Nat := 405282749544256125236815

theorem tailTrace_887946 : CollatzResearch.WordTrace tailWord_887946 prefixEnd_887946 405282749544256125236815 := by
  unfold tailWord_887946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096512810282691487126923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21590700827420510632338461 8096512810282691487126923)
  ·
    refine ⟨12144769215424037230690385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8096512810282691487126923 12144769215424037230690385)
    ·
      refine ⟨9108576911568027923017789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12144769215424037230690385 9108576911568027923017789)
      ·
        refine ⟨3415716341838010471131671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9108576911568027923017789 3415716341838010471131671)
        ·
          refine ⟨5123574512757015706697507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415716341838010471131671 5123574512757015706697507)
          ·
            refine ⟨7685361769135523560046261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123574512757015706697507 7685361769135523560046261)
            ·
              refine ⟨720502665856455333754337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7685361769135523560046261 720502665856455333754337)
              ·
                refine ⟨540376999392341500315753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720502665856455333754337 540376999392341500315753)
                ·
                  refine ⟨405282749544256125236815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540376999392341500315753 405282749544256125236815)
                  ·
                    rfl

theorem cell20_887946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_887946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887946 prefixEnd_887946 := by exact prefixLift 887946
  have htrace : WordTrace (prefixWord ++ tailWord_887946) baseStart_887946 baseEnd_887946 := by
    simpa [prefixWord, tailWord_887946, baseEnd_887946] using wordTrace_append hprefix tailTrace_887946
  have hstable : (prefixWord ++ tailWord_887946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887946).length < 2 ^ (prefixWord ++ tailWord_887946).sum := by decide
  have hdescent : baseEnd_887946 < baseStart_887946 := by decide
  rcases family_descends (prefixWord ++ tailWord_887946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887960 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_887960 : Nat := 118140960795 + 887960 * 2 ^ 59
def prefixEnd_887960 : Nat := 4983230072969 + 3 ^ 40 * 887960 * 2
def baseEnd_887960 : Nat := 405289139525734298770091

theorem tailTrace_887960 : CollatzResearch.WordTrace tailWord_887960 prefixEnd_887960 405289139525734298770091 := by
  unfold tailWord_887960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16193280931540023169758667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21591041242053364226344889 16193280931540023169758667)
  ·
    refine ⟨24289921397310034754638001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16193280931540023169758667 24289921397310034754638001)
    ·
      refine ⟨18217441047982526065978501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24289921397310034754638001 18217441047982526065978501)
      ·
        refine ⟨3415770196496723637370969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18217441047982526065978501 3415770196496723637370969)
        ·
          refine ⟨2561827647372542728028227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3415770196496723637370969 2561827647372542728028227)
          ·
            refine ⟨3842741471058814092042341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561827647372542728028227 3842741471058814092042341)
            ·
              refine ⟨720514025823527642257939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3842741471058814092042341 720514025823527642257939)
              ·
                refine ⟨1080771038735291463386909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720514025823527642257939 1080771038735291463386909)
                ·
                  refine ⟨405289139525734298770091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080771038735291463386909 405289139525734298770091)
                  ·
                    rfl

theorem cell20_887960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_887960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887960 prefixEnd_887960 := by exact prefixLift 887960
  have htrace : WordTrace (prefixWord ++ tailWord_887960) baseStart_887960 baseEnd_887960 := by
    simpa [prefixWord, tailWord_887960, baseEnd_887960] using wordTrace_append hprefix tailTrace_887960
  have hstable : (prefixWord ++ tailWord_887960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887960).length < 2 ^ (prefixWord ++ tailWord_887960).sum := by decide
  have hdescent : baseEnd_887960 < baseStart_887960 := by decide
  rcases family_descends (prefixWord ++ tailWord_887960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887971 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_887971 : Nat := 118140960795 + 887971 * 2 ^ 59
def prefixEnd_887971 : Nat := 4983230072969 + 3 ^ 40 * 887971 * 2
def baseEnd_887971 : Nat := 405294160225467149403379

theorem tailTrace_887971 : CollatzResearch.WordTrace tailWord_887971 prefixEnd_887971 405294160225467149403379 := by
  unfold tailWord_887971
  simp only [CollatzResearch.WordTrace]
  refine ⟨32386963066040195218167767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21591308710693463478778511 32386963066040195218167767)
  ·
    refine ⟨48580444599060292827251651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32386963066040195218167767 48580444599060292827251651)
    ·
      refine ⟨72870666898590439240877477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48580444599060292827251651 72870666898590439240877477)
      ·
        refine ⟨13663250043485707357664527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72870666898590439240877477 13663250043485707357664527)
        ·
          refine ⟨20494875065228561036496791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663250043485707357664527 20494875065228561036496791)
          ·
            refine ⟨30742312597842841554745187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20494875065228561036496791 30742312597842841554745187)
            ·
              refine ⟨46113468896764262332117781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30742312597842841554745187 46113468896764262332117781)
              ·
                refine ⟨2161568854535824796818021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46113468896764262332117781 2161568854535824796818021)
                ·
                  refine ⟨405294160225467149403379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161568854535824796818021 405294160225467149403379)
                  ·
                    rfl

theorem cell20_887971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_887971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887971 prefixEnd_887971 := by exact prefixLift 887971
  have htrace : WordTrace (prefixWord ++ tailWord_887971) baseStart_887971 baseEnd_887971 := by
    simpa [prefixWord, tailWord_887971, baseEnd_887971] using wordTrace_append hprefix tailTrace_887971
  have hstable : (prefixWord ++ tailWord_887971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887971).length < 2 ^ (prefixWord ++ tailWord_887971).sum := by decide
  have hdescent : baseEnd_887971 < baseStart_887971 := by decide
  rcases family_descends (prefixWord ++ tailWord_887971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887998 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_887998 : Nat := 118140960795 + 887998 * 2 ^ 59
def prefixEnd_887998 : Nat := 4983230072969 + 3 ^ 40 * 887998 * 2
def baseEnd_887998 : Nat := 405306483761175055503269

theorem tailTrace_887998 : CollatzResearch.WordTrace tailWord_887998 prefixEnd_887998 405306483761175055503269 := by
  unfold tailWord_887998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048493479617797353675081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21591965224628252552933765 4048493479617797353675081)
  ·
    refine ⟨3036370109713348015256311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4048493479617797353675081 3036370109713348015256311)
    ·
      refine ⟨4554555164570022022884467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3036370109713348015256311 4554555164570022022884467)
      ·
        refine ⟨6831832746855033034326701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554555164570022022884467 6831832746855033034326701)
        ·
          refine ⟨2561937280070637387872513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6831832746855033034326701 2561937280070637387872513)
          ·
            refine ⟨1921452960052978040904385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2561937280070637387872513 1921452960052978040904385)
            ·
              refine ⟨1441089720039733530678289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921452960052978040904385 1441089720039733530678289)
              ·
                refine ⟨1080817290029800148008717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441089720039733530678289 1080817290029800148008717)
                ·
                  refine ⟨405306483761175055503269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080817290029800148008717 405306483761175055503269)
                  ·
                    rfl

theorem cell20_887998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_887998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_887998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_887998 prefixEnd_887998 := by exact prefixLift 887998
  have htrace : WordTrace (prefixWord ++ tailWord_887998) baseStart_887998 baseEnd_887998 := by
    simpa [prefixWord, tailWord_887998, baseEnd_887998] using wordTrace_append hprefix tailTrace_887998
  have hstable : (prefixWord ++ tailWord_887998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887998).length < 2 ^ (prefixWord ++ tailWord_887998).sum := by decide
  have hdescent : baseEnd_887998 < baseStart_887998 := by decide
  rcases family_descends (prefixWord ++ tailWord_887998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888001 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 2]
def baseStart_888001 : Nat := 118140960795 + 888001 * 2 ^ 59
def prefixEnd_888001 : Nat := 4983230072969 + 3 ^ 40 * 888001 * 2
def baseEnd_888001 : Nat := 405307853042920378403257

theorem tailTrace_888001 : CollatzResearch.WordTrace tailWord_888001 prefixEnd_888001 405307853042920378403257 := by
  unfold tailWord_888001
  simp only [CollatzResearch.WordTrace]
  refine ⟨32388057255931510341759857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21592038170621006894506571 32388057255931510341759857)
  ·
    refine ⟨24291042941948632756319893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32388057255931510341759857 24291042941948632756319893)
    ·
      refine ⟨1138642637903842160452495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24291042941948632756319893 1138642637903842160452495)
      ·
        refine ⟨1707963956855763240678743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138642637903842160452495 1707963956855763240678743)
        ·
          refine ⟨2561945935283644861018115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707963956855763240678743 2561945935283644861018115)
          ·
            refine ⟨3842918902925467291527173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561945935283644861018115 3842918902925467291527173)
            ·
              refine ⟨720547294298525117161345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3842918902925467291527173 720547294298525117161345)
              ·
                refine ⟨540410470723893837871009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720547294298525117161345 540410470723893837871009)
                ·
                  refine ⟨405307853042920378403257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540410470723893837871009 405307853042920378403257)
                  ·
                    rfl

theorem cell20_888001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_888001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888001 prefixEnd_888001 := by exact prefixLift 888001
  have htrace : WordTrace (prefixWord ++ tailWord_888001) baseStart_888001 baseEnd_888001 := by
    simpa [prefixWord, tailWord_888001, baseEnd_888001] using wordTrace_append hprefix tailTrace_888001
  have hstable : (prefixWord ++ tailWord_888001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888001).length < 2 ^ (prefixWord ++ tailWord_888001).sum := by decide
  have hdescent : baseEnd_888001 < baseStart_888001 := by decide
  rcases family_descends (prefixWord ++ tailWord_888001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888022 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_888022 : Nat := 118140960795 + 888022 * 2 ^ 59
def prefixEnd_888022 : Nat := 4983230072969 + 3 ^ 40 * 888022 * 2
def baseEnd_888022 : Nat := 405317438015137638703171

theorem tailTrace_888022 : CollatzResearch.WordTrace tailWord_888022 prefixEnd_888022 405317438015137638703171 := by
  unfold tailWord_888022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024301449303464433017145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21592548792570287285516213 2024301449303464433017145)
  ·
    refine ⟨1518226086977598324762859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2024301449303464433017145 1518226086977598324762859)
    ·
      refine ⟨2277339130466397487144289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518226086977598324762859 2277339130466397487144289)
      ·
        refine ⟨1708004347849798115358217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277339130466397487144289 1708004347849798115358217)
        ·
          refine ⟨1281003260887348586518663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708004347849798115358217 1281003260887348586518663)
          ·
            refine ⟨1921504891331022879777995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281003260887348586518663 1921504891331022879777995)
            ·
              refine ⟨2882257336996534319666993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921504891331022879777995 2882257336996534319666993)
              ·
                refine ⟨2161693002747400739750245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882257336996534319666993 2161693002747400739750245)
                ·
                  refine ⟨405317438015137638703171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2161693002747400739750245 405317438015137638703171)
                  ·
                    rfl

theorem cell20_888022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_888022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888022 prefixEnd_888022 := by exact prefixLift 888022
  have htrace : WordTrace (prefixWord ++ tailWord_888022) baseStart_888022 baseEnd_888022 := by
    simpa [prefixWord, tailWord_888022, baseEnd_888022] using wordTrace_append hprefix tailTrace_888022
  have hstable : (prefixWord ++ tailWord_888022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888022).length < 2 ^ (prefixWord ++ tailWord_888022).sum := by decide
  have hdescent : baseEnd_888022 < baseStart_888022 := by decide
  rcases family_descends (prefixWord ++ tailWord_888022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888029 : List Nat := [1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_888029 : Nat := 118140960795 + 888029 * 2 ^ 59
def prefixEnd_888029 : Nat := 4983230072969 + 3 ^ 40 * 888029 * 2
def baseEnd_888029 : Nat := 135106877668625575156603

theorem tailTrace_888029 : CollatzResearch.WordTrace tailWord_888029 prefixEnd_888029 135106877668625575156603 := by
  unfold tailWord_888029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32389078499830071123779141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21592718999886714082519427 32389078499830071123779141)
  ·
    refine ⟨6072952218718138335708589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32389078499830071123779141 6072952218718138335708589)
    ·
      refine ⟨2277357082019301875890721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6072952218718138335708589 2277357082019301875890721)
      ·
        refine ⟨1708017811514476406918041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277357082019301875890721 1708017811514476406918041)
        ·
          refine ⟨1281013358635857305188531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708017811514476406918041 1281013358635857305188531)
          ·
            refine ⟨1921520037953785957782797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281013358635857305188531 1921520037953785957782797)
            ·
              refine ⟨720570014232669734168549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1921520037953785957782797 720570014232669734168549)
              ·
                refine ⟨135106877668625575156603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720570014232669734168549 135106877668625575156603)
                ·
                  rfl

theorem cell20_888029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_888029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888029 prefixEnd_888029 := by exact prefixLift 888029
  have htrace : WordTrace (prefixWord ++ tailWord_888029) baseStart_888029 baseEnd_888029 := by
    simpa [prefixWord, tailWord_888029, baseEnd_888029] using wordTrace_append hprefix tailTrace_888029
  have hstable : (prefixWord ++ tailWord_888029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888029).length < 2 ^ (prefixWord ++ tailWord_888029).sum := by decide
  have hdescent : baseEnd_888029 < baseStart_888029 := by decide
  rcases family_descends (prefixWord ++ tailWord_888029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888040 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_888040 : Nat := 118140960795 + 888040 * 2 ^ 59
def prefixEnd_888040 : Nat := 4983230072969 + 3 ^ 40 * 888040 * 2
def baseEnd_888040 : Nat := 405325653705609576103097

theorem tailTrace_888040 : CollatzResearch.WordTrace tailWord_888040 prefixEnd_888040 405325653705609576103097 := by
  unfold tailWord_888040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194739851395110001214787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21592986468526813334953049 16194739851395110001214787)
  ·
    refine ⟨24292109777092665001822181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194739851395110001214787 24292109777092665001822181)
    ·
      refine ⟨4554770583204874687841659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24292109777092665001822181 4554770583204874687841659)
      ·
        refine ⟨6832155874807312031762489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554770583204874687841659 6832155874807312031762489)
        ·
          refine ⟨5124116906105484023821867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6832155874807312031762489 5124116906105484023821867)
          ·
            refine ⟨7686175359158226035732801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124116906105484023821867 7686175359158226035732801)
            ·
              refine ⟨5764631519368669526799601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686175359158226035732801 5764631519368669526799601)
              ·
                refine ⟨4323473639526502145099701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5764631519368669526799601 4323473639526502145099701)
                ·
                  refine ⟨405325653705609576103097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4323473639526502145099701 405325653705609576103097)
                  ·
                    rfl

theorem cell20_888040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_888040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888040 prefixEnd_888040 := by exact prefixLift 888040
  have htrace : WordTrace (prefixWord ++ tailWord_888040) baseStart_888040 baseEnd_888040 := by
    simpa [prefixWord, tailWord_888040, baseEnd_888040] using wordTrace_append hprefix tailTrace_888040
  have hstable : (prefixWord ++ tailWord_888040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888040).length < 2 ^ (prefixWord ++ tailWord_888040).sum := by decide
  have hdescent : baseEnd_888040 < baseStart_888040 := by decide
  rcases family_descends (prefixWord ++ tailWord_888040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888043 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 2]
def baseStart_888043 : Nat := 118140960795 + 888043 * 2 ^ 59
def prefixEnd_888043 : Nat := 4983230072969 + 3 ^ 40 * 888043 * 2
def baseEnd_888043 : Nat := 405327022987354899003085

theorem tailTrace_888043 : CollatzResearch.WordTrace tailWord_888043 prefixEnd_888043 405327022987354899003085 := by
  unfold tailWord_888043
  simp only [CollatzResearch.WordTrace]
  refine ⟨32389589121779351514788783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21593059414519567676525855 32389589121779351514788783)
  ·
    refine ⟨48584383682669027272183175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32389589121779351514788783 48584383682669027272183175)
    ·
      refine ⟨72876575524003540908274763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48584383682669027272183175 72876575524003540908274763)
      ·
        refine ⟨109314863286005311362412145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72876575524003540908274763 109314863286005311362412145)
        ·
          refine ⟨81986147464503983521809109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109314863286005311362412145 81986147464503983521809109)
          ·
            refine ⟨1921550331199312113792401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81986147464503983521809109 1921550331199312113792401)
            ·
              refine ⟨1441162748399484085344301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921550331199312113792401 1441162748399484085344301)
              ·
                refine ⟨540436030649806532004113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441162748399484085344301 540436030649806532004113)
                ·
                  refine ⟨405327022987354899003085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540436030649806532004113 405327022987354899003085)
                  ·
                    rfl

theorem cell20_888043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2].length) (baseStart_888043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888043 prefixEnd_888043 := by exact prefixLift 888043
  have htrace : WordTrace (prefixWord ++ tailWord_888043) baseStart_888043 baseEnd_888043 := by
    simpa [prefixWord, tailWord_888043, baseEnd_888043] using wordTrace_append hprefix tailTrace_888043
  have hstable : (prefixWord ++ tailWord_888043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888043).length < 2 ^ (prefixWord ++ tailWord_888043).sum := by decide
  have hdescent : baseEnd_888043 < baseStart_888043 := by decide
  rcases family_descends (prefixWord ++ tailWord_888043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888088 : List Nat := [2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_888088 : Nat := 118140960795 + 888088 * 2 ^ 59
def prefixEnd_888088 : Nat := 4983230072969 + 3 ^ 40 * 888088 * 2
def baseEnd_888088 : Nat := 135115854071178247500967

theorem tailTrace_888088 : CollatzResearch.WordTrace tailWord_888088 prefixEnd_888088 135115854071178247500967 := by
  unfold tailWord_888088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16195615203308162100088459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21594153604410882800117945 16195615203308162100088459)
  ·
    refine ⟨24293422804962243150132689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16195615203308162100088459 24293422804962243150132689)
    ·
      refine ⟨18220067103721682362599517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24293422804962243150132689 18220067103721682362599517)
      ·
        refine ⟨6832525163895630885974819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18220067103721682362599517 6832525163895630885974819)
        ·
          refine ⟨10248787745843446328962229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832525163895630885974819 10248787745843446328962229)
          ·
            refine ⟨960823851172823093340209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10248787745843446328962229 960823851172823093340209)
            ·
              refine ⟨720617888379617320005157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960823851172823093340209 720617888379617320005157)
              ·
                refine ⟨135115854071178247500967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720617888379617320005157 135115854071178247500967)
                ·
                  rfl

theorem cell20_888088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_888088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888088 prefixEnd_888088 := by exact prefixLift 888088
  have htrace : WordTrace (prefixWord ++ tailWord_888088) baseStart_888088 baseEnd_888088 := by
    simpa [prefixWord, tailWord_888088, baseEnd_888088] using wordTrace_append hprefix tailTrace_888088
  have hstable : (prefixWord ++ tailWord_888088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888088).length < 2 ^ (prefixWord ++ tailWord_888088).sum := by decide
  have hdescent : baseEnd_888088 < baseStart_888088 := by decide
  rcases family_descends (prefixWord ++ tailWord_888088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888094 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_888094 : Nat := 118140960795 + 888094 * 2 ^ 59
def prefixEnd_888094 : Nat := 4983230072969 + 3 ^ 40 * 888094 * 2
def baseEnd_888094 : Nat := 405350300777025388302877

theorem tailTrace_888094 : CollatzResearch.WordTrace tailWord_888094 prefixEnd_888094 405350300777025388302877 := by
  unfold tailWord_888094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048931155574323403111917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21594299496396391483263557 4048931155574323403111917)
  ·
    refine ⟨1518349183340371276166969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4048931155574323403111917 1518349183340371276166969)
    ·
      refine ⟨1138761887505278457125227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518349183340371276166969 1138761887505278457125227)
      ·
        refine ⟨1708142831257917685687841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138761887505278457125227 1708142831257917685687841)
        ·
          refine ⟨1281107123443438264265881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708142831257917685687841 1281107123443438264265881)
          ·
            refine ⟨960830342582578698199411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281107123443438264265881 960830342582578698199411)
            ·
              refine ⟨1441245513873868047299117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960830342582578698199411 1441245513873868047299117)
              ·
                refine ⟨540467067702700517737169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441245513873868047299117 540467067702700517737169)
                ·
                  refine ⟨405350300777025388302877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540467067702700517737169 405350300777025388302877)
                  ·
                    rfl

theorem cell20_888094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_888094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888094 prefixEnd_888094 := by exact prefixLift 888094
  have htrace : WordTrace (prefixWord ++ tailWord_888094) baseStart_888094 baseEnd_888094 := by
    simpa [prefixWord, tailWord_888094, baseEnd_888094] using wordTrace_append hprefix tailTrace_888094
  have hstable : (prefixWord ++ tailWord_888094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888094).length < 2 ^ (prefixWord ++ tailWord_888094).sum := by decide
  have hdescent : baseEnd_888094 < baseStart_888094 := by decide
  rcases family_descends (prefixWord ++ tailWord_888094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888129 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 3]
def baseStart_888129 : Nat := 118140960795 + 888129 * 2 ^ 59
def prefixEnd_888129 : Nat := 4983230072969 + 3 ^ 40 * 888129 * 2
def baseEnd_888129 : Nat := 405366275730720822136067

theorem tailTrace_888129 : CollatzResearch.WordTrace tailWord_888129 prefixEnd_888129 405366275730720822136067 := by
  unfold tailWord_888129
  simp only [CollatzResearch.WordTrace]
  refine ⟨32392725799467788202419441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21595150532978525468279627 32392725799467788202419441)
  ·
    refine ⟨24294544349600841151814581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32392725799467788202419441 24294544349600841151814581)
    ·
      refine ⟨2277613532775078857982617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24294544349600841151814581 2277613532775078857982617)
      ·
        refine ⟨1708210149581309143486963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277613532775078857982617 1708210149581309143486963)
        ·
          refine ⟨2562315224371963715230445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708210149581309143486963 2562315224371963715230445)
          ·
            refine ⟨960868209139486393211417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2562315224371963715230445 960868209139486393211417)
            ·
              refine ⟨720651156854614794908563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960868209139486393211417 720651156854614794908563)
              ·
                refine ⟨1080976735281922192362845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720651156854614794908563 1080976735281922192362845)
                ·
                  refine ⟨405366275730720822136067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1080976735281922192362845 405366275730720822136067)
                  ·
                    rfl

theorem cell20_888129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_888129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888129 prefixEnd_888129 := by exact prefixLift 888129
  have htrace : WordTrace (prefixWord ++ tailWord_888129) baseStart_888129 baseEnd_888129 := by
    simpa [prefixWord, tailWord_888129, baseEnd_888129] using wordTrace_append hprefix tailTrace_888129
  have hstable : (prefixWord ++ tailWord_888129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888129).length < 2 ^ (prefixWord ++ tailWord_888129).sum := by decide
  have hdescent : baseEnd_888129 < baseStart_888129 := by decide
  rcases family_descends (prefixWord ++ tailWord_888129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888168 : List Nat := [2, 1, 4, 2, 11]
def baseStart_888168 : Nat := 118140960795 + 888168 * 2 ^ 59
def prefixEnd_888168 : Nat := 4983230072969 + 3 ^ 40 * 888168 * 2
def baseEnd_888168 : Nat := 5004741683869259504147

theorem tailTrace_888168 : CollatzResearch.WordTrace tailWord_888168 prefixEnd_888168 5004741683869259504147 := by
  unfold tailWord_888168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16197074123163248931544579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21596098830884331908726105 16197074123163248931544579)
  ·
    refine ⟨24295611184744873397316869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16197074123163248931544579 24295611184744873397316869)
    ·
      refine ⟨4555427097139663761996913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24295611184744873397316869 4555427097139663761996913)
      ·
        refine ⟨3416570322854747821497685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4555427097139663761996913 3416570322854747821497685)
        ·
          refine ⟨5004741683869259504147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3416570322854747821497685 5004741683869259504147)
          ·
            rfl

theorem cell20_888168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 11].length) (baseStart_888168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888168 prefixEnd_888168 := by exact prefixLift 888168
  have htrace : WordTrace (prefixWord ++ tailWord_888168) baseStart_888168 baseEnd_888168 := by
    simpa [prefixWord, tailWord_888168, baseEnd_888168] using wordTrace_append hprefix tailTrace_888168
  have hstable : (prefixWord ++ tailWord_888168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888168).length < 2 ^ (prefixWord ++ tailWord_888168).sum := by decide
  have hdescent : baseEnd_888168 < baseStart_888168 := by decide
  rcases family_descends (prefixWord ++ tailWord_888168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888170 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_888170 : Nat := 118140960795 + 888170 * 2 ^ 59
def prefixEnd_888170 : Nat := 4983230072969 + 3 ^ 40 * 888170 * 2
def baseEnd_888170 : Nat := 405384989247906901769233

theorem tailTrace_888170 : CollatzResearch.WordTrace tailWord_888170 prefixEnd_888170 405384989247906901769233 := by
  unfold tailWord_888170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098555298079813051165491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21596147461546168136441309 8098555298079813051165491)
  ·
    refine ⟨12147832947119719576748237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098555298079813051165491 12147832947119719576748237)
    ·
      refine ⟨4555437355169894841280589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12147832947119719576748237 4555437355169894841280589)
      ·
        refine ⟨1708289008188710565480221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4555437355169894841280589 1708289008188710565480221)
        ·
          refine ⟨640608378070766462055083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1708289008188710565480221 640608378070766462055083)
          ·
            refine ⟨960912567106149693082625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640608378070766462055083 960912567106149693082625)
            ·
              refine ⟨720684425329612269811969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960912567106149693082625 720684425329612269811969)
              ·
                refine ⟨540513318997209202358977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720684425329612269811969 540513318997209202358977)
                ·
                  refine ⟨405384989247906901769233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540513318997209202358977 405384989247906901769233)
                  ·
                    rfl

theorem cell20_888170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_888170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888170 prefixEnd_888170 := by exact prefixLift 888170
  have htrace : WordTrace (prefixWord ++ tailWord_888170) baseStart_888170 baseEnd_888170 := by
    simpa [prefixWord, tailWord_888170, baseEnd_888170] using wordTrace_append hprefix tailTrace_888170
  have hstable : (prefixWord ++ tailWord_888170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888170).length < 2 ^ (prefixWord ++ tailWord_888170).sum := by decide
  have hdescent : baseEnd_888170 < baseStart_888170 := by decide
  rcases family_descends (prefixWord ++ tailWord_888170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888181 : List Nat := [1, 3, 4, 1, 4, 1, 1, 5]
def baseStart_888181 : Nat := 118140960795 + 888181 * 2 ^ 59
def prefixEnd_888181 : Nat := 4983230072969 + 3 ^ 40 * 888181 * 2
def baseEnd_888181 : Nat := 135130003315879917467507

theorem tailTrace_888181 : CollatzResearch.WordTrace tailWord_888181 prefixEnd_888181 135130003315879917467507 := by
  unfold tailWord_888181
  simp only [CollatzResearch.WordTrace]
  refine ⟨32394622395279401083312397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21596414930186267388874931 32394622395279401083312397)
  ·
    refine ⟨12147983398229775406242149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32394622395279401083312397 12147983398229775406242149)
    ·
      refine ⟨2277746887168082888670403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12147983398229775406242149 2277746887168082888670403)
      ·
        refine ⟨3416620330752124333005605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277746887168082888670403 3416620330752124333005605)
        ·
          refine ⟨640616312016023312438551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3416620330752124333005605 640616312016023312438551)
          ·
            refine ⟨960924468024034968657827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640616312016023312438551 960924468024034968657827)
            ·
              refine ⟨1441386702036052452986741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960924468024034968657827 1441386702036052452986741)
              ·
                refine ⟨135130003315879917467507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1441386702036052452986741 135130003315879917467507)
                ·
                  rfl

theorem cell20_888181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_888181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888181 prefixEnd_888181 := by exact prefixLift 888181
  have htrace : WordTrace (prefixWord ++ tailWord_888181) baseStart_888181 baseEnd_888181 := by
    simpa [prefixWord, tailWord_888181, baseEnd_888181] using wordTrace_append hprefix tailTrace_888181
  have hstable : (prefixWord ++ tailWord_888181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888181).length < 2 ^ (prefixWord ++ tailWord_888181).sum := by decide
  have hdescent : baseEnd_888181 < baseStart_888181 := by decide
  rcases family_descends (prefixWord ++ tailWord_888181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888199 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_888199 : Nat := 118140960795 + 888199 * 2 ^ 59
def prefixEnd_888199 : Nat := 4983230072969 + 3 ^ 40 * 888199 * 2
def baseEnd_888199 : Nat := 405398225638111689802447

theorem tailTrace_888199 : CollatzResearch.WordTrace tailWord_888199 prefixEnd_888199 405398225638111689802447 := by
  unfold tailWord_888199
  simp only [CollatzResearch.WordTrace]
  refine ⟨32395278909214190157467651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21596852606142793438311767 32395278909214190157467651)
  ·
    refine ⟨48592918363821285236201477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32395278909214190157467651 48592918363821285236201477)
    ·
      refine ⟨9111172193216490981787777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48592918363821285236201477 9111172193216490981787777)
      ·
        refine ⟨6833379144912368236340833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9111172193216490981787777 6833379144912368236340833)
        ·
          refine ⟨5125034358684276177255625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6833379144912368236340833 5125034358684276177255625)
          ·
            refine ⟨3843775769013207132941719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5125034358684276177255625 3843775769013207132941719)
            ·
              refine ⟨5765663653519810699412579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843775769013207132941719 5765663653519810699412579)
              ·
                refine ⟨8648495480279716049118869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765663653519810699412579 8648495480279716049118869)
                ·
                  refine ⟨405398225638111689802447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8648495480279716049118869 405398225638111689802447)
                  ·
                    rfl

theorem cell20_888199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_888199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888199 prefixEnd_888199 := by exact prefixLift 888199
  have htrace : WordTrace (prefixWord ++ tailWord_888199) baseStart_888199 baseEnd_888199 := by
    simpa [prefixWord, tailWord_888199, baseEnd_888199] using wordTrace_append hprefix tailTrace_888199
  have hstable : (prefixWord ++ tailWord_888199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888199).length < 2 ^ (prefixWord ++ tailWord_888199).sum := by decide
  have hdescent : baseEnd_888199 < baseStart_888199 := by decide
  rcases family_descends (prefixWord ++ tailWord_888199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888212 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_888212 : Nat := 118140960795 + 888212 * 2 ^ 59
def prefixEnd_888212 : Nat := 4983230072969 + 3 ^ 40 * 888212 * 2
def baseEnd_888212 : Nat := 405404159192341422369061

theorem tailTrace_888212 : CollatzResearch.WordTrace tailWord_888212 prefixEnd_888212 405404159192341422369061 := by
  unfold tailWord_888212
  simp only [CollatzResearch.WordTrace]
  refine ⟨16197876529083546688845445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21597168705444728918460593 16197876529083546688845445)
  ·
    refine ⟨3037101849203165004158521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16197876529083546688845445 3037101849203165004158521)
    ·
      refine ⟨2277826386902373753118891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3037101849203165004158521 2277826386902373753118891)
      ·
        refine ⟨3416739580353560629678337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277826386902373753118891 3416739580353560629678337)
        ·
          refine ⟨2562554685265170472258753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3416739580353560629678337 2562554685265170472258753)
          ·
            refine ⟨1921916013948877854194065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562554685265170472258753 1921916013948877854194065)
            ·
              refine ⟨1441437010461658390645549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921916013948877854194065 1441437010461658390645549)
              ·
                refine ⟨540538878923121896492081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441437010461658390645549 540538878923121896492081)
                ·
                  refine ⟨405404159192341422369061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540538878923121896492081 405404159192341422369061)
                  ·
                    rfl

theorem cell20_888212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_888212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888212 prefixEnd_888212 := by exact prefixLift 888212
  have htrace : WordTrace (prefixWord ++ tailWord_888212) baseStart_888212 baseEnd_888212 := by
    simpa [prefixWord, tailWord_888212, baseEnd_888212] using wordTrace_append hprefix tailTrace_888212
  have hstable : (prefixWord ++ tailWord_888212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888212).length < 2 ^ (prefixWord ++ tailWord_888212).sum := by decide
  have hdescent : baseEnd_888212 < baseStart_888212 := by decide
  rcases family_descends (prefixWord ++ tailWord_888212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888222 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_888222 : Nat := 118140960795 + 888222 * 2 ^ 59
def prefixEnd_888222 : Nat := 4983230072969 + 3 ^ 40 * 888222 * 2
def baseEnd_888222 : Nat := 405408723464825832035687

theorem tailTrace_888222 : CollatzResearch.WordTrace tailWord_888222 prefixEnd_888222 405408723464825832035687 := by
  unfold tailWord_888222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049514723516358135694365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21597411858753910057036613 4049514723516358135694365)
  ·
    refine ⟨1518568021318634300885387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4049514723516358135694365 1518568021318634300885387)
    ·
      refine ⟨2277852031977951451328081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518568021318634300885387 2277852031977951451328081)
      ·
        refine ⟨1708389023983463588496061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277852031977951451328081 1708389023983463588496061)
        ·
          refine ⟨640645883993798845686023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1708389023983463588496061 640645883993798845686023)
          ·
            refine ⟨960968825990698268529035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640645883993798845686023 960968825990698268529035)
            ·
              refine ⟨1441453238986047402793553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960968825990698268529035 1441453238986047402793553)
              ·
                refine ⟨1081089929239535552095165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441453238986047402793553 1081089929239535552095165)
                ·
                  refine ⟨405408723464825832035687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081089929239535552095165 405408723464825832035687)
                  ·
                    rfl

theorem cell20_888222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_888222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888222 prefixEnd_888222 := by exact prefixLift 888222
  have htrace : WordTrace (prefixWord ++ tailWord_888222) baseStart_888222 baseEnd_888222 := by
    simpa [prefixWord, tailWord_888222, baseEnd_888222] using wordTrace_append hprefix tailTrace_888222
  have hstable : (prefixWord ++ tailWord_888222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888222).length < 2 ^ (prefixWord ++ tailWord_888222).sum := by decide
  have hdescent : baseEnd_888222 < baseStart_888222 := by decide
  rcases family_descends (prefixWord ++ tailWord_888222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888226 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_888226 : Nat := 118140960795 + 888226 * 2 ^ 59
def prefixEnd_888226 : Nat := 4983230072969 + 3 ^ 40 * 888226 * 2
def baseEnd_888226 : Nat := 405410549173819595902337

theorem tailTrace_888226 : CollatzResearch.WordTrace tailWord_888226 prefixEnd_888226 405410549173819595902337 := by
  unfold tailWord_888226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099065920029093442175133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21597509120077582512467021 8099065920029093442175133)
  ·
    refine ⟨3037149720010910040815675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8099065920029093442175133 3037149720010910040815675)
    ·
      refine ⟨4555724580016365061223513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037149720010910040815675 4555724580016365061223513)
      ·
        refine ⟨3416793435012273795917635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4555724580016365061223513 3416793435012273795917635)
        ·
          refine ⟨5125190152518410693876453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416793435012273795917635 5125190152518410693876453)
          ·
            refine ⟨960973153597202005101835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5125190152518410693876453 960973153597202005101835)
            ·
              refine ⟨1441459730395803007652753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960973153597202005101835 1441459730395803007652753)
              ·
                refine ⟨1081094797796852255739565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441459730395803007652753 1081094797796852255739565)
                ·
                  refine ⟨405410549173819595902337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081094797796852255739565 405410549173819595902337)
                  ·
                    rfl

theorem cell20_888226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_888226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888226 prefixEnd_888226 := by exact prefixLift 888226
  have htrace : WordTrace (prefixWord ++ tailWord_888226) baseStart_888226 baseEnd_888226 := by
    simpa [prefixWord, tailWord_888226, baseEnd_888226] using wordTrace_append hprefix tailTrace_888226
  have hstable : (prefixWord ++ tailWord_888226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888226).length < 2 ^ (prefixWord ++ tailWord_888226).sum := by decide
  have hdescent : baseEnd_888226 < baseStart_888226 := by decide
  rcases family_descends (prefixWord ++ tailWord_888226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888247 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 3]
def baseStart_888247 : Nat := 118140960795 + 888247 * 2 ^ 59
def prefixEnd_888247 : Nat := 4983230072969 + 3 ^ 40 * 888247 * 2
def baseEnd_888247 : Nat := 405420134146036856202251

theorem tailTrace_888247 : CollatzResearch.WordTrace tailWord_888247 prefixEnd_888247 405420134146036856202251 := by
  unfold tailWord_888247
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397029613040294355214995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21598019742026862903476663 32397029613040294355214995)
  ·
    refine ⟨48595544419560441532822493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397029613040294355214995 48595544419560441532822493)
    ·
      refine ⟨18223329157335165574808435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48595544419560441532822493 18223329157335165574808435)
      ·
        refine ⟨27334993736002748362212653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223329157335165574808435 27334993736002748362212653)
        ·
          refine ⟨10250622651001030635829745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27334993736002748362212653 10250622651001030635829745)
          ·
            refine ⟨7687966988250772976872309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10250622651001030635829745 7687966988250772976872309)
            ·
              refine ⟨720746905148509966581779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7687966988250772976872309 720746905148509966581779)
              ·
                refine ⟨1081120357722764949872669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720746905148509966581779 1081120357722764949872669)
                ·
                  refine ⟨405420134146036856202251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081120357722764949872669 405420134146036856202251)
                  ·
                    rfl

theorem cell20_888247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_888247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888247 prefixEnd_888247 := by exact prefixLift 888247
  have htrace : WordTrace (prefixWord ++ tailWord_888247) baseStart_888247 baseEnd_888247 := by
    simpa [prefixWord, tailWord_888247, baseEnd_888247] using wordTrace_append hprefix tailTrace_888247
  have hstable : (prefixWord ++ tailWord_888247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888247).length < 2 ^ (prefixWord ++ tailWord_888247).sum := by decide
  have hdescent : baseEnd_888247 < baseStart_888247 := by decide
  rcases family_descends (prefixWord ++ tailWord_888247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888268 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_888268 : Nat := 118140960795 + 888268 * 2 ^ 59
def prefixEnd_888268 : Nat := 4983230072969 + 3 ^ 40 * 888268 * 2
def baseEnd_888268 : Nat := 405429719118254116502165

theorem tailTrace_888268 : CollatzResearch.WordTrace tailWord_888268 prefixEnd_888268 405429719118254116502165 := by
  unfold tailWord_888268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198897772982107470864729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21598530363976143294486305 16198897772982107470864729)
  ·
    refine ⟨12149173329736580603148547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16198897772982107470864729 12149173329736580603148547)
    ·
      refine ⟨18223759994604870904722821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12149173329736580603148547 18223759994604870904722821)
      ·
        refine ⟨3416954998988413294635529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18223759994604870904722821 3416954998988413294635529)
        ·
          refine ⟨2562716249241309970976647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3416954998988413294635529 2562716249241309970976647)
          ·
            refine ⟨3844074373861964956464971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562716249241309970976647 3844074373861964956464971)
            ·
              refine ⟨5766111560792947434697457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844074373861964956464971 5766111560792947434697457)
              ·
                refine ⟨4324583670594710576023093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766111560792947434697457 4324583670594710576023093)
                ·
                  refine ⟨405429719118254116502165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4324583670594710576023093 405429719118254116502165)
                  ·
                    rfl

theorem cell20_888268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_888268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888268 prefixEnd_888268 := by exact prefixLift 888268
  have htrace : WordTrace (prefixWord ++ tailWord_888268) baseStart_888268 baseEnd_888268 := by
    simpa [prefixWord, tailWord_888268, baseEnd_888268] using wordTrace_append hprefix tailTrace_888268
  have hstable : (prefixWord ++ tailWord_888268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888268).length < 2 ^ (prefixWord ++ tailWord_888268).sum := by decide
  have hdescent : baseEnd_888268 < baseStart_888268 := by decide
  rcases family_descends (prefixWord ++ tailWord_888268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888278 : List Nat := [5, 2, 1, 1, 1, 4, 6]
def baseStart_888278 : Nat := 118140960795 + 888278 * 2 ^ 59
def prefixEnd_888278 : Nat := 4983230072969 + 3 ^ 40 * 888278 * 2
def baseEnd_888278 : Nat := 45048253710082058463199

theorem tailTrace_888278 : CollatzResearch.WordTrace tailWord_888278 prefixEnd_888278 45048253710082058463199 := by
  unfold tailWord_888278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024885017245499165599593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21598773517285324433062325 2024885017245499165599593)
  ·
    refine ⟨1518663762934124374199695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2024885017245499165599593 1518663762934124374199695)
    ·
      refine ⟨2277995644401186561299543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518663762934124374199695 2277995644401186561299543)
      ·
        refine ⟨3416993466601779841949315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277995644401186561299543 3416993466601779841949315)
        ·
          refine ⟨5125490199902669762923973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416993466601779841949315 5125490199902669762923973)
          ·
            refine ⟨961029412481750580548245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5125490199902669762923973 961029412481750580548245)
            ·
              refine ⟨45048253710082058463199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 961029412481750580548245 45048253710082058463199)
              ·
                rfl

theorem cell20_888278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_888278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888278 prefixEnd_888278 := by exact prefixLift 888278
  have htrace : WordTrace (prefixWord ++ tailWord_888278) baseStart_888278 baseEnd_888278 := by
    simpa [prefixWord, tailWord_888278, baseEnd_888278] using wordTrace_append hprefix tailTrace_888278
  have hstable : (prefixWord ++ tailWord_888278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888278).length < 2 ^ (prefixWord ++ tailWord_888278).sum := by decide
  have hdescent : baseEnd_888278 < baseStart_888278 := by decide
  rcases family_descends (prefixWord ++ tailWord_888278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888282 : List Nat := [3, 1, 1, 2, 3, 2, 8]
def baseStart_888282 : Nat := 118140960795 + 888282 * 2 ^ 59
def prefixEnd_888282 : Nat := 4983230072969 + 3 ^ 40 * 888282 * 2
def baseEnd_888282 : Nat := 45048456566636921115049

theorem tailTrace_888282 : CollatzResearch.WordTrace tailWord_888282 prefixEnd_888282 45048456566636921115049 := by
  unfold tailWord_888282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099576541978373833184775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21598870778608996888492733 8099576541978373833184775)
  ·
    refine ⟨12149364812967560749777163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8099576541978373833184775 12149364812967560749777163)
    ·
      refine ⟨18224047219451341124665745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12149364812967560749777163 18224047219451341124665745)
      ·
        refine ⟨13668035414588505843499309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18224047219451341124665745 13668035414588505843499309)
        ·
          refine ⟨5125513280470689691312241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13668035414588505843499309 5125513280470689691312241)
          ·
            refine ⟨3844134960353017268484181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5125513280470689691312241 3844134960353017268484181)
            ·
              refine ⟨45048456566636921115049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3844134960353017268484181 45048456566636921115049)
              ·
                rfl

theorem cell20_888282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_888282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888282 prefixEnd_888282 := by exact prefixLift 888282
  have htrace : WordTrace (prefixWord ++ tailWord_888282) baseStart_888282 baseEnd_888282 := by
    simpa [prefixWord, tailWord_888282, baseEnd_888282] using wordTrace_append hprefix tailTrace_888282
  have hstable : (prefixWord ++ tailWord_888282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888282).length < 2 ^ (prefixWord ++ tailWord_888282).sum := by decide
  have hdescent : baseEnd_888282 < baseStart_888282 := by decide
  rcases family_descends (prefixWord ++ tailWord_888282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888292 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_888292 : Nat := 118140960795 + 888292 * 2 ^ 59
def prefixEnd_888292 : Nat := 4983230072969 + 3 ^ 40 * 888292 * 2
def baseEnd_888292 : Nat := 405440673372216699702067

theorem tailTrace_888292 : CollatzResearch.WordTrace tailWord_888292 prefixEnd_888292 405440673372216699702067 := by
  unfold tailWord_888292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199335448938633520301565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21599113931918178027068753 16199335448938633520301565)
  ·
    refine ⟨6074750793351987570113087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16199335448938633520301565 6074750793351987570113087)
    ·
      refine ⟨9112126190027981355169631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6074750793351987570113087 9112126190027981355169631)
      ·
        refine ⟨13668189285041972032754447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9112126190027981355169631 13668189285041972032754447)
        ·
          refine ⟨20502283927562958049131671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13668189285041972032754447 20502283927562958049131671)
          ·
            refine ⟨30753425891344437073697507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20502283927562958049131671 30753425891344437073697507)
            ·
              refine ⟨46130138837016655610546261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30753425891344437073697507 46130138837016655610546261)
              ·
                refine ⟨540587564496288932936089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46130138837016655610546261 540587564496288932936089)
                ·
                  refine ⟨405440673372216699702067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540587564496288932936089 405440673372216699702067)
                  ·
                    rfl

theorem cell20_888292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_888292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888292 prefixEnd_888292 := by exact prefixLift 888292
  have htrace : WordTrace (prefixWord ++ tailWord_888292) baseStart_888292 baseEnd_888292 := by
    simpa [prefixWord, tailWord_888292, baseEnd_888292] using wordTrace_append hprefix tailTrace_888292
  have hstable : (prefixWord ++ tailWord_888292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888292).length < 2 ^ (prefixWord ++ tailWord_888292).sum := by decide
  have hdescent : baseEnd_888292 < baseStart_888292 := by decide
  rcases family_descends (prefixWord ++ tailWord_888292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888333 : List Nat := [1, 7, 1, 1, 3, 7]
def baseStart_888333 : Nat := 118140960795 + 888333 * 2 ^ 59
def prefixEnd_888333 : Nat := 4983230072969 + 3 ^ 40 * 888333 * 2
def baseEnd_888333 : Nat := 15017014329237139975379

theorem tailTrace_888333 : CollatzResearch.WordTrace tailWord_888333 prefixEnd_888333 15017014329237139975379 := by
  unfold tailWord_888333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32400166290728731042845653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21600110860485820695230435 32400166290728731042845653)
  ·
    refine ⟨759378897438954633816695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32400166290728731042845653 759378897438954633816695)
    ·
      refine ⟨1139068346158431950725043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759378897438954633816695 1139068346158431950725043)
      ·
        refine ⟨1708602519237647926087565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139068346158431950725043 1708602519237647926087565)
        ·
          refine ⟨640725944714117972282837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1708602519237647926087565 640725944714117972282837)
          ·
            refine ⟨15017014329237139975379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 640725944714117972282837 15017014329237139975379)
            ·
              rfl

theorem cell20_888333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 7].length) (baseStart_888333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888333 prefixEnd_888333 := by exact prefixLift 888333
  have htrace : WordTrace (prefixWord ++ tailWord_888333) baseStart_888333 baseEnd_888333 := by
    simpa [prefixWord, tailWord_888333, baseEnd_888333] using wordTrace_append hprefix tailTrace_888333
  have hstable : (prefixWord ++ tailWord_888333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888333).length < 2 ^ (prefixWord ++ tailWord_888333).sum := by decide
  have hdescent : baseEnd_888333 < baseStart_888333 := by decide
  rcases family_descends (prefixWord ++ tailWord_888333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888375 : List Nat := [1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_888375 : Nat := 118140960795 + 888375 * 2 ^ 59
def prefixEnd_888375 : Nat := 4983230072969 + 3 ^ 40 * 888375 * 2
def baseEnd_888375 : Nat := 135159518944612433311687

theorem tailTrace_888375 : CollatzResearch.WordTrace tailWord_888375 prefixEnd_888375 135159518944612433311687 := by
  unfold tailWord_888375
  simp only [CollatzResearch.WordTrace]
  refine ⟨32401698156576572215874579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21601132104384381477249719 32401698156576572215874579)
  ·
    refine ⟨48602547234864858323811869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32401698156576572215874579 48602547234864858323811869)
    ·
      refine ⟨18225955213074321871429451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48602547234864858323811869 18225955213074321871429451)
      ·
        refine ⟨27338932819611482807144177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18225955213074321871429451 27338932819611482807144177)
        ·
          refine ⟨20504199614708612105358133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27338932819611482807144177 20504199614708612105358133)
          ·
            refine ⟨1922268713878932384877325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20504199614708612105358133 1922268713878932384877325)
            ·
              refine ⟨720850767704599644328997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1922268713878932384877325 720850767704599644328997)
              ·
                refine ⟨135159518944612433311687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720850767704599644328997 135159518944612433311687)
                ·
                  rfl

theorem cell20_888375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_888375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888375 prefixEnd_888375 := by exact prefixLift 888375
  have htrace : WordTrace (prefixWord ++ tailWord_888375) baseStart_888375 baseEnd_888375 := by
    simpa [prefixWord, tailWord_888375, baseEnd_888375] using wordTrace_append hprefix tailTrace_888375
  have hstable : (prefixWord ++ tailWord_888375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888375).length < 2 ^ (prefixWord ++ tailWord_888375).sum := by decide
  have hdescent : baseEnd_888375 < baseStart_888375 := by decide
  rcases family_descends (prefixWord ++ tailWord_888375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888385 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 2]
def baseStart_888385 : Nat := 118140960795 + 888385 * 2 ^ 59
def prefixEnd_888385 : Nat := 4983230072969 + 3 ^ 40 * 888385 * 2
def baseEnd_888385 : Nat := 405483121106321709601687

theorem tailTrace_888385 : CollatzResearch.WordTrace tailWord_888385 prefixEnd_888385 405483121106321709601687 := by
  unfold tailWord_888385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32402062886540343923738609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21601375257693562615825739 32402062886540343923738609)
  ·
    refine ⟨24301547164905257942803957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32402062886540343923738609 24301547164905257942803957)
    ·
      refine ⟨2278270046709867932137871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24301547164905257942803957 2278270046709867932137871)
      ·
        refine ⟨3417405070064801898206807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278270046709867932137871 3417405070064801898206807)
        ·
          refine ⟨5126107605097202847310211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417405070064801898206807 5126107605097202847310211)
          ·
            refine ⟨7689161407645804270965317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126107605097202847310211 7689161407645804270965317)
            ·
              refine ⟨1441717763933588300805997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7689161407645804270965317 1441717763933588300805997)
              ·
                refine ⟨540644161475095612802249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441717763933588300805997 540644161475095612802249)
                ·
                  refine ⟨405483121106321709601687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540644161475095612802249 405483121106321709601687)
                  ·
                    rfl

theorem cell20_888385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_888385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888385 prefixEnd_888385 := by exact prefixLift 888385
  have htrace : WordTrace (prefixWord ++ tailWord_888385) baseStart_888385 baseEnd_888385 := by
    simpa [prefixWord, tailWord_888385, baseEnd_888385] using wordTrace_append hprefix tailTrace_888385
  have hstable : (prefixWord ++ tailWord_888385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888385).length < 2 ^ (prefixWord ++ tailWord_888385).sum := by decide
  have hdescent : baseEnd_888385 < baseStart_888385 := by decide
  rcases family_descends (prefixWord ++ tailWord_888385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888396 : List Nat := [2, 2, 1, 3, 1, 4, 7]
def baseStart_888396 : Nat := 118140960795 + 888396 * 2 ^ 59
def prefixEnd_888396 : Nat := 4983230072969 + 3 ^ 40 * 888396 * 2
def baseEnd_888396 : Nat := 45054237978450506692775

theorem tailTrace_888396 : CollatzResearch.WordTrace tailWord_888396 prefixEnd_888396 45054237978450506692775 := by
  unfold tailWord_888396
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201232044750246401194521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21601642726333661868259361 16201232044750246401194521)
  ·
    refine ⟨12150924033562684800895891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16201232044750246401194521 12150924033562684800895891)
    ·
      refine ⟨18226386050344027201343837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12150924033562684800895891 18226386050344027201343837)
      ·
        refine ⟨6834894768879010200503939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18226386050344027201343837 6834894768879010200503939)
        ·
          refine ⟨10252342153318515300755909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6834894768879010200503939 10252342153318515300755909)
          ·
            refine ⟨1922314153747221618891733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10252342153318515300755909 1922314153747221618891733)
            ·
              refine ⟨45054237978450506692775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1922314153747221618891733 45054237978450506692775)
              ·
                rfl

theorem cell20_888396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_888396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888396 prefixEnd_888396 := by exact prefixLift 888396
  have htrace : WordTrace (prefixWord ++ tailWord_888396) baseStart_888396 baseEnd_888396 := by
    simpa [prefixWord, tailWord_888396, baseEnd_888396] using wordTrace_append hprefix tailTrace_888396
  have hstable : (prefixWord ++ tailWord_888396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888396).length < 2 ^ (prefixWord ++ tailWord_888396).sum := by decide
  have hdescent : baseEnd_888396 < baseStart_888396 := by decide
  rcases family_descends (prefixWord ++ tailWord_888396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888441 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_888441 : Nat := 118140960795 + 888441 * 2 ^ 59
def prefixEnd_888441 : Nat := 4983230072969 + 3 ^ 40 * 888441 * 2
def baseEnd_888441 : Nat := 405508681032234403734791

theorem tailTrace_888441 : CollatzResearch.WordTrace tailWord_888441 prefixEnd_888441 405508681032234403734791 := by
  unfold tailWord_888441
  simp only [CollatzResearch.WordTrace]
  refine ⟨32404105374337465487777177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21602736916224976991851451 32404105374337465487777177)
  ·
    refine ⟨24303079030753099115832883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32404105374337465487777177 24303079030753099115832883)
    ·
      refine ⟨36454618546129648673749325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24303079030753099115832883 36454618546129648673749325)
      ·
        refine ⟨13670481954798618252655997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36454618546129648673749325 13670481954798618252655997)
        ·
          refine ⟨5126430733049481844745999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13670481954798618252655997 5126430733049481844745999)
          ·
            refine ⟨7689646099574222767118999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126430733049481844745999 7689646099574222767118999)
            ·
              refine ⟨11534469149361334150678499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7689646099574222767118999 11534469149361334150678499)
              ·
                refine ⟨17301703724042001226017749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11534469149361334150678499 17301703724042001226017749)
                ·
                  refine ⟨405508681032234403734791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17301703724042001226017749 405508681032234403734791)
                  ·
                    rfl

theorem cell20_888441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_888441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888441 prefixEnd_888441 := by exact prefixLift 888441
  have htrace : WordTrace (prefixWord ++ tailWord_888441) baseStart_888441 baseEnd_888441 := by
    simpa [prefixWord, tailWord_888441, baseEnd_888441] using wordTrace_append hprefix tailTrace_888441
  have hstable : (prefixWord ++ tailWord_888441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888441).length < 2 ^ (prefixWord ++ tailWord_888441).sum := by decide
  have hdescent : baseEnd_888441 < baseStart_888441 := by decide
  rcases family_descends (prefixWord ++ tailWord_888441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888458 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_888458 : Nat := 118140960795 + 888458 * 2 ^ 59
def prefixEnd_888458 : Nat := 4983230072969 + 3 ^ 40 * 888458 * 2
def baseEnd_888458 : Nat := 405516440295457900168055

theorem tailTrace_888458 : CollatzResearch.WordTrace tailWord_888458 prefixEnd_888458 405516440295457900168055 := by
  unfold tailWord_888458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101181353818969347786507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21603150276850584927430685 8101181353818969347786507)
  ·
    refine ⟨12151772030728454021679761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8101181353818969347786507 12151772030728454021679761)
    ·
      refine ⟨9113829023046340516259821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12151772030728454021679761 9113829023046340516259821)
      ·
        refine ⟨3417685883642377693597433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9113829023046340516259821 3417685883642377693597433)
        ·
          refine ⟨2563264412731783270198075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417685883642377693597433 2563264412731783270198075)
          ·
            refine ⟨3844896619097674905297113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563264412731783270198075 3844896619097674905297113)
            ·
              refine ⟨2883672464323256178972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844896619097674905297113 2883672464323256178972835)
              ·
                refine ⟨4325508696484884268459253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883672464323256178972835 4325508696484884268459253)
                ·
                  refine ⟨405516440295457900168055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4325508696484884268459253 405516440295457900168055)
                  ·
                    rfl

theorem cell20_888458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_888458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_888458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_888458 prefixEnd_888458 := by exact prefixLift 888458
  have htrace : WordTrace (prefixWord ++ tailWord_888458) baseStart_888458 baseEnd_888458 := by
    simpa [prefixWord, tailWord_888458, baseEnd_888458] using wordTrace_append hprefix tailTrace_888458
  have hstable : (prefixWord ++ tailWord_888458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888458).length < 2 ^ (prefixWord ++ tailWord_888458).sum := by decide
  have hdescent : baseEnd_888458 < baseStart_888458 := by decide
  rcases family_descends (prefixWord ++ tailWord_888458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
