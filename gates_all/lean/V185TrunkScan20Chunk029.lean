import V185TrunkScan20Chunk028

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_176318 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_176318 : Nat := 118140960795 + 176318 * 2 ^ 59
def prefixEnd_176318 : Nat := 4983230072969 + 3 ^ 40 * 176318 * 2
def baseEnd_176318 : Nat := 80476339590707901079231

theorem tailTrace_176318 : CollatzResearch.WordTrace tailWord_176318 prefixEnd_176318 80476339590707901079231 := by
  unfold tailWord_176318
  simp only [CollatzResearch.WordTrace]
  refine ⟨803855721904684195264201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4287230516824982374742405 803855721904684195264201)
  ·
    refine ⟨602891791428513146448151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 803855721904684195264201 602891791428513146448151)
    ·
      refine ⟨904337687142769719672227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602891791428513146448151 904337687142769719672227)
      ·
        refine ⟨1356506530714154579508341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904337687142769719672227 1356506530714154579508341)
        ·
          refine ⟨127172487254451991828907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1356506530714154579508341 127172487254451991828907)
          ·
            refine ⟨190758730881677987743361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127172487254451991828907 190758730881677987743361)
            ·
              refine ⟨143069048161258490807521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190758730881677987743361 143069048161258490807521)
              ·
                refine ⟨107301786120943868105641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143069048161258490807521 107301786120943868105641)
                ·
                  refine ⟨80476339590707901079231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107301786120943868105641 80476339590707901079231)
                  ·
                    rfl

theorem cell20_176318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_176318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176318 prefixEnd_176318 := by exact prefixLift 176318
  have htrace : WordTrace (prefixWord ++ tailWord_176318) baseStart_176318 baseEnd_176318 := by
    simpa [prefixWord, tailWord_176318, baseEnd_176318] using wordTrace_append hprefix tailTrace_176318
  have hstable : (prefixWord ++ tailWord_176318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176318).length < 2 ^ (prefixWord ++ tailWord_176318).sum := by decide
  have hdescent : baseEnd_176318 < baseStart_176318 := by decide
  rcases family_descends (prefixWord ++ tailWord_176318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176323 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_176323 : Nat := 118140960795 + 176323 * 2 ^ 59
def prefixEnd_176323 : Nat := 4983230072969 + 3 ^ 40 * 176323 * 2
def baseEnd_176323 : Nat := 80478621726950105912543

theorem tailTrace_176323 : CollatzResearch.WordTrace tailWord_176323 prefixEnd_176323 80478621726950105912543 := by
  unfold tailWord_176323
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431028140219359416045623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4287352093479572944030415 6431028140219359416045623)
  ·
    refine ⟨9646542210329039124068435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6431028140219359416045623 9646542210329039124068435)
    ·
      refine ⟨14469813315493558686102653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9646542210329039124068435 14469813315493558686102653)
      ·
        refine ⟨5426179993310084507288495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14469813315493558686102653 5426179993310084507288495)
        ·
          refine ⟨8139269989965126760932743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426179993310084507288495 8139269989965126760932743)
          ·
            refine ⟨12208904984947690141399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8139269989965126760932743 12208904984947690141399115)
            ·
              refine ⟨18313357477421535212098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12208904984947690141399115 18313357477421535212098673)
              ·
                refine ⟨13735018108066151409074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18313357477421535212098673 13735018108066151409074005)
                ·
                  refine ⟨80478621726950105912543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13735018108066151409074005 80478621726950105912543)
                  ·
                    rfl

theorem cell20_176323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_176323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176323 prefixEnd_176323 := by exact prefixLift 176323
  have htrace : WordTrace (prefixWord ++ tailWord_176323) baseStart_176323 baseEnd_176323 := by
    simpa [prefixWord, tailWord_176323, baseEnd_176323] using wordTrace_append hprefix tailTrace_176323
  have hstable : (prefixWord ++ tailWord_176323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176323).length < 2 ^ (prefixWord ++ tailWord_176323).sum := by decide
  have hdescent : baseEnd_176323 < baseStart_176323 := by decide
  rcases family_descends (prefixWord ++ tailWord_176323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176361 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_176361 : Nat := 118140960795 + 176361 * 2 ^ 59
def prefixEnd_176361 : Nat := 4983230072969 + 3 ^ 40 * 176361 * 2
def baseEnd_176361 : Nat := 80495965962390862645721

theorem tailTrace_176361 : CollatzResearch.WordTrace tailWord_176361 prefixEnd_176361 80495965962390862645721 := by
  unfold tailWord_176361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432414114081691905928937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4288276076054461270619291 6432414114081691905928937)
  ·
    refine ⟨4824310585561268929446703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6432414114081691905928937 4824310585561268929446703)
    ·
      refine ⟨7236465878341903394170055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824310585561268929446703 7236465878341903394170055)
      ·
        refine ⟨10854698817512855091255083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236465878341903394170055 10854698817512855091255083)
        ·
          refine ⟨16282048226269282636882625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10854698817512855091255083 16282048226269282636882625)
          ·
            refine ⟨12211536169701961977661969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16282048226269282636882625 12211536169701961977661969)
            ·
              refine ⟨9158652127276471483246477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12211536169701961977661969 9158652127276471483246477)
              ·
                refine ⟨3434494547728676806217429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9158652127276471483246477 3434494547728676806217429)
                ·
                  refine ⟨80495965962390862645721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3434494547728676806217429 80495965962390862645721)
                  ·
                    rfl

theorem cell20_176361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_176361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176361 prefixEnd_176361 := by exact prefixLift 176361
  have htrace : WordTrace (prefixWord ++ tailWord_176361) baseStart_176361 baseEnd_176361 := by
    simpa [prefixWord, tailWord_176361, baseEnd_176361] using wordTrace_append hprefix tailTrace_176361
  have hstable : (prefixWord ++ tailWord_176361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176361).length < 2 ^ (prefixWord ++ tailWord_176361).sum := by decide
  have hdescent : baseEnd_176361 < baseStart_176361 := by decide
  rcases family_descends (prefixWord ++ tailWord_176361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176378 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_176378 : Nat := 118140960795 + 176378 * 2 ^ 59
def prefixEnd_176378 : Nat := 4983230072969 + 3 ^ 40 * 176378 * 2
def baseEnd_176378 : Nat := 80503725225614359078985

theorem tailTrace_176378 : CollatzResearch.WordTrace tailWord_176378 prefixEnd_176378 80503725225614359078985 := by
  unfold tailWord_176378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608258538755025952324447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4288689436680069206198525 1608258538755025952324447)
  ·
    refine ⟨2412387808132538928486671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1608258538755025952324447 2412387808132538928486671)
    ·
      refine ⟨3618581712198808392730007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412387808132538928486671 3618581712198808392730007)
      ·
        refine ⟨5427872568298212589095011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618581712198808392730007 5427872568298212589095011)
        ·
          refine ⟨8141808852447318883642517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427872568298212589095011 8141808852447318883642517)
          ·
            refine ⟨381647289958468072670743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8141808852447318883642517 381647289958468072670743)
            ·
              refine ⟨572470934937702109006115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381647289958468072670743 572470934937702109006115)
              ·
                refine ⟨858706402406553163509173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572470934937702109006115 858706402406553163509173)
                ·
                  refine ⟨80503725225614359078985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 858706402406553163509173 80503725225614359078985)
                  ·
                    rfl

theorem cell20_176378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_176378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176378 prefixEnd_176378 := by exact prefixLift 176378
  have htrace : WordTrace (prefixWord ++ tailWord_176378) baseStart_176378 baseEnd_176378 := by
    simpa [prefixWord, tailWord_176378, baseEnd_176378] using wordTrace_append hprefix tailTrace_176378
  have hstable : (prefixWord ++ tailWord_176378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176378).length < 2 ^ (prefixWord ++ tailWord_176378).sum := by decide
  have hdescent : baseEnd_176378 < baseStart_176378 := by decide
  rcases family_descends (prefixWord ++ tailWord_176378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176391 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 3]
def baseStart_176391 : Nat := 118140960795 + 176391 * 2 ^ 59
def prefixEnd_176391 : Nat := 4983230072969 + 3 ^ 40 * 176391 * 2
def baseEnd_176391 : Nat := 80509658779844091645599

theorem tailTrace_176391 : CollatzResearch.WordTrace tailWord_176391 prefixEnd_176391 80509658779844091645599 := by
  unfold tailWord_176391
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433508303973007029521027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289005535982004686347351 6433508303973007029521027)
  ·
    refine ⟨9650262455959510544281541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433508303973007029521027 9650262455959510544281541)
    ·
      refine ⟨1809424210492408227052789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9650262455959510544281541 1809424210492408227052789)
      ·
        refine ⟨169633519733663271286199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1809424210492408227052789 169633519733663271286199)
        ·
          refine ⟨254450279600494906929299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169633519733663271286199 254450279600494906929299)
          ·
            refine ⟨381675419400742360393949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254450279600494906929299 381675419400742360393949)
            ·
              refine ⟨143128282275278385147731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381675419400742360393949 143128282275278385147731)
              ·
                refine ⟨214692423412917577721597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143128282275278385147731 214692423412917577721597)
                ·
                  refine ⟨80509658779844091645599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214692423412917577721597 80509658779844091645599)
                  ·
                    rfl

theorem cell20_176391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_176391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176391 prefixEnd_176391 := by exact prefixLift 176391
  have htrace : WordTrace (prefixWord ++ tailWord_176391) baseStart_176391 baseEnd_176391 := by
    simpa [prefixWord, tailWord_176391, baseEnd_176391] using wordTrace_append hprefix tailTrace_176391
  have hstable : (prefixWord ++ tailWord_176391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176391).length < 2 ^ (prefixWord ++ tailWord_176391).sum := by decide
  have hdescent : baseEnd_176391 < baseStart_176391 := by decide
  rcases family_descends (prefixWord ++ tailWord_176391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176395 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 3]
def baseStart_176395 : Nat := 118140960795 + 176395 * 2 ^ 59
def prefixEnd_176395 : Nat := 4983230072969 + 3 ^ 40 * 176395 * 2
def baseEnd_176395 : Nat := 80511484488837855512249

theorem tailTrace_176395 : CollatzResearch.WordTrace tailWord_176395 prefixEnd_176395 80511484488837855512249 := by
  unfold tailWord_176395
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433654195958515712666639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289102797305677141777759 6433654195958515712666639)
  ·
    refine ⟨9650481293937773568999959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433654195958515712666639 9650481293937773568999959)
    ·
      refine ⟨14475721940906660353499939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9650481293937773568999959 14475721940906660353499939)
      ·
        refine ⟨21713582911359990530249909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14475721940906660353499939 21713582911359990530249909)
        ·
          refine ⟨2035648397939999112210929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21713582911359990530249909 2035648397939999112210929)
          ·
            refine ⟨1526736298454999334158197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035648397939999112210929 1526736298454999334158197)
            ·
              refine ⟨143131527980156187577331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1526736298454999334158197 143131527980156187577331)
              ·
                refine ⟨214697291970234281365997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143131527980156187577331 214697291970234281365997)
                ·
                  refine ⟨80511484488837855512249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214697291970234281365997 80511484488837855512249)
                  ·
                    rfl

theorem cell20_176395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_176395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176395 prefixEnd_176395 := by exact prefixLift 176395
  have htrace : WordTrace (prefixWord ++ tailWord_176395) baseStart_176395 baseEnd_176395 := by
    simpa [prefixWord, tailWord_176395, baseEnd_176395] using wordTrace_append hprefix tailTrace_176395
  have hstable : (prefixWord ++ tailWord_176395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176395).length < 2 ^ (prefixWord ++ tailWord_176395).sum := by decide
  have hdescent : baseEnd_176395 < baseStart_176395 := by decide
  rcases family_descends (prefixWord ++ tailWord_176395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176416 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_176416 : Nat := 118140960795 + 176416 * 2 ^ 59
def prefixEnd_176416 : Nat := 4983230072969 + 3 ^ 40 * 176416 * 2
def baseEnd_176416 : Nat := 80521069461055115812163

theorem tailTrace_176416 : CollatzResearch.WordTrace tailWord_176416 prefixEnd_176416 80521069461055115812163 := by
  unfold tailWord_176416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217210064441218149590551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4289613419254957532787401 3217210064441218149590551)
  ·
    refine ⟨4825815096661827224385827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3217210064441218149590551 4825815096661827224385827)
    ·
      refine ⟨7238722644992740836578741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825815096661827224385827 7238722644992740836578741)
      ·
        refine ⟨678630247968069453429257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7238722644992740836578741 678630247968069453429257)
        ·
          refine ⟨508972685976052090071943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678630247968069453429257 508972685976052090071943)
          ·
            refine ⟨763459028964078135107915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508972685976052090071943 763459028964078135107915)
            ·
              refine ⟨1145188543446117202661873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763459028964078135107915 1145188543446117202661873)
              ·
                refine ⟨858891407584587901996405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145188543446117202661873 858891407584587901996405)
                ·
                  refine ⟨80521069461055115812163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 858891407584587901996405 80521069461055115812163)
                  ·
                    rfl

theorem cell20_176416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_176416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176416 prefixEnd_176416 := by exact prefixLift 176416
  have htrace : WordTrace (prefixWord ++ tailWord_176416) baseStart_176416 baseEnd_176416 := by
    simpa [prefixWord, tailWord_176416, baseEnd_176416] using wordTrace_append hprefix tailTrace_176416
  have hstable : (prefixWord ++ tailWord_176416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176416).length < 2 ^ (prefixWord ++ tailWord_176416).sum := by decide
  have hdescent : baseEnd_176416 < baseStart_176416 := by decide
  rcases family_descends (prefixWord ++ tailWord_176416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176426 : List Nat := [3, 1, 4, 2, 2, 2, 6]
def baseStart_176426 : Nat := 118140960795 + 176426 * 2 ^ 59
def prefixEnd_176426 : Nat := 4983230072969 + 3 ^ 40 * 176426 * 2
def baseEnd_176426 : Nat := 8947292637059947275421

theorem tailTrace_176426 : CollatzResearch.WordTrace tailWord_176426 prefixEnd_176426 8947292637059947275421 := by
  unfold tailWord_176426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608696214711552001761283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4289856572564138671363421 1608696214711552001761283)
  ·
    refine ⟨2413044322067328002641925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1608696214711552001761283 2413044322067328002641925)
    ·
      refine ⟨452445810387624000495361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2413044322067328002641925 452445810387624000495361)
      ·
        refine ⟨339334357790718000371521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452445810387624000495361 339334357790718000371521)
        ·
          refine ⟨254500768343038500278641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339334357790718000371521 254500768343038500278641)
          ·
            refine ⟨190875576257278875208981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254500768343038500278641 190875576257278875208981)
            ·
              refine ⟨8947292637059947275421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190875576257278875208981 8947292637059947275421)
              ·
                rfl

theorem cell20_176426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_176426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176426 prefixEnd_176426 := by exact prefixLift 176426
  have htrace : WordTrace (prefixWord ++ tailWord_176426) baseStart_176426 baseEnd_176426 := by
    simpa [prefixWord, tailWord_176426, baseEnd_176426] using wordTrace_append hprefix tailTrace_176426
  have hstable : (prefixWord ++ tailWord_176426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176426).length < 2 ^ (prefixWord ++ tailWord_176426).sum := by decide
  have hdescent : baseEnd_176426 < baseStart_176426 := by decide
  rcases family_descends (prefixWord ++ tailWord_176426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176440 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_176440 : Nat := 118140960795 + 176440 * 2 ^ 59
def prefixEnd_176440 : Nat := 4983230072969 + 3 ^ 40 * 176440 * 2
def baseEnd_176440 : Nat := 80532023715017699012065

theorem tailTrace_176440 : CollatzResearch.WordTrace tailWord_176440 prefixEnd_176440 80532023715017699012065 := by
  unfold tailWord_176440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217647740397744199027387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4290196987196992265369849 3217647740397744199027387)
  ·
    refine ⟨4826471610596616298541081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3217647740397744199027387 4826471610596616298541081)
    ·
      refine ⟨3619853707947462223905811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4826471610596616298541081 3619853707947462223905811)
      ·
        refine ⟨5429780561921193335858717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619853707947462223905811 5429780561921193335858717)
        ·
          refine ⟨2036167710720447500947019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5429780561921193335858717 2036167710720447500947019)
          ·
            refine ⟨3054251566080671251420529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036167710720447500947019 3054251566080671251420529)
            ·
              refine ⟨2290688674560503438565397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054251566080671251420529 2290688674560503438565397)
              ·
                refine ⟨107376031620023598682753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2290688674560503438565397 107376031620023598682753)
                ·
                  refine ⟨80532023715017699012065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107376031620023598682753 80532023715017699012065)
                  ·
                    rfl

theorem cell20_176440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_176440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176440 prefixEnd_176440 := by exact prefixLift 176440
  have htrace : WordTrace (prefixWord ++ tailWord_176440) baseStart_176440 baseEnd_176440 := by
    simpa [prefixWord, tailWord_176440, baseEnd_176440] using wordTrace_append hprefix tailTrace_176440
  have hstable : (prefixWord ++ tailWord_176440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176440).length < 2 ^ (prefixWord ++ tailWord_176440).sum := by decide
  have hdescent : baseEnd_176440 < baseStart_176440 := by decide
  rcases family_descends (prefixWord ++ tailWord_176440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176523 : List Nat := [1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_176523 : Nat := 118140960795 + 176523 * 2 ^ 59
def prefixEnd_176523 : Nat := 4983230072969 + 3 ^ 40 * 176523 * 2
def baseEnd_176523 : Nat := 26856635725546099748353

theorem tailTrace_176523 : CollatzResearch.WordTrace tailWord_176523 prefixEnd_176523 26856635725546099748353 := by
  unfold tailWord_176523
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438322739494793573326223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4292215159663195715550815 6438322739494793573326223)
  ·
    refine ⟨9657484109242190359989335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6438322739494793573326223 9657484109242190359989335)
    ·
      refine ⟨14486226163863285539984003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9657484109242190359989335 14486226163863285539984003)
      ·
        refine ⟨21729339245794928309976005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14486226163863285539984003 21729339245794928309976005)
        ·
          refine ⟨4074251108586549058120501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21729339245794928309976005 4074251108586549058120501)
          ·
            refine ⟨381961041429988974198797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4074251108586549058120501 381961041429988974198797)
            ·
              refine ⟨143235390536245865324549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 381961041429988974198797 143235390536245865324549)
              ·
                refine ⟨26856635725546099748353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143235390536245865324549 26856635725546099748353)
                ·
                  rfl

theorem cell20_176523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_176523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176523 prefixEnd_176523 := by exact prefixLift 176523
  have htrace : WordTrace (prefixWord ++ tailWord_176523) baseStart_176523 baseEnd_176523 := by
    simpa [prefixWord, tailWord_176523, baseEnd_176523] using wordTrace_append hprefix tailTrace_176523
  have hstable : (prefixWord ++ tailWord_176523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176523).length < 2 ^ (prefixWord ++ tailWord_176523).sum := by decide
  have hdescent : baseEnd_176523 < baseStart_176523 := by decide
  rcases family_descends (prefixWord ++ tailWord_176523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176544 : List Nat := [2, 1, 1, 4, 1, 4, 7]
def baseStart_176544 : Nat := 118140960795 + 176544 * 2 ^ 59
def prefixEnd_176544 : Nat := 4983230072969 + 3 ^ 40 * 176544 * 2
def baseEnd_176544 : Nat := 8953276905428395504997

theorem tailTrace_176544 : CollatzResearch.WordTrace tailWord_176544 prefixEnd_176544 8953276905428395504997 := by
  unfold tailWord_176544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219544336209357079920343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4292725781612476106560457 3219544336209357079920343)
  ·
    refine ⟨4829316504314035619880515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219544336209357079920343 4829316504314035619880515)
    ·
      refine ⟨7243974756471053429820773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829316504314035619880515 7243974756471053429820773)
      ·
        refine ⟨1358245266838322518091395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7243974756471053429820773 1358245266838322518091395)
        ·
          refine ⟨2037367900257483777137093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358245266838322518091395 2037367900257483777137093)
          ·
            refine ⟨382006481298278208213205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2037367900257483777137093 382006481298278208213205)
            ·
              refine ⟨8953276905428395504997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 382006481298278208213205 8953276905428395504997)
              ·
                rfl

theorem cell20_176544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_176544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176544 prefixEnd_176544 := by exact prefixLift 176544
  have htrace : WordTrace (prefixWord ++ tailWord_176544) baseStart_176544 baseEnd_176544 := by
    simpa [prefixWord, tailWord_176544, baseEnd_176544] using wordTrace_append hprefix tailTrace_176544
  have hstable : (prefixWord ++ tailWord_176544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176544).length < 2 ^ (prefixWord ++ tailWord_176544).sum := by decide
  have hdescent : baseEnd_176544 < baseStart_176544 := by decide
  rcases family_descends (prefixWord ++ tailWord_176544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176547 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_176547 : Nat := 118140960795 + 176547 * 2 ^ 59
def prefixEnd_176547 : Nat := 4983230072969 + 3 ^ 40 * 176547 * 2
def baseEnd_176547 : Nat := 80580861430600882444961

theorem tailTrace_176547 : CollatzResearch.WordTrace tailWord_176547 prefixEnd_176547 80580861430600882444961 := by
  unfold tailWord_176547
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439198091407845672199895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4292798727605230448133263 6439198091407845672199895)
  ·
    refine ⟨9658797137111768508299843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6439198091407845672199895 9658797137111768508299843)
    ·
      refine ⟨14488195705667652762449765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9658797137111768508299843 14488195705667652762449765)
      ·
        refine ⟨2716536694812684892959331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14488195705667652762449765 2716536694812684892959331)
        ·
          refine ⟨4074805042219027339438997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716536694812684892959331 4074805042219027339438997)
          ·
            refine ⟨191006486354016906536203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4074805042219027339438997 191006486354016906536203)
            ·
              refine ⟨286509729531025359804305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191006486354016906536203 286509729531025359804305)
              ·
                refine ⟨214882297148269019853229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286509729531025359804305 214882297148269019853229)
                ·
                  refine ⟨80580861430600882444961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214882297148269019853229 80580861430600882444961)
                  ·
                    rfl

theorem cell20_176547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_176547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176547 prefixEnd_176547 := by exact prefixLift 176547
  have htrace : WordTrace (prefixWord ++ tailWord_176547) baseStart_176547 baseEnd_176547 := by
    simpa [prefixWord, tailWord_176547, baseEnd_176547] using wordTrace_append hprefix tailTrace_176547
  have hstable : (prefixWord ++ tailWord_176547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176547).length < 2 ^ (prefixWord ++ tailWord_176547).sum := by decide
  have hdescent : baseEnd_176547 < baseStart_176547 := by decide
  rcases family_descends (prefixWord ++ tailWord_176547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176588 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_176588 : Nat := 118140960795 + 176588 * 2 ^ 59
def prefixEnd_176588 : Nat := 4983230072969 + 3 ^ 40 * 176588 * 2
def baseEnd_176588 : Nat := 80599574947786962078127

theorem tailTrace_176588 : CollatzResearch.WordTrace tailWord_176588 prefixEnd_176588 80599574947786962078127 := by
  unfold tailWord_176588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220346742129654837221209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4293795656172873116294945 3220346742129654837221209)
  ·
    refine ⟨2415260056597241127915907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220346742129654837221209 2415260056597241127915907)
    ·
      refine ⟨3622890084895861691873861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415260056597241127915907 3622890084895861691873861)
      ·
        refine ⟨679291890917974067226349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3622890084895861691873861 679291890917974067226349)
        ·
          refine ⟨254734459094240275209881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679291890917974067226349 254734459094240275209881)
          ·
            refine ⟨191050844320680206407411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254734459094240275209881 191050844320680206407411)
            ·
              refine ⟨286576266481020309611117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191050844320680206407411 286576266481020309611117)
              ·
                refine ⟨107466099930382616104169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286576266481020309611117 107466099930382616104169)
                ·
                  refine ⟨80599574947786962078127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107466099930382616104169 80599574947786962078127)
                  ·
                    rfl

theorem cell20_176588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_176588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176588 prefixEnd_176588 := by exact prefixLift 176588
  have htrace : WordTrace (prefixWord ++ tailWord_176588) baseStart_176588 baseEnd_176588 := by
    simpa [prefixWord, tailWord_176588, baseEnd_176588] using wordTrace_append hprefix tailTrace_176588
  have hstable : (prefixWord ++ tailWord_176588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176588).length < 2 ^ (prefixWord ++ tailWord_176588).sum := by decide
  have hdescent : baseEnd_176588 < baseStart_176588 := by decide
  rcases family_descends (prefixWord ++ tailWord_176588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176609 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 2]
def baseStart_176609 : Nat := 118140960795 + 176609 * 2 ^ 59
def prefixEnd_176609 : Nat := 4983230072969 + 3 ^ 40 * 176609 * 2
def baseEnd_176609 : Nat := 80609159920004222378041

theorem tailTrace_176609 : CollatzResearch.WordTrace tailWord_176609 prefixEnd_176609 80609159920004222378041 := by
  unfold tailWord_176609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441459417183230260956881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4294306278122153507304587 6441459417183230260956881)
  ·
    refine ⟨4831094562887422695717661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6441459417183230260956881 4831094562887422695717661)
    ·
      refine ⟨1811660461082783510894123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4831094562887422695717661 1811660461082783510894123)
      ·
        refine ⟨2717490691624175266341185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811660461082783510894123 2717490691624175266341185)
        ·
          refine ⟨2038118018718131449755889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2717490691624175266341185 2038118018718131449755889)
          ·
            refine ⟨1528588514038598587316917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038118018718131449755889 1528588514038598587316917)
            ·
              refine ⟨143305173191118617560961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1528588514038598587316917 143305173191118617560961)
              ·
                refine ⟨107478879893338963170721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143305173191118617560961 107478879893338963170721)
                ·
                  refine ⟨80609159920004222378041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107478879893338963170721 80609159920004222378041)
                  ·
                    rfl

theorem cell20_176609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_176609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176609 prefixEnd_176609 := by exact prefixLift 176609
  have htrace : WordTrace (prefixWord ++ tailWord_176609) baseStart_176609 baseEnd_176609 := by
    simpa [prefixWord, tailWord_176609, baseEnd_176609] using wordTrace_append hprefix tailTrace_176609
  have hstable : (prefixWord ++ tailWord_176609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176609).length < 2 ^ (prefixWord ++ tailWord_176609).sum := by decide
  have hdescent : baseEnd_176609 < baseStart_176609 := by decide
  rcases family_descends (prefixWord ++ tailWord_176609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176620 : List Nat := [2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_176620 : Nat := 118140960795 + 176620 * 2 ^ 59
def prefixEnd_176620 : Nat := 4983230072969 + 3 ^ 40 * 176620 * 2
def baseEnd_176620 : Nat := 26871393539912357670443

theorem tailTrace_176620 : CollatzResearch.WordTrace tailWord_176620 prefixEnd_176620 26871393539912357670443 := by
  unfold tailWord_176620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220930310071689569803657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4294573746762252759738209 3220930310071689569803657)
  ·
    refine ⟨2415697732553767177352743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220930310071689569803657 2415697732553767177352743)
    ·
      refine ⟨3623546598830650766029115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415697732553767177352743 3623546598830650766029115)
      ·
        refine ⟨5435319898245976149043673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623546598830650766029115 5435319898245976149043673)
        ·
          refine ⟨4076489923684482111782755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5435319898245976149043673 4076489923684482111782755)
          ·
            refine ⟨6114734885526723167674133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4076489923684482111782755 6114734885526723167674133)
            ·
              refine ⟨286628197759065148484725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6114734885526723167674133 286628197759065148484725)
              ·
                refine ⟨26871393539912357670443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286628197759065148484725 26871393539912357670443)
                ·
                  rfl

theorem cell20_176620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_176620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176620 prefixEnd_176620 := by exact prefixLift 176620
  have htrace : WordTrace (prefixWord ++ tailWord_176620) baseStart_176620 baseEnd_176620 := by
    simpa [prefixWord, tailWord_176620, baseEnd_176620] using wordTrace_append hprefix tailTrace_176620
  have hstable : (prefixWord ++ tailWord_176620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176620).length < 2 ^ (prefixWord ++ tailWord_176620).sum := by decide
  have hdescent : baseEnd_176620 < baseStart_176620 := by decide
  rcases family_descends (prefixWord ++ tailWord_176620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176664 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_176664 : Nat := 118140960795 + 176664 * 2 ^ 59
def prefixEnd_176664 : Nat := 4983230072969 + 3 ^ 40 * 176664 * 2
def baseEnd_176664 : Nat := 80634263418668475544483

theorem tailTrace_176664 : CollatzResearch.WordTrace tailWord_176664 prefixEnd_176664 80634263418668475544483 := by
  unfold tailWord_176664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221732715991987327104523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4295643621322649769472697 3221732715991987327104523)
  ·
    refine ⟨4832599073987980990656785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221732715991987327104523 4832599073987980990656785)
    ·
      refine ⟨3624449305490985742992589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4832599073987980990656785 3624449305490985742992589)
      ·
        refine ⟨1359168489559119653622221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3624449305490985742992589 1359168489559119653622221)
        ·
          refine ⟨509688183584669870108333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1359168489559119653622221 509688183584669870108333)
          ·
            refine ⟨191133068844251201290625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509688183584669870108333 191133068844251201290625)
            ·
              refine ⟨143349801633188400967969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191133068844251201290625 143349801633188400967969)
              ·
                refine ⟨107512351224891300725977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143349801633188400967969 107512351224891300725977)
                ·
                  refine ⟨80634263418668475544483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107512351224891300725977 80634263418668475544483)
                  ·
                    rfl

theorem cell20_176664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_176664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176664 prefixEnd_176664 := by exact prefixLift 176664
  have htrace : WordTrace (prefixWord ++ tailWord_176664) baseStart_176664 baseEnd_176664 := by
    simpa [prefixWord, tailWord_176664, baseEnd_176664] using wordTrace_append hprefix tailTrace_176664
  have hstable : (prefixWord ++ tailWord_176664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176664).length < 2 ^ (prefixWord ++ tailWord_176664).sum := by decide
  have hdescent : baseEnd_176664 < baseStart_176664 := by decide
  rcases family_descends (prefixWord ++ tailWord_176664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176675 : List Nat := [1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_176675 : Nat := 118140960795 + 176675 * 2 ^ 59
def prefixEnd_176675 : Nat := 4983230072969 + 3 ^ 40 * 176675 * 2
def baseEnd_176675 : Nat := 26879761372800442059257

theorem tailTrace_176675 : CollatzResearch.WordTrace tailWord_176675 prefixEnd_176675 26879761372800442059257 := by
  unfold tailWord_176675
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443866634944123532859479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4295911089962749021906319 6443866634944123532859479)
  ·
    refine ⟨9665799952416185299289219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6443866634944123532859479 9665799952416185299289219)
    ·
      refine ⟨14498699928624277948933829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9665799952416185299289219 14498699928624277948933829)
      ·
        refine ⟨2718506236617052115425093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14498699928624277948933829 2718506236617052115425093)
        ·
          refine ⟨509719919365697271642205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2718506236617052115425093 509719919365697271642205)
          ·
            refine ⟨191144969762136476865827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509719919365697271642205 191144969762136476865827)
            ·
              refine ⟨286717454643204715298741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191144969762136476865827 286717454643204715298741)
              ·
                refine ⟨26879761372800442059257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286717454643204715298741 26879761372800442059257)
                ·
                  rfl

theorem cell20_176675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_176675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176675 prefixEnd_176675 := by exact prefixLift 176675
  have htrace : WordTrace (prefixWord ++ tailWord_176675) baseStart_176675 baseEnd_176675 := by
    simpa [prefixWord, tailWord_176675, baseEnd_176675] using wordTrace_append hprefix tailTrace_176675
  have hstable : (prefixWord ++ tailWord_176675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176675).length < 2 ^ (prefixWord ++ tailWord_176675).sum := by decide
  have hdescent : baseEnd_176675 < baseStart_176675 := by decide
  rcases family_descends (prefixWord ++ tailWord_176675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176703 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_176703 : Nat := 118140960795 + 176703 * 2 ^ 59
def prefixEnd_176703 : Nat := 4983230072969 + 3 ^ 40 * 176703 * 2
def baseEnd_176703 : Nat := 80652064081357673244323

theorem tailTrace_176703 : CollatzResearch.WordTrace tailWord_176703 prefixEnd_176703 80652064081357673244323 := by
  unfold tailWord_176703
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444887878842684314878763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4296591919228456209919175 6444887878842684314878763)
  ·
    refine ⟨9667331818264026472318145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6444887878842684314878763 9667331818264026472318145)
    ·
      refine ⟨7250498863698019854238609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9667331818264026472318145 7250498863698019854238609)
      ·
        refine ⟨5437874147773514890678957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250498863698019854238609 5437874147773514890678957)
        ·
          refine ⟨2039202805415068084004609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5437874147773514890678957 2039202805415068084004609)
          ·
            refine ⟨1529402104061301063003457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039202805415068084004609 1529402104061301063003457)
            ·
              refine ⟨1147051578045975797252593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529402104061301063003457 1147051578045975797252593)
              ·
                refine ⟨860288683534481847939445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147051578045975797252593 860288683534481847939445)
                ·
                  refine ⟨80652064081357673244323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860288683534481847939445 80652064081357673244323)
                  ·
                    rfl

theorem cell20_176703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_176703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176703 prefixEnd_176703 := by exact prefixLift 176703
  have htrace : WordTrace (prefixWord ++ tailWord_176703) baseStart_176703 baseEnd_176703 := by
    simpa [prefixWord, tailWord_176703, baseEnd_176703] using wordTrace_append hprefix tailTrace_176703
  have hstable : (prefixWord ++ tailWord_176703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176703).length < 2 ^ (prefixWord ++ tailWord_176703).sum := by decide
  have hdescent : baseEnd_176703 < baseStart_176703 := by decide
  rcases family_descends (prefixWord ++ tailWord_176703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176727 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_176727 : Nat := 118140960795 + 176727 * 2 ^ 59
def prefixEnd_176727 : Nat := 4983230072969 + 3 ^ 40 * 176727 * 2
def baseEnd_176727 : Nat := 80663018335320256444225

theorem tailTrace_176727 : CollatzResearch.WordTrace tailWord_176727 prefixEnd_176727 80663018335320256444225 := by
  unfold tailWord_176727
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445763230755736413752435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4297175487170490942501623 6445763230755736413752435)
  ·
    refine ⟨9668644846133604620628653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6445763230755736413752435 9668644846133604620628653)
    ·
      refine ⟨3625741817300101732735745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9668644846133604620628653 3625741817300101732735745)
      ·
        refine ⟨2719306362975076299551809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3625741817300101732735745 2719306362975076299551809)
        ·
          refine ⟨2039479772231307224663857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2719306362975076299551809 2039479772231307224663857)
          ·
            refine ⟨1529609829173480418497893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039479772231307224663857 1529609829173480418497893)
            ·
              refine ⟨286801842970027578468355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1529609829173480418497893 286801842970027578468355)
              ·
                refine ⟨430202764455041367702533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286801842970027578468355 430202764455041367702533)
                ·
                  refine ⟨80663018335320256444225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430202764455041367702533 80663018335320256444225)
                  ·
                    rfl

theorem cell20_176727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_176727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176727 prefixEnd_176727 := by exact prefixLift 176727
  have htrace : WordTrace (prefixWord ++ tailWord_176727) baseStart_176727 baseEnd_176727 := by
    simpa [prefixWord, tailWord_176727, baseEnd_176727] using wordTrace_append hprefix tailTrace_176727
  have hstable : (prefixWord ++ tailWord_176727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176727).length < 2 ^ (prefixWord ++ tailWord_176727).sum := by decide
  have hdescent : baseEnd_176727 < baseStart_176727 := by decide
  rcases family_descends (prefixWord ++ tailWord_176727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176737 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 3]
def baseStart_176737 : Nat := 118140960795 + 176737 * 2 ^ 59
def prefixEnd_176737 : Nat := 4983230072969 + 3 ^ 40 * 176737 * 2
def baseEnd_176737 : Nat := 80667582607804666110851

theorem tailTrace_176737 : CollatzResearch.WordTrace tailWord_176737 prefixEnd_176737 80667582607804666110851 := by
  unfold tailWord_176737
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446127960719508121616465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4297418640479672081077643 6446127960719508121616465)
  ·
    refine ⟨4834595970539631091212349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6446127960719508121616465 4834595970539631091212349)
    ·
      refine ⟨1812973488952361659204631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4834595970539631091212349 1812973488952361659204631)
      ·
        refine ⟨2719460233428542488806947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812973488952361659204631 2719460233428542488806947)
        ·
          refine ⟨4079190350142813733210421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719460233428542488806947 4079190350142813733210421)
          ·
            refine ⟨382424095325888787488477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4079190350142813733210421 382424095325888787488477)
            ·
              refine ⟨143409035747208295308179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382424095325888787488477 143409035747208295308179)
              ·
                refine ⟨215113553620812442962269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143409035747208295308179 215113553620812442962269)
                ·
                  refine ⟨80667582607804666110851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215113553620812442962269 80667582607804666110851)
                  ·
                    rfl

theorem cell20_176737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_176737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176737 prefixEnd_176737 := by exact prefixLift 176737
  have htrace : WordTrace (prefixWord ++ tailWord_176737) baseStart_176737 baseEnd_176737 := by
    simpa [prefixWord, tailWord_176737, baseEnd_176737] using wordTrace_append hprefix tailTrace_176737
  have hstable : (prefixWord ++ tailWord_176737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176737).length < 2 ^ (prefixWord ++ tailWord_176737).sum := by decide
  have hdescent : baseEnd_176737 < baseStart_176737 := by decide
  rcases family_descends (prefixWord ++ tailWord_176737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176757 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 2]
def baseStart_176757 : Nat := 118140960795 + 176757 * 2 ^ 59
def prefixEnd_176757 : Nat := 4983230072969 + 3 ^ 40 * 176757 * 2
def baseEnd_176757 : Nat := 80676711152773485444103

theorem tailTrace_176757 : CollatzResearch.WordTrace tailWord_176757 prefixEnd_176757 80676711152773485444103 := by
  unfold tailWord_176757
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446857420647051537344525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4297904947098034358229683 6446857420647051537344525)
  ·
    refine ⟨2417571532742644326504197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6446857420647051537344525 2417571532742644326504197)
    ·
      refine ⟨453294662389245811219537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2417571532742644326504197 453294662389245811219537)
      ·
        refine ⟨339970996791934358414653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453294662389245811219537 339970996791934358414653)
        ·
          refine ⟨127489123796975384405495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339970996791934358414653 127489123796975384405495)
          ·
            refine ⟨191233685695463076608243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127489123796975384405495 191233685695463076608243)
            ·
              refine ⟨286850528543194614912365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191233685695463076608243 286850528543194614912365)
              ·
                refine ⟨107568948203697980592137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286850528543194614912365 107568948203697980592137)
                ·
                  refine ⟨80676711152773485444103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107568948203697980592137 80676711152773485444103)
                  ·
                    rfl

theorem cell20_176757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_176757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176757 prefixEnd_176757 := by exact prefixLift 176757
  have htrace : WordTrace (prefixWord ++ tailWord_176757) baseStart_176757 baseEnd_176757 := by
    simpa [prefixWord, tailWord_176757, baseEnd_176757] using wordTrace_append hprefix tailTrace_176757
  have hstable : (prefixWord ++ tailWord_176757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176757).length < 2 ^ (prefixWord ++ tailWord_176757).sum := by decide
  have hdescent : baseEnd_176757 < baseStart_176757 := by decide
  rcases family_descends (prefixWord ++ tailWord_176757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176761 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 2]
def baseStart_176761 : Nat := 118140960795 + 176761 * 2 ^ 59
def prefixEnd_176761 : Nat := 4983230072969 + 3 ^ 40 * 176761 * 2
def baseEnd_176761 : Nat := 80678536861767249310753

theorem tailTrace_176761 : CollatzResearch.WordTrace tailWord_176761 prefixEnd_176761 80678536861767249310753 := by
  unfold tailWord_176761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447003312632560220490137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4298002208421706813660091 6447003312632560220490137)
  ·
    refine ⟨4835252484474420165367603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6447003312632560220490137 4835252484474420165367603)
    ·
      refine ⟨7252878726711630248051405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835252484474420165367603 7252878726711630248051405)
      ·
        refine ⟨2719829522516861343019277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7252878726711630248051405 2719829522516861343019277)
        ·
          refine ⟨1019936070943823003632229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2719829522516861343019277 1019936070943823003632229)
          ·
            refine ⟨191238013301966813181043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1019936070943823003632229 191238013301966813181043)
            ·
              refine ⟨286857019952950219771565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191238013301966813181043 286857019952950219771565)
              ·
                refine ⟨107571382482356332414337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286857019952950219771565 107571382482356332414337)
                ·
                  refine ⟨80678536861767249310753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107571382482356332414337 80678536861767249310753)
                  ·
                    rfl

theorem cell20_176761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_176761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176761 prefixEnd_176761 := by exact prefixLift 176761
  have htrace : WordTrace (prefixWord ++ tailWord_176761) baseStart_176761 baseEnd_176761 := by
    simpa [prefixWord, tailWord_176761, baseEnd_176761] using wordTrace_append hprefix tailTrace_176761
  have hstable : (prefixWord ++ tailWord_176761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176761).length < 2 ^ (prefixWord ++ tailWord_176761).sum := by decide
  have hdescent : baseEnd_176761 < baseStart_176761 := by decide
  rcases family_descends (prefixWord ++ tailWord_176761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176772 : List Nat := [2, 3, 2, 1, 3, 1, 8]
def baseStart_176772 : Nat := 118140960795 + 176772 * 2 ^ 59
def prefixEnd_176772 : Nat := 4983230072969 + 3 ^ 40 * 176772 * 2
def baseEnd_176772 : Nat := 8964839729055566660449

theorem tailTrace_176772 : CollatzResearch.WordTrace tailWord_176772 prefixEnd_176772 8964839729055566660449 := by
  unfold tailWord_176772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223702257796354549570285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4298269677061806066093713 3223702257796354549570285)
  ·
    refine ⟨1208888346673632956088857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3223702257796354549570285 1208888346673632956088857)
    ·
      refine ⟨906666260005224717066643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1208888346673632956088857 906666260005224717066643)
      ·
        refine ⟨1359999390007837075599965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906666260005224717066643 1359999390007837075599965)
        ·
          refine ⟨509999771252938903349987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1359999390007837075599965 509999771252938903349987)
          ·
            refine ⟨764999656879408355024981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509999771252938903349987 764999656879408355024981)
            ·
              refine ⟨8964839729055566660449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 764999656879408355024981 8964839729055566660449)
              ·
                rfl

theorem cell20_176772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_176772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176772 prefixEnd_176772 := by exact prefixLift 176772
  have htrace : WordTrace (prefixWord ++ tailWord_176772) baseStart_176772 baseEnd_176772 := by
    simpa [prefixWord, tailWord_176772, baseEnd_176772] using wordTrace_append hprefix tailTrace_176772
  have hstable : (prefixWord ++ tailWord_176772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176772).length < 2 ^ (prefixWord ++ tailWord_176772).sum := by decide
  have hdescent : baseEnd_176772 < baseStart_176772 := by decide
  rcases family_descends (prefixWord ++ tailWord_176772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176778 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_176778 : Nat := 118140960795 + 176778 * 2 ^ 59
def prefixEnd_176778 : Nat := 4983230072969 + 3 ^ 40 * 176778 * 2
def baseEnd_176778 : Nat := 80686296124990745744017

theorem tailTrace_176778 : CollatzResearch.WordTrace tailWord_176778 prefixEnd_176778 80686296124990745744017 := by
  unfold tailWord_176778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611905838392743030964747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4298415569047314749239325 1611905838392743030964747)
  ·
    refine ⟨2417858757589114546447121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1611905838392743030964747 2417858757589114546447121)
    ·
      refine ⟨1813394068191835909835341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2417858757589114546447121 1813394068191835909835341)
      ·
        refine ⟨680022775571938466188253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1813394068191835909835341 680022775571938466188253)
        ·
          refine ⟨255008540839476924820595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 680022775571938466188253 255008540839476924820595)
          ·
            refine ⟨382512811259215387230893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255008540839476924820595 382512811259215387230893)
            ·
              refine ⟨143442304222205770211585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382512811259215387230893 143442304222205770211585)
              ·
                refine ⟨107581728166654327658689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143442304222205770211585 107581728166654327658689)
                ·
                  refine ⟨80686296124990745744017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107581728166654327658689 80686296124990745744017)
                  ·
                    rfl

theorem cell20_176778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_176778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176778 prefixEnd_176778 := by exact prefixLift 176778
  have htrace : WordTrace (prefixWord ++ tailWord_176778) baseStart_176778 baseEnd_176778 := by
    simpa [prefixWord, tailWord_176778, baseEnd_176778] using wordTrace_append hprefix tailTrace_176778
  have hstable : (prefixWord ++ tailWord_176778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176778).length < 2 ^ (prefixWord ++ tailWord_176778).sum := by decide
  have hdescent : baseEnd_176778 < baseStart_176778 := by decide
  rcases family_descends (prefixWord ++ tailWord_176778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176831 : List Nat := [1, 1, 2, 2, 2, 12]
def baseStart_176831 : Nat := 118140960795 + 176831 * 2 ^ 59
def prefixEnd_176831 : Nat := 4983230072969 + 3 ^ 40 * 176831 * 2
def baseEnd_176831 : Nat := 2989277287746596925079

theorem tailTrace_176831 : CollatzResearch.WordTrace tailWord_176831 prefixEnd_176831 2989277287746596925079 := by
  unfold tailWord_176831
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449556422378962175538347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4299704281585974783692231 6449556422378962175538347)
  ·
    refine ⟨9674334633568443263307521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6449556422378962175538347 9674334633568443263307521)
    ·
      refine ⟨7255750975176332447480641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9674334633568443263307521 7255750975176332447480641)
      ·
        refine ⟨5441813231382249335610481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7255750975176332447480641 5441813231382249335610481)
        ·
          refine ⟨4081359923536687001707861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5441813231382249335610481 4081359923536687001707861)
          ·
            refine ⟨2989277287746596925079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4081359923536687001707861 2989277287746596925079)
            ·
              rfl

theorem cell20_176831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 12].length) (baseStart_176831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176831 prefixEnd_176831 := by exact prefixLift 176831
  have htrace : WordTrace (prefixWord ++ tailWord_176831) baseStart_176831 baseEnd_176831 := by
    simpa [prefixWord, tailWord_176831, baseEnd_176831] using wordTrace_append hprefix tailTrace_176831
  have hstable : (prefixWord ++ tailWord_176831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176831).length < 2 ^ (prefixWord ++ tailWord_176831).sum := by decide
  have hdescent : baseEnd_176831 < baseStart_176831 := by decide
  rcases family_descends (prefixWord ++ tailWord_176831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176865 : List Nat := [1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_176865 : Nat := 118140960795 + 176865 * 2 ^ 59
def prefixEnd_176865 : Nat := 4983230072969 + 3 ^ 40 * 176865 * 2
def baseEnd_176865 : Nat := 26908668431868369947887

theorem tailTrace_176865 : CollatzResearch.WordTrace tailWord_176865 prefixEnd_176865 26908668431868369947887 := by
  unfold tailWord_176865
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450796504255785982276049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4300531002837190654850699 6450796504255785982276049)
  ·
    refine ⟨4838097378191839486707037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6450796504255785982276049 4838097378191839486707037)
    ·
      refine ⟨1814286516821939807515139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4838097378191839486707037 1814286516821939807515139)
      ·
        refine ⟨2721429775232909711272709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814286516821939807515139 2721429775232909711272709)
        ·
          refine ⟨510268082856170570863633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2721429775232909711272709 510268082856170570863633)
          ·
            refine ⟨382701062142127928147725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510268082856170570863633 382701062142127928147725)
            ·
              refine ⟨143512898303297973055397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382701062142127928147725 143512898303297973055397)
              ·
                refine ⟨26908668431868369947887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143512898303297973055397 26908668431868369947887)
                ·
                  rfl

theorem cell20_176865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_176865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176865 prefixEnd_176865 := by exact prefixLift 176865
  have htrace : WordTrace (prefixWord ++ tailWord_176865) baseStart_176865 baseEnd_176865 := by
    simpa [prefixWord, tailWord_176865, baseEnd_176865] using wordTrace_append hprefix tailTrace_176865
  have hstable : (prefixWord ++ tailWord_176865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176865).length < 2 ^ (prefixWord ++ tailWord_176865).sum := by decide
  have hdescent : baseEnd_176865 < baseStart_176865 := by decide
  rcases family_descends (prefixWord ++ tailWord_176865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176886 : List Nat := [5, 1, 1, 1, 1, 2, 9]
def baseStart_176886 : Nat := 118140960795 + 176886 * 2 ^ 59
def prefixEnd_176886 : Nat := 4983230072969 + 3 ^ 40 * 176886 * 2
def baseEnd_176886 : Nat := 8970621140869152238175

theorem tailTrace_176886 : CollatzResearch.WordTrace tailWord_176886 prefixEnd_176886 8970621140869152238175 := by
  unfold tailWord_176886
  simp only [CollatzResearch.WordTrace]
  refine ⟨403222652323731660549407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4301041624786471045860341 403222652323731660549407)
  ·
    refine ⟨604833978485597490824111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403222652323731660549407 604833978485597490824111)
    ·
      refine ⟨907250967728396236236167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604833978485597490824111 907250967728396236236167)
      ·
        refine ⟨1360876451592594354354251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907250967728396236236167 1360876451592594354354251)
        ·
          refine ⟨2041314677388891531531377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360876451592594354354251 2041314677388891531531377)
          ·
            refine ⟨1530986008041668648648533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041314677388891531531377 1530986008041668648648533)
            ·
              refine ⟨8970621140869152238175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1530986008041668648648533 8970621140869152238175)
              ·
                rfl

theorem cell20_176886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_176886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176886 prefixEnd_176886 := by exact prefixLift 176886
  have htrace : WordTrace (prefixWord ++ tailWord_176886) baseStart_176886 baseEnd_176886 := by
    simpa [prefixWord, tailWord_176886, baseEnd_176886] using wordTrace_append hprefix tailTrace_176886
  have hstable : (prefixWord ++ tailWord_176886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176886).length < 2 ^ (prefixWord ++ tailWord_176886).sum := by decide
  have hdescent : baseEnd_176886 < baseStart_176886 := by decide
  rcases family_descends (prefixWord ++ tailWord_176886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176893 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_176893 : Nat := 118140960795 + 176893 * 2 ^ 59
def prefixEnd_176893 : Nat := 4983230072969 + 3 ^ 40 * 176893 * 2
def baseEnd_176893 : Nat := 80738785258561456910213

theorem tailTrace_176893 : CollatzResearch.WordTrace tailWord_176893 prefixEnd_176893 80738785258561456910213 := by
  unfold tailWord_176893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451817748154346764295333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4301211832102897842863555 6451817748154346764295333)
  ·
    refine ⟨1209715827778940018305375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6451817748154346764295333 1209715827778940018305375)
    ·
      refine ⟨1814573741668410027458063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209715827778940018305375 1814573741668410027458063)
      ·
        refine ⟨2721860612502615041187095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814573741668410027458063 2721860612502615041187095)
        ·
          refine ⟨4082790918753922561780643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721860612502615041187095 4082790918753922561780643)
          ·
            refine ⟨6124186378130883842670965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082790918753922561780643 6124186378130883842670965)
            ·
              refine ⟨574142472949770360250403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6124186378130883842670965 574142472949770360250403)
              ·
                refine ⟨861213709424655540375605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574142472949770360250403 861213709424655540375605)
                ·
                  refine ⟨80738785258561456910213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 861213709424655540375605 80738785258561456910213)
                  ·
                    rfl

theorem cell20_176893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_176893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176893 prefixEnd_176893 := by exact prefixLift 176893
  have htrace : WordTrace (prefixWord ++ tailWord_176893) baseStart_176893 baseEnd_176893 := by
    simpa [prefixWord, tailWord_176893, baseEnd_176893] using wordTrace_append hprefix tailTrace_176893
  have hstable : (prefixWord ++ tailWord_176893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176893).length < 2 ^ (prefixWord ++ tailWord_176893).sum := by decide
  have hdescent : baseEnd_176893 < baseStart_176893 := by decide
  rcases family_descends (prefixWord ++ tailWord_176893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176907 : List Nat := [1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_176907 : Nat := 118140960795 + 176907 * 2 ^ 59
def prefixEnd_176907 : Nat := 4983230072969 + 3 ^ 40 * 176907 * 2
def baseEnd_176907 : Nat := 26915058413346543481163

theorem tailTrace_176907 : CollatzResearch.WordTrace tailWord_176907 prefixEnd_176907 26915058413346543481163 := by
  unfold tailWord_176907
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452328370103627155304975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4301552246735751436869983 6452328370103627155304975)
  ·
    refine ⟨9678492555155440732957463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452328370103627155304975 9678492555155440732957463)
    ·
      refine ⟨14517738832733161099436195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678492555155440732957463 14517738832733161099436195)
      ·
        refine ⟨21776608249099741649154293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517738832733161099436195 21776608249099741649154293)
        ·
          refine ⟨2041557023353100779608215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21776608249099741649154293 2041557023353100779608215)
          ·
            refine ⟨3062335535029651169412323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041557023353100779608215 3062335535029651169412323)
            ·
              refine ⟨4593503302544476754118485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062335535029651169412323 4593503302544476754118485)
              ·
                refine ⟨26915058413346543481163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4593503302544476754118485 26915058413346543481163)
                ·
                  rfl

theorem cell20_176907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_176907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176907 prefixEnd_176907 := by exact prefixLift 176907
  have htrace : WordTrace (prefixWord ++ tailWord_176907) baseStart_176907 baseEnd_176907 := by
    simpa [prefixWord, tailWord_176907, baseEnd_176907] using wordTrace_append hprefix tailTrace_176907
  have hstable : (prefixWord ++ tailWord_176907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176907).length < 2 ^ (prefixWord ++ tailWord_176907).sum := by decide
  have hdescent : baseEnd_176907 < baseStart_176907 := by decide
  rcases family_descends (prefixWord ++ tailWord_176907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176924 : List Nat := [2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_176924 : Nat := 118140960795 + 176924 * 2 ^ 59
def prefixEnd_176924 : Nat := 4983230072969 + 3 ^ 40 * 176924 * 2
def baseEnd_176924 : Nat := 26917644834421042292251

theorem tailTrace_176924 : CollatzResearch.WordTrace tailWord_176924 prefixEnd_176924 26917644834421042292251 := by
  unfold tailWord_176924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226474205521019529336913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4301965607361359372449217 3226474205521019529336913)
  ·
    refine ⟨2419855654140764647002685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3226474205521019529336913 2419855654140764647002685)
    ·
      refine ⟨907445870302786742626007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2419855654140764647002685 907445870302786742626007)
      ·
        refine ⟨1361168805454180113939011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907445870302786742626007 1361168805454180113939011)
        ·
          refine ⟨2041753208181270170908517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361168805454180113939011 2041753208181270170908517)
          ·
            refine ⟨382828726533988157045347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2041753208181270170908517 382828726533988157045347)
            ·
              refine ⟨574243089800982235568021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382828726533988157045347 574243089800982235568021)
              ·
                refine ⟨26917644834421042292251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 574243089800982235568021 26917644834421042292251)
                ·
                  rfl

theorem cell20_176924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_176924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176924 prefixEnd_176924 := by exact prefixLift 176924
  have htrace : WordTrace (prefixWord ++ tailWord_176924) baseStart_176924 baseEnd_176924 := by
    simpa [prefixWord, tailWord_176924, baseEnd_176924] using wordTrace_append hprefix tailTrace_176924
  have hstable : (prefixWord ++ tailWord_176924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176924).length < 2 ^ (prefixWord ++ tailWord_176924).sum := by decide
  have hdescent : baseEnd_176924 < baseStart_176924 := by decide
  rcases family_descends (prefixWord ++ tailWord_176924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176961 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 3]
def baseStart_176961 : Nat := 118140960795 + 176961 * 2 ^ 59
def prefixEnd_176961 : Nat := 4983230072969 + 3 ^ 40 * 176961 * 2
def baseEnd_176961 : Nat := 80769822311455442643269

theorem tailTrace_176961 : CollatzResearch.WordTrace tailWord_176961 prefixEnd_176961 80769822311455442643269 := by
  unfold tailWord_176961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454297911907994377770737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4302865274605329585180491 6454297911907994377770737)
  ·
    refine ⟨4840723433930995783328053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6454297911907994377770737 4840723433930995783328053)
    ·
      refine ⟨453817821931030854687005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4840723433930995783328053 453817821931030854687005)
      ·
        refine ⟨170181683224136570507627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453817821931030854687005 170181683224136570507627)
        ·
          refine ⟨255272524836204855761441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170181683224136570507627 255272524836204855761441)
          ·
            refine ⟨191454393627153641821081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255272524836204855761441 191454393627153641821081)
            ·
              refine ⟨143590795220365231365811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191454393627153641821081 143590795220365231365811)
              ·
                refine ⟨215386192830547847048717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143590795220365231365811 215386192830547847048717)
                ·
                  refine ⟨80769822311455442643269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215386192830547847048717 80769822311455442643269)
                  ·
                    rfl

theorem cell20_176961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_176961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176961 prefixEnd_176961 := by exact prefixLift 176961
  have htrace : WordTrace (prefixWord ++ tailWord_176961) baseStart_176961 baseEnd_176961 := by
    simpa [prefixWord, tailWord_176961, baseEnd_176961] using wordTrace_append hprefix tailTrace_176961
  have hstable : (prefixWord ++ tailWord_176961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176961).length < 2 ^ (prefixWord ++ tailWord_176961).sum := by decide
  have hdescent : baseEnd_176961 < baseStart_176961 := by decide
  rcases family_descends (prefixWord ++ tailWord_176961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176976 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_176976 : Nat := 118140960795 + 176976 * 2 ^ 59
def prefixEnd_176976 : Nat := 4983230072969 + 3 ^ 40 * 176976 * 2
def baseEnd_176976 : Nat := 80776668720182057143207

theorem tailTrace_176976 : CollatzResearch.WordTrace tailWord_176976 prefixEnd_176976 80776668720182057143207 := by
  unfold tailWord_176976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227422503426825969783391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4303230004569101293044521 3227422503426825969783391)
  ·
    refine ⟨4841133755140238954675087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227422503426825969783391 4841133755140238954675087)
    ·
      refine ⟨7261700632710358432012631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4841133755140238954675087 7261700632710358432012631)
      ·
        refine ⟨10892550949065537648018947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7261700632710358432012631 10892550949065537648018947)
        ·
          refine ⟨16338826423598306472028421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10892550949065537648018947 16338826423598306472028421)
          ·
            refine ⟨3063529954424682463505329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16338826423598306472028421 3063529954424682463505329)
            ·
              refine ⟨2297647465818511847628997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063529954424682463505329 2297647465818511847628997)
              ·
                refine ⟨430808899840970971430437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2297647465818511847628997 430808899840970971430437)
                ·
                  refine ⟨80776668720182057143207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430808899840970971430437 80776668720182057143207)
                  ·
                    rfl

theorem cell20_176976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_176976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_176976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_176976 prefixEnd_176976 := by exact prefixLift 176976
  have htrace : WordTrace (prefixWord ++ tailWord_176976) baseStart_176976 baseEnd_176976 := by
    simpa [prefixWord, tailWord_176976, baseEnd_176976] using wordTrace_append hprefix tailTrace_176976
  have hstable : (prefixWord ++ tailWord_176976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176976).length < 2 ^ (prefixWord ++ tailWord_176976).sum := by decide
  have hdescent : baseEnd_176976 < baseStart_176976 := by decide
  rcases family_descends (prefixWord ++ tailWord_176976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177031 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_177031 : Nat := 118140960795 + 177031 * 2 ^ 59
def prefixEnd_177031 : Nat := 4983230072969 + 3 ^ 40 * 177031 * 2
def baseEnd_177031 : Nat := 80801772218846310309649

theorem tailTrace_177031 : CollatzResearch.WordTrace tailWord_177031 prefixEnd_177031 80801772218846310309649 := by
  unfold tailWord_177031
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456851021654396332818947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4304567347769597555212631 6456851021654396332818947)
  ·
    refine ⟨9685276532481594499228421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6456851021654396332818947 9685276532481594499228421)
    ·
      refine ⟨1815989349840298968605329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9685276532481594499228421 1815989349840298968605329)
      ·
        refine ⟨1361992012380224226453997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815989349840298968605329 1361992012380224226453997)
        ·
          refine ⟨510747004642584084920249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1361992012380224226453997 510747004642584084920249)
          ·
            refine ⟨383060253481938063690187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510747004642584084920249 383060253481938063690187)
            ·
              refine ⟨574590380222907095535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383060253481938063690187 574590380222907095535281)
              ·
                refine ⟨430942785167180321651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574590380222907095535281 430942785167180321651461)
                ·
                  refine ⟨80801772218846310309649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430942785167180321651461 80801772218846310309649)
                  ·
                    rfl

theorem cell20_177031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_177031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177031 prefixEnd_177031 := by exact prefixLift 177031
  have htrace : WordTrace (prefixWord ++ tailWord_177031) baseStart_177031 baseEnd_177031 := by
    simpa [prefixWord, tailWord_177031, baseEnd_177031] using wordTrace_append hprefix tailTrace_177031
  have hstable : (prefixWord ++ tailWord_177031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177031).length < 2 ^ (prefixWord ++ tailWord_177031).sum := by decide
  have hdescent : baseEnd_177031 < baseStart_177031 := by decide
  rcases family_descends (prefixWord ++ tailWord_177031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177114 : List Nat := [3, 1, 1, 2, 4, 3, 6]
def baseStart_177114 : Nat := 118140960795 + 177114 * 2 ^ 59
def prefixEnd_177114 : Nat := 4983230072969 + 3 ^ 40 * 177114 * 2
def baseEnd_177114 : Nat := 8982183964496323393627

theorem tailTrace_177114 : CollatzResearch.WordTrace tailWord_177114 prefixEnd_177114 8982183964496323393627 := by
  unfold tailWord_177114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614969570088425377022599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4306585520235801005393597 1614969570088425377022599)
  ·
    refine ⟨2422454355132638065533899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614969570088425377022599 2422454355132638065533899)
    ·
      refine ⟨3633681532698957098300849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422454355132638065533899 3633681532698957098300849)
      ·
        refine ⟨2725261149524217823725637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3633681532698957098300849 2725261149524217823725637)
        ·
          refine ⟨510986465535790841948557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2725261149524217823725637 510986465535790841948557)
          ·
            refine ⟨191619924575921565730709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510986465535790841948557 191619924575921565730709)
            ·
              refine ⟨8982183964496323393627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191619924575921565730709 8982183964496323393627)
              ·
                rfl

theorem cell20_177114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_177114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177114 prefixEnd_177114 := by exact prefixLift 177114
  have htrace : WordTrace (prefixWord ++ tailWord_177114) baseStart_177114 baseEnd_177114 := by
    simpa [prefixWord, tailWord_177114, baseEnd_177114] using wordTrace_append hprefix tailTrace_177114
  have hstable : (prefixWord ++ tailWord_177114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177114).length < 2 ^ (prefixWord ++ tailWord_177114).sum := by decide
  have hdescent : baseEnd_177114 < baseStart_177114 := by decide
  rcases family_descends (prefixWord ++ tailWord_177114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177121 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_177121 : Nat := 118140960795 + 177121 * 2 ^ 59
def prefixEnd_177121 : Nat := 4983230072969 + 3 ^ 40 * 177121 * 2
def baseEnd_177121 : Nat := 80842850671205997309281

theorem tailTrace_177121 : CollatzResearch.WordTrace tailWord_177121 prefixEnd_177121 80842850671205997309281 := by
  unfold tailWord_177121
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460133591328341703595217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4306755727552227802396811 6460133591328341703595217)
  ·
    refine ⟨4845100193496256277696413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6460133591328341703595217 4845100193496256277696413)
    ·
      refine ⟨1816912572561096104136155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4845100193496256277696413 1816912572561096104136155)
      ·
        refine ⟨2725368858841644156204233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816912572561096104136155 2725368858841644156204233)
        ·
          refine ⟨2044026644131233117153175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725368858841644156204233 2044026644131233117153175)
          ·
            refine ⟨3066039966196849675729763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044026644131233117153175 3066039966196849675729763)
            ·
              refine ⟨4599059949295274513594645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066039966196849675729763 4599059949295274513594645)
              ·
                refine ⟨215580935123215992824749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4599059949295274513594645 215580935123215992824749)
                ·
                  refine ⟨80842850671205997309281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215580935123215992824749 80842850671205997309281)
                  ·
                    rfl

theorem cell20_177121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_177121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177121 prefixEnd_177121 := by exact prefixLift 177121
  have htrace : WordTrace (prefixWord ++ tailWord_177121) baseStart_177121 baseEnd_177121 := by
    simpa [prefixWord, tailWord_177121, baseEnd_177121] using wordTrace_append hprefix tailTrace_177121
  have hstable : (prefixWord ++ tailWord_177121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177121).length < 2 ^ (prefixWord ++ tailWord_177121).sum := by decide
  have hdescent : baseEnd_177121 < baseStart_177121 := by decide
  rcases family_descends (prefixWord ++ tailWord_177121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177134 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_177134 : Nat := 118140960795 + 177134 * 2 ^ 59
def prefixEnd_177134 : Nat := 4983230072969 + 3 ^ 40 * 177134 * 2
def baseEnd_177134 : Nat := 80848784225435729875895

theorem tailTrace_177134 : CollatzResearch.WordTrace tailWord_177134 prefixEnd_177134 80848784225435729875895 := by
  unfold tailWord_177134
  simp only [CollatzResearch.WordTrace]
  refine ⟨807575967535155615477307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4307071826854163282545637 807575967535155615477307)
  ·
    refine ⟨1211363951302733423215961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 807575967535155615477307 1211363951302733423215961)
    ·
      refine ⟨908522963477050067411971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1211363951302733423215961 908522963477050067411971)
      ·
        refine ⟨1362784445215575101117957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908522963477050067411971 1362784445215575101117957)
        ·
          refine ⟨255522083477920331459617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1362784445215575101117957 255522083477920331459617)
          ·
            refine ⟨191641562608440248594713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255522083477920331459617 191641562608440248594713)
            ·
              refine ⟨143731171956330186446035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191641562608440248594713 143731171956330186446035)
              ·
                refine ⟨215596757934495279669053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143731171956330186446035 215596757934495279669053)
                ·
                  refine ⟨80848784225435729875895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215596757934495279669053 80848784225435729875895)
                  ·
                    rfl

theorem cell20_177134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_177134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177134 prefixEnd_177134 := by exact prefixLift 177134
  have htrace : WordTrace (prefixWord ++ tailWord_177134) baseStart_177134 baseEnd_177134 := by
    simpa [prefixWord, tailWord_177134, baseEnd_177134] using wordTrace_append hprefix tailTrace_177134
  have hstable : (prefixWord ++ tailWord_177134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177134).length < 2 ^ (prefixWord ++ tailWord_177134).sum := by decide
  have hdescent : baseEnd_177134 < baseStart_177134 := by decide
  rcases family_descends (prefixWord ++ tailWord_177134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177135 : List Nat := [1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_177135 : Nat := 118140960795 + 177135 * 2 ^ 59
def prefixEnd_177135 : Nat := 4983230072969 + 3 ^ 40 * 177135 * 2
def baseEnd_177135 : Nat := 26949746884228056947519

theorem tailTrace_177135 : CollatzResearch.WordTrace tailWord_177135 prefixEnd_177135 26949746884228056947519 := by
  unfold tailWord_177135
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460644213277622094604859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4307096142185081396403239 6460644213277622094604859)
  ·
    refine ⟨9690966319916433141907289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6460644213277622094604859 9690966319916433141907289)
    ·
      refine ⟨7268224739937324856430467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9690966319916433141907289 7268224739937324856430467)
      ·
        refine ⟨10902337109905987284645701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7268224739937324856430467 10902337109905987284645701)
        ·
          refine ⟨2044188208107372615871069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10902337109905987284645701 2044188208107372615871069)
          ·
            refine ⟨766570578040264730951651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2044188208107372615871069 766570578040264730951651)
            ·
              refine ⟨1149855867060397096427477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766570578040264730951651 1149855867060397096427477)
              ·
                refine ⟨26949746884228056947519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1149855867060397096427477 26949746884228056947519)
                ·
                  rfl

theorem cell20_177135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_177135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177135 prefixEnd_177135 := by exact prefixLift 177135
  have htrace : WordTrace (prefixWord ++ tailWord_177135) baseStart_177135 baseEnd_177135 := by
    simpa [prefixWord, tailWord_177135, baseEnd_177135] using wordTrace_append hprefix tailTrace_177135
  have hstable : (prefixWord ++ tailWord_177135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177135).length < 2 ^ (prefixWord ++ tailWord_177135).sum := by decide
  have hdescent : baseEnd_177135 < baseStart_177135 := by decide
  rcases family_descends (prefixWord ++ tailWord_177135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177173 : List Nat := [1, 3, 2, 1, 4, 9]
def baseStart_177173 : Nat := 118140960795 + 177173 * 2 ^ 59
def prefixEnd_177173 : Nat := 4983230072969 + 3 ^ 40 * 177173 * 2
def baseEnd_177173 : Nat := 2995058699560182502805

theorem tailTrace_177173 : CollatzResearch.WordTrace tailWord_177173 prefixEnd_177173 2995058699560182502805 := by
  unfold tailWord_177173
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462030187139954584488173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4308020124759969722992115 6462030187139954584488173)
  ·
    refine ⟨2423261320177482969183065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6462030187139954584488173 2423261320177482969183065)
    ·
      refine ⟨1817445990133112226887299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2423261320177482969183065 1817445990133112226887299)
      ·
        refine ⟨2726168985199668340330949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817445990133112226887299 2726168985199668340330949)
        ·
          refine ⟨511156684724937813812053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2726168985199668340330949 511156684724937813812053)
          ·
            refine ⟨2995058699560182502805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 511156684724937813812053 2995058699560182502805)
            ·
              rfl

theorem cell20_177173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 9].length) (baseStart_177173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177173 prefixEnd_177173 := by exact prefixLift 177173
  have htrace : WordTrace (prefixWord ++ tailWord_177173) baseStart_177173 baseEnd_177173 := by
    simpa [prefixWord, tailWord_177173, baseEnd_177173] using wordTrace_append hprefix tailTrace_177173
  have hstable : (prefixWord ++ tailWord_177173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177173).length < 2 ^ (prefixWord ++ tailWord_177173).sum := by decide
  have hdescent : baseEnd_177173 < baseStart_177173 := by decide
  rcases family_descends (prefixWord ++ tailWord_177173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177176 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_177176 : Nat := 118140960795 + 177176 * 2 ^ 59
def prefixEnd_177176 : Nat := 4983230072969 + 3 ^ 40 * 177176 * 2
def baseEnd_177176 : Nat := 80867954169870250475723

theorem tailTrace_177176 : CollatzResearch.WordTrace tailWord_177176 prefixEnd_177176 80867954169870250475723 := by
  unfold tailWord_177176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231069803064543048423691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4308093070752724064564921 3231069803064543048423691)
  ·
    refine ⟨4846604704596814572635537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231069803064543048423691 4846604704596814572635537)
    ·
      refine ⟨3634953528447610929476653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4846604704596814572635537 3634953528447610929476653)
      ·
        refine ⟨1363107573167854098553745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3634953528447610929476653 1363107573167854098553745)
        ·
          refine ⟨1022330679875890573915309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363107573167854098553745 1022330679875890573915309)
          ·
            refine ⟨383374004953458965218241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1022330679875890573915309 383374004953458965218241)
            ·
              refine ⟨287530503715094223913681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383374004953458965218241 287530503715094223913681)
              ·
                refine ⟨215647877786320667935261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287530503715094223913681 215647877786320667935261)
                ·
                  refine ⟨80867954169870250475723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215647877786320667935261 80867954169870250475723)
                  ·
                    rfl

theorem cell20_177176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_177176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177176 prefixEnd_177176 := by exact prefixLift 177176
  have htrace : WordTrace (prefixWord ++ tailWord_177176) baseStart_177176 baseEnd_177176 := by
    simpa [prefixWord, tailWord_177176, baseEnd_177176] using wordTrace_append hprefix tailTrace_177176
  have hstable : (prefixWord ++ tailWord_177176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177176).length < 2 ^ (prefixWord ++ tailWord_177176).sum := by decide
  have hdescent : baseEnd_177176 < baseStart_177176 := by decide
  rcases family_descends (prefixWord ++ tailWord_177176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177217 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 2]
def baseStart_177217 : Nat := 118140960795 + 177217 * 2 ^ 59
def prefixEnd_177217 : Nat := 4983230072969 + 3 ^ 40 * 177217 * 2
def baseEnd_177217 : Nat := 80886667687056330108889

theorem tailTrace_177217 : CollatzResearch.WordTrace tailWord_177217 prefixEnd_177217 80886667687056330108889 := by
  unfold tailWord_177217
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463634998980550099089905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4309089999320366732726603 6463634998980550099089905)
  ·
    refine ⟨4847726249235412574317429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6463634998980550099089905 4847726249235412574317429)
    ·
      refine ⟨454474335865819928842259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4847726249235412574317429 454474335865819928842259)
      ·
        refine ⟨681711503798729893263389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454474335865819928842259 681711503798729893263389)
        ·
          refine ⟨255641813924523709973771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681711503798729893263389 255641813924523709973771)
          ·
            refine ⟨383462720886785564960657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255641813924523709973771 383462720886785564960657)
            ·
              refine ⟨287597040665089173720493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383462720886785564960657 287597040665089173720493)
              ·
                refine ⟨107848890249408440145185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287597040665089173720493 107848890249408440145185)
                ·
                  refine ⟨80886667687056330108889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107848890249408440145185 80886667687056330108889)
                  ·
                    rfl

theorem cell20_177217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_177217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177217 prefixEnd_177217 := by exact prefixLift 177217
  have htrace : WordTrace (prefixWord ++ tailWord_177217) baseStart_177217 baseEnd_177217 := by
    simpa [prefixWord, tailWord_177217, baseEnd_177217] using wordTrace_append hprefix tailTrace_177217
  have hstable : (prefixWord ++ tailWord_177217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177217).length < 2 ^ (prefixWord ++ tailWord_177217).sum := by decide
  have hdescent : baseEnd_177217 < baseStart_177217 := by decide
  rcases family_descends (prefixWord ++ tailWord_177217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177221 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 2]
def baseStart_177221 : Nat := 118140960795 + 177221 * 2 ^ 59
def prefixEnd_177221 : Nat := 4983230072969 + 3 ^ 40 * 177221 * 2
def baseEnd_177221 : Nat := 80888493396050093975539

theorem tailTrace_177221 : CollatzResearch.WordTrace tailWord_177221 prefixEnd_177221 80888493396050093975539 := by
  unfold tailWord_177221
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463780890966058782235517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4309187260644039188157011 6463780890966058782235517)
  ·
    refine ⟨2423917834112272043338319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6463780890966058782235517 2423917834112272043338319)
    ·
      refine ⟨3635876751168408065007479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423917834112272043338319 3635876751168408065007479)
      ·
        refine ⟨5453815126752612097511219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635876751168408065007479 5453815126752612097511219)
        ·
          refine ⟨8180722690128918146266829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453815126752612097511219 8180722690128918146266829)
          ·
            refine ⟨3067771008798344304850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8180722690128918146266829 3067771008798344304850061)
            ·
              refine ⟨1150414128299379114318773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3067771008798344304850061 1150414128299379114318773)
              ·
                refine ⟨107851324528066791967385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1150414128299379114318773 107851324528066791967385)
                ·
                  refine ⟨80888493396050093975539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107851324528066791967385 80888493396050093975539)
                  ·
                    rfl

theorem cell20_177221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_177221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177221 prefixEnd_177221 := by exact prefixLift 177221
  have htrace : WordTrace (prefixWord ++ tailWord_177221) baseStart_177221 baseEnd_177221 := by
    simpa [prefixWord, tailWord_177221, baseEnd_177221] using wordTrace_append hprefix tailTrace_177221
  have hstable : (prefixWord ++ tailWord_177221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177221).length < 2 ^ (prefixWord ++ tailWord_177221).sum := by decide
  have hdescent : baseEnd_177221 < baseStart_177221 := by decide
  rcases family_descends (prefixWord ++ tailWord_177221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177304 : List Nat := [2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_177304 : Nat := 118140960795 + 177304 * 2 ^ 59
def prefixEnd_177304 : Nat := 4983230072969 + 3 ^ 40 * 177304 * 2
def baseEnd_177304 : Nat := 26975458952556898069511

theorem tailTrace_177304 : CollatzResearch.WordTrace tailWord_177304 prefixEnd_177304 26975458952556898069511 := by
  unfold tailWord_177304
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233404074832681978753483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4311205433110242638337977 3233404074832681978753483)
  ·
    refine ⟨4850106112249022968130225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233404074832681978753483 4850106112249022968130225)
    ·
      refine ⟨3637579584186767226097669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4850106112249022968130225 3637579584186767226097669)
      ·
        refine ⟨682046172035018854893313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3637579584186767226097669 682046172035018854893313)
        ·
          refine ⟨511534629026264141169985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682046172035018854893313 511534629026264141169985)
          ·
            refine ⟨383650971769698105877489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511534629026264141169985 383650971769698105877489)
            ·
              refine ⟨287738228827273579408117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383650971769698105877489 287738228827273579408117)
              ·
                refine ⟨26975458952556898069511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287738228827273579408117 26975458952556898069511)
                ·
                  rfl

theorem cell20_177304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_177304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177304 prefixEnd_177304 := by exact prefixLift 177304
  have htrace : WordTrace (prefixWord ++ tailWord_177304) baseStart_177304 baseEnd_177304 := by
    simpa [prefixWord, tailWord_177304, baseEnd_177304] using wordTrace_append hprefix tailTrace_177304
  have hstable : (prefixWord ++ tailWord_177304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177304).length < 2 ^ (prefixWord ++ tailWord_177304).sum := by decide
  have hdescent : baseEnd_177304 < baseStart_177304 := by decide
  rcases family_descends (prefixWord ++ tailWord_177304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177335 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 2]
def baseStart_177335 : Nat := 118140960795 + 177335 * 2 ^ 59
def prefixEnd_177335 : Nat := 4983230072969 + 3 ^ 40 * 177335 * 2
def baseEnd_177335 : Nat := 80940526102372364175073

theorem tailTrace_177335 : CollatzResearch.WordTrace tailWord_177335 prefixEnd_177335 80940526102372364175073 := by
  unfold tailWord_177335
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467938812553056251885459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4311959208368704167923639 6467938812553056251885459)
  ·
    refine ⟨9701908218829584377828189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467938812553056251885459 9701908218829584377828189)
    ·
      refine ⟨3638215582061094141685571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9701908218829584377828189 3638215582061094141685571)
      ·
        refine ⟨5457323373091641212528357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638215582061094141685571 5457323373091641212528357)
        ·
          refine ⟨1023248132454682727349067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5457323373091641212528357 1023248132454682727349067)
          ·
            refine ⟨1534872198682024091023601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023248132454682727349067 1534872198682024091023601)
            ·
              refine ⟨1151154149011518068267701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534872198682024091023601 1151154149011518068267701)
              ·
                refine ⟨107920701469829818900097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151154149011518068267701 107920701469829818900097)
                ·
                  refine ⟨80940526102372364175073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107920701469829818900097 80940526102372364175073)
                  ·
                    rfl

theorem cell20_177335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2].length) (baseStart_177335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177335 prefixEnd_177335 := by exact prefixLift 177335
  have htrace : WordTrace (prefixWord ++ tailWord_177335) baseStart_177335 baseEnd_177335 := by
    simpa [prefixWord, tailWord_177335, baseEnd_177335] using wordTrace_append hprefix tailTrace_177335
  have hstable : (prefixWord ++ tailWord_177335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177335).length < 2 ^ (prefixWord ++ tailWord_177335).sum := by decide
  have hdescent : baseEnd_177335 < baseStart_177335 := by decide
  rcases family_descends (prefixWord ++ tailWord_177335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177339 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_177339 : Nat := 118140960795 + 177339 * 2 ^ 59
def prefixEnd_177339 : Nat := 4983230072969 + 3 ^ 40 * 177339 * 2
def baseEnd_177339 : Nat := 80942351811366128041723

theorem tailTrace_177339 : CollatzResearch.WordTrace tailWord_177339 prefixEnd_177339 80942351811366128041723 := by
  unfold tailWord_177339
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468084704538564935031071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4312056469692376623354047 6468084704538564935031071)
  ·
    refine ⟨9702127056807847402546607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6468084704538564935031071 9702127056807847402546607)
    ·
      refine ⟨14553190585211771103819911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702127056807847402546607 14553190585211771103819911)
      ·
        refine ⟨21829785877817656655729867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553190585211771103819911 21829785877817656655729867)
        ·
          refine ⟨32744678816726484983594801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21829785877817656655729867 32744678816726484983594801)
          ·
            refine ⟨24558509112544863737696101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32744678816726484983594801 24558509112544863737696101)
            ·
              refine ⟨4604720458602161950818019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24558509112544863737696101 4604720458602161950818019)
              ·
                refine ⟨6907080687903242926227029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604720458602161950818019 6907080687903242926227029)
                ·
                  refine ⟨80942351811366128041723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6907080687903242926227029 80942351811366128041723)
                  ·
                    rfl

theorem cell20_177339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_177339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177339 prefixEnd_177339 := by exact prefixLift 177339
  have htrace : WordTrace (prefixWord ++ tailWord_177339) baseStart_177339 baseEnd_177339 := by
    simpa [prefixWord, tailWord_177339, baseEnd_177339] using wordTrace_append hprefix tailTrace_177339
  have hstable : (prefixWord ++ tailWord_177339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177339).length < 2 ^ (prefixWord ++ tailWord_177339).sum := by decide
  have hdescent : baseEnd_177339 < baseStart_177339 := by decide
  rcases family_descends (prefixWord ++ tailWord_177339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177345 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_177345 : Nat := 118140960795 + 177345 * 2 ^ 59
def prefixEnd_177345 : Nat := 4983230072969 + 3 ^ 40 * 177345 * 2
def baseEnd_177345 : Nat := 80945090374856773841699

theorem tailTrace_177345 : CollatzResearch.WordTrace tailWord_177345 prefixEnd_177345 80945090374856773841699 := by
  unfold tailWord_177345
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468303542516827959749489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4312202361677885306499659 6468303542516827959749489)
  ·
    refine ⟨4851227656887620969812117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6468303542516827959749489 4851227656887620969812117)
    ·
      refine ⟨227401296416607232959943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4851227656887620969812117 227401296416607232959943)
      ·
        refine ⟨341101944624910849439915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227401296416607232959943 341101944624910849439915)
        ·
          refine ⟨511652916937366274159873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341101944624910849439915 511652916937366274159873)
          ·
            refine ⟨383739687703024705619905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511652916937366274159873 383739687703024705619905)
            ·
              refine ⟨287804765777268529214929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383739687703024705619905 287804765777268529214929)
              ·
                refine ⟨215853574332951396911197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287804765777268529214929 215853574332951396911197)
                ·
                  refine ⟨80945090374856773841699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215853574332951396911197 80945090374856773841699)
                  ·
                    rfl

theorem cell20_177345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_177345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177345 prefixEnd_177345 := by exact prefixLift 177345
  have htrace : WordTrace (prefixWord ++ tailWord_177345) baseStart_177345 baseEnd_177345 := by
    simpa [prefixWord, tailWord_177345, baseEnd_177345] using wordTrace_append hprefix tailTrace_177345
  have hstable : (prefixWord ++ tailWord_177345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177345).length < 2 ^ (prefixWord ++ tailWord_177345).sum := by decide
  have hdescent : baseEnd_177345 < baseStart_177345 := by decide
  rcases family_descends (prefixWord ++ tailWord_177345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177348 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_177348 : Nat := 118140960795 + 177348 * 2 ^ 59
def prefixEnd_177348 : Nat := 4983230072969 + 3 ^ 40 * 177348 * 2
def baseEnd_177348 : Nat := 80946459656602096741687

theorem tailTrace_177348 : CollatzResearch.WordTrace tailWord_177348 prefixEnd_177348 80946459656602096741687 := by
  unfold tailWord_177348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234206480752979736054349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4312275307670639648072465 3234206480752979736054349)
  ·
    refine ⟨1212827430282367401020381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3234206480752979736054349 1212827430282367401020381)
    ·
      refine ⟨454810286355887775382643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1212827430282367401020381 454810286355887775382643)
      ·
        refine ⟨682215429533831663073965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454810286355887775382643 682215429533831663073965)
        ·
          refine ⟨255830786075186873652737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 682215429533831663073965 255830786075186873652737)
          ·
            refine ⟨191873089556390155239553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255830786075186873652737 191873089556390155239553)
            ·
              refine ⟨143904817167292616429665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191873089556390155239553 143904817167292616429665)
              ·
                refine ⟨107928612875469462322249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143904817167292616429665 107928612875469462322249)
                ·
                  refine ⟨80946459656602096741687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107928612875469462322249 80946459656602096741687)
                  ·
                    rfl

theorem cell20_177348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_177348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177348 prefixEnd_177348 := by exact prefixLift 177348
  have htrace : WordTrace (prefixWord ++ tailWord_177348) baseStart_177348 baseEnd_177348 := by
    simpa [prefixWord, tailWord_177348, baseEnd_177348] using wordTrace_append hprefix tailTrace_177348
  have hstable : (prefixWord ++ tailWord_177348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177348).length < 2 ^ (prefixWord ++ tailWord_177348).sum := by decide
  have hdescent : baseEnd_177348 < baseStart_177348 := by decide
  rcases family_descends (prefixWord ++ tailWord_177348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177352 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_177352 : Nat := 118140960795 + 177352 * 2 ^ 59
def prefixEnd_177352 : Nat := 4983230072969 + 3 ^ 40 * 177352 * 2
def baseEnd_177352 : Nat := 80948285365595860608337

theorem tailTrace_177352 : CollatzResearch.WordTrace tailWord_177352 prefixEnd_177352 80948285365595860608337 := by
  unfold tailWord_177352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234279426745734077627155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4312372568994312103502873 3234279426745734077627155)
  ·
    refine ⟨4851419140118601116440733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234279426745734077627155 4851419140118601116440733)
    ·
      refine ⟨1819282177544475418665275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4851419140118601116440733 1819282177544475418665275)
      ·
        refine ⟨2728923266316713127997913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819282177544475418665275 2728923266316713127997913)
        ·
          refine ⟨2046692449737534845998435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728923266316713127997913 2046692449737534845998435)
          ·
            refine ⟨3070038674606302268997653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046692449737534845998435 3070038674606302268997653)
            ·
              refine ⟨143908062872170418859265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3070038674606302268997653 143908062872170418859265)
              ·
                refine ⟨107931047154127814144449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143908062872170418859265 107931047154127814144449)
                ·
                  refine ⟨80948285365595860608337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107931047154127814144449 80948285365595860608337)
                  ·
                    rfl

theorem cell20_177352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_177352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177352 prefixEnd_177352 := by exact prefixLift 177352
  have htrace : WordTrace (prefixWord ++ tailWord_177352) baseStart_177352 baseEnd_177352 := by
    simpa [prefixWord, tailWord_177352, baseEnd_177352] using wordTrace_append hprefix tailTrace_177352
  have hstable : (prefixWord ++ tailWord_177352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177352).length < 2 ^ (prefixWord ++ tailWord_177352).sum := by decide
  have hdescent : baseEnd_177352 < baseStart_177352 := by decide
  rcases family_descends (prefixWord ++ tailWord_177352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177370 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_177370 : Nat := 118140960795 + 177370 * 2 ^ 59
def prefixEnd_177370 : Nat := 4983230072969 + 3 ^ 40 * 177370 * 2
def baseEnd_177370 : Nat := 80956501056067798008263

theorem tailTrace_177370 : CollatzResearch.WordTrace tailWord_177370 prefixEnd_177370 80956501056067798008263 := by
  unfold tailWord_177370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617303841856564307352391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4312810244950838152939709 1617303841856564307352391)
  ·
    refine ⟨2425955762784846461028587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1617303841856564307352391 2425955762784846461028587)
    ·
      refine ⟨3638933644177269691542881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425955762784846461028587 3638933644177269691542881)
      ·
        refine ⟨2729200233132952268657161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3638933644177269691542881 2729200233132952268657161)
        ·
          refine ⟨2046900174849714201492871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729200233132952268657161 2046900174849714201492871)
          ·
            refine ⟨3070350262274571302239307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046900174849714201492871 3070350262274571302239307)
            ·
              refine ⟨4605525393411856953358961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070350262274571302239307 4605525393411856953358961)
              ·
                refine ⟨3454144045058892715019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605525393411856953358961 3454144045058892715019221)
                ·
                  refine ⟨80956501056067798008263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3454144045058892715019221 80956501056067798008263)
                  ·
                    rfl

theorem cell20_177370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_177370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177370 prefixEnd_177370 := by exact prefixLift 177370
  have htrace : WordTrace (prefixWord ++ tailWord_177370) baseStart_177370 baseEnd_177370 := by
    simpa [prefixWord, tailWord_177370, baseEnd_177370] using wordTrace_append hprefix tailTrace_177370
  have hstable : (prefixWord ++ tailWord_177370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177370).length < 2 ^ (prefixWord ++ tailWord_177370).sum := by decide
  have hdescent : baseEnd_177370 < baseStart_177370 := by decide
  rcases family_descends (prefixWord ++ tailWord_177370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177396 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_177396 : Nat := 118140960795 + 177396 * 2 ^ 59
def prefixEnd_177396 : Nat := 4983230072969 + 3 ^ 40 * 177396 * 2
def baseEnd_177396 : Nat := 80968368164527263141491

theorem tailTrace_177396 : CollatzResearch.WordTrace tailWord_177396 prefixEnd_177396 80968368164527263141491 := by
  unfold tailWord_177396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235081832666031834928021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4313442443554709113237361 3235081832666031834928021)
  ·
    refine ⟨151644460906220242262251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3235081832666031834928021 151644460906220242262251)
    ·
      refine ⟨227466691359330363393377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151644460906220242262251 227466691359330363393377)
      ·
        refine ⟨170600018519497772545033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227466691359330363393377 170600018519497772545033)
        ·
          refine ⟨127950013889623329408775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170600018519497772545033 127950013889623329408775)
          ·
            refine ⟨191925020834434994113163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127950013889623329408775 191925020834434994113163)
            ·
              refine ⟨287887531251652491169745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191925020834434994113163 287887531251652491169745)
              ·
                refine ⟨215915648438739368377309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287887531251652491169745 215915648438739368377309)
                ·
                  refine ⟨80968368164527263141491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215915648438739368377309 80968368164527263141491)
                  ·
                    rfl

theorem cell20_177396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_177396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177396 prefixEnd_177396 := by exact prefixLift 177396
  have htrace : WordTrace (prefixWord ++ tailWord_177396) baseStart_177396 baseEnd_177396 := by
    simpa [prefixWord, tailWord_177396, baseEnd_177396] using wordTrace_append hprefix tailTrace_177396
  have hstable : (prefixWord ++ tailWord_177396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177396).length < 2 ^ (prefixWord ++ tailWord_177396).sum := by decide
  have hdescent : baseEnd_177396 < baseStart_177396 := by decide
  rcases family_descends (prefixWord ++ tailWord_177396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177411 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 2]
def baseStart_177411 : Nat := 118140960795 + 177411 * 2 ^ 59
def prefixEnd_177411 : Nat := 4983230072969 + 3 ^ 40 * 177411 * 2
def baseEnd_177411 : Nat := 80975214573253877641429

theorem tailTrace_177411 : CollatzResearch.WordTrace tailWord_177411 prefixEnd_177411 80975214573253877641429 := by
  unfold tailWord_177411
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470710760277721231652087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4313807173518480821101391 6470710760277721231652087)
  ·
    refine ⟨9706066140416581847478131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6470710760277721231652087 9706066140416581847478131)
    ·
      refine ⟨14559099210624872771217197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706066140416581847478131 14559099210624872771217197)
      ·
        refine ⟨5459662203984327289206449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14559099210624872771217197 5459662203984327289206449)
        ·
          refine ⟨4094746652988245466904837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459662203984327289206449 4094746652988245466904837)
          ·
            refine ⟨767764997435296025044657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4094746652988245466904837 767764997435296025044657)
            ·
              refine ⟨575823748076472018783493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767764997435296025044657 575823748076472018783493)
              ·
                refine ⟨107966952764338503521905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575823748076472018783493 107966952764338503521905)
                ·
                  refine ⟨80975214573253877641429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107966952764338503521905 80975214573253877641429)
                  ·
                    rfl

theorem cell20_177411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2].length) (baseStart_177411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177411 prefixEnd_177411 := by exact prefixLift 177411
  have htrace : WordTrace (prefixWord ++ tailWord_177411) baseStart_177411 baseEnd_177411 := by
    simpa [prefixWord, tailWord_177411, baseEnd_177411] using wordTrace_append hprefix tailTrace_177411
  have hstable : (prefixWord ++ tailWord_177411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177411).length < 2 ^ (prefixWord ++ tailWord_177411).sum := by decide
  have hdescent : baseEnd_177411 < baseStart_177411 := by decide
  rcases family_descends (prefixWord ++ tailWord_177411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177432 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_177432 : Nat := 118140960795 + 177432 * 2 ^ 59
def prefixEnd_177432 : Nat := 4983230072969 + 3 ^ 40 * 177432 * 2
def baseEnd_177432 : Nat := 80984799545471137941343

theorem tailTrace_177432 : CollatzResearch.WordTrace tailWord_177432 prefixEnd_177432 80984799545471137941343 := by
  unfold tailWord_177432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235738346600820909083275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4314317795467761212111033 3235738346600820909083275)
  ·
    refine ⟨4853607519901231363624913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3235738346600820909083275 4853607519901231363624913)
    ·
      refine ⟨3640205639925923522718685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4853607519901231363624913 3640205639925923522718685)
      ·
        refine ⟨1365077114972221321019507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3640205639925923522718685 1365077114972221321019507)
        ·
          refine ⟨2047615672458331981529261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365077114972221321019507 2047615672458331981529261)
          ·
            refine ⟨767855877171874493073473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2047615672458331981529261 767855877171874493073473)
            ·
              refine ⟨575891907878905869805105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767855877171874493073473 575891907878905869805105)
              ·
                refine ⟨431918930909179402353829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575891907878905869805105 431918930909179402353829)
                ·
                  refine ⟨80984799545471137941343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431918930909179402353829 80984799545471137941343)
                  ·
                    rfl

theorem cell20_177432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_177432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177432 prefixEnd_177432 := by exact prefixLift 177432
  have htrace : WordTrace (prefixWord ++ tailWord_177432) baseStart_177432 baseEnd_177432 := by
    simpa [prefixWord, tailWord_177432, baseEnd_177432] using wordTrace_append hprefix tailTrace_177432
  have hstable : (prefixWord ++ tailWord_177432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177432).length < 2 ^ (prefixWord ++ tailWord_177432).sum := by decide
  have hdescent : baseEnd_177432 < baseStart_177432 := by decide
  rcases family_descends (prefixWord ++ tailWord_177432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177462 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_177462 : Nat := 118140960795 + 177462 * 2 ^ 59
def prefixEnd_177462 : Nat := 4983230072969 + 3 ^ 40 * 177462 * 2
def baseEnd_177462 : Nat := 80998492362924366941221

theorem tailTrace_177462 : CollatzResearch.WordTrace tailWord_177462 prefixEnd_177462 80998492362924366941221 := by
  unfold tailWord_177462
  simp only [CollatzResearch.WordTrace]
  refine ⟨404535680193309808859915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4315047255395304627839093 404535680193309808859915)
  ·
    refine ⟨606803520289964713289873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 404535680193309808859915 606803520289964713289873)
    ·
      refine ⟨455102640217473534967405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 606803520289964713289873 455102640217473534967405)
      ·
        refine ⟨170663490081552575612777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455102640217473534967405 170663490081552575612777)
        ·
          refine ⟨127997617561164431709583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170663490081552575612777 127997617561164431709583)
          ·
            refine ⟨191996426341746647564375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127997617561164431709583 191996426341746647564375)
            ·
              refine ⟨287994639512619971346563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191996426341746647564375 287994639512619971346563)
              ·
                refine ⟨431991959268929957019845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287994639512619971346563 431991959268929957019845)
                ·
                  refine ⟨80998492362924366941221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431991959268929957019845 80998492362924366941221)
                  ·
                    rfl

theorem cell20_177462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_177462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177462 prefixEnd_177462 := by exact prefixLift 177462
  have htrace : WordTrace (prefixWord ++ tailWord_177462) baseStart_177462 baseEnd_177462 := by
    simpa [prefixWord, tailWord_177462, baseEnd_177462] using wordTrace_append hprefix tailTrace_177462
  have hstable : (prefixWord ++ tailWord_177462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177462).length < 2 ^ (prefixWord ++ tailWord_177462).sum := by decide
  have hdescent : baseEnd_177462 < baseStart_177462 := by decide
  rcases family_descends (prefixWord ++ tailWord_177462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177466 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_177466 : Nat := 118140960795 + 177466 * 2 ^ 59
def prefixEnd_177466 : Nat := 4983230072969 + 3 ^ 40 * 177466 * 2
def baseEnd_177466 : Nat := 81000318071918130807871

theorem tailTrace_177466 : CollatzResearch.WordTrace tailWord_177466 prefixEnd_177466 81000318071918130807871 := by
  unfold tailWord_177466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618179193769616406226063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4315144516718977083269501 1618179193769616406226063)
  ·
    refine ⟨2427268790654424609339095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1618179193769616406226063 2427268790654424609339095)
    ·
      refine ⟨3640903185981636914008643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427268790654424609339095 3640903185981636914008643)
      ·
        refine ⟨5461354778972455371012965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640903185981636914008643 5461354778972455371012965)
        ·
          refine ⟨1024004021057335382064931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5461354778972455371012965 1024004021057335382064931)
          ·
            refine ⟨1536006031586003073097397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024004021057335382064931 1536006031586003073097397)
            ·
              refine ⟨144000565461187788102881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1536006031586003073097397 144000565461187788102881)
              ·
                refine ⟨108000424095890841077161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144000565461187788102881 108000424095890841077161)
                ·
                  refine ⟨81000318071918130807871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108000424095890841077161 81000318071918130807871)
                  ·
                    rfl

theorem cell20_177466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_177466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177466 prefixEnd_177466 := by exact prefixLift 177466
  have htrace : WordTrace (prefixWord ++ tailWord_177466) baseStart_177466 baseEnd_177466 := by
    simpa [prefixWord, tailWord_177466, baseEnd_177466] using wordTrace_append hprefix tailTrace_177466
  have hstable : (prefixWord ++ tailWord_177466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177466).length < 2 ^ (prefixWord ++ tailWord_177466).sum := by decide
  have hdescent : baseEnd_177466 < baseStart_177466 := by decide
  rcases family_descends (prefixWord ++ tailWord_177466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177476 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_177476 : Nat := 118140960795 + 177476 * 2 ^ 59
def prefixEnd_177476 : Nat := 4983230072969 + 3 ^ 40 * 177476 * 2
def baseEnd_177476 : Nat := 81004882344402540474497

theorem tailTrace_177476 : CollatzResearch.WordTrace tailWord_177476 prefixEnd_177476 81004882344402540474497 := by
  unfold tailWord_177476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236540752521118666384141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4315387670028158221845521 3236540752521118666384141)
  ·
    refine ⟨1213702782195419499894053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3236540752521118666384141 1213702782195419499894053)
    ·
      refine ⟨227569271661641156230135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1213702782195419499894053 227569271661641156230135)
      ·
        refine ⟨341353907492461734345203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227569271661641156230135 341353907492461734345203)
        ·
          refine ⟨512030861238692601517805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341353907492461734345203 512030861238692601517805)
          ·
            refine ⟨192011572964509725569177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512030861238692601517805 192011572964509725569177)
            ·
              refine ⟨144008679723382294176883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192011572964509725569177 144008679723382294176883)
              ·
                refine ⟨216013019585073441265325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144008679723382294176883 216013019585073441265325)
                ·
                  refine ⟨81004882344402540474497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216013019585073441265325 81004882344402540474497)
                  ·
                    rfl

theorem cell20_177476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_177476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177476 prefixEnd_177476 := by exact prefixLift 177476
  have htrace : WordTrace (prefixWord ++ tailWord_177476) baseStart_177476 baseEnd_177476 := by
    simpa [prefixWord, tailWord_177476, baseEnd_177476] using wordTrace_append hprefix tailTrace_177476
  have hstable : (prefixWord ++ tailWord_177476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177476).length < 2 ^ (prefixWord ++ tailWord_177476).sum := by decide
  have hdescent : baseEnd_177476 < baseStart_177476 := by decide
  rcases family_descends (prefixWord ++ tailWord_177476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177491 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_177491 : Nat := 118140960795 + 177491 * 2 ^ 59
def prefixEnd_177491 : Nat := 4983230072969 + 3 ^ 40 * 177491 * 2
def baseEnd_177491 : Nat := 81011728753129154974435

theorem tailTrace_177491 : CollatzResearch.WordTrace tailWord_177491 prefixEnd_177491 81011728753129154974435 := by
  unfold tailWord_177491
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473628599987894894564327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4315752399991929929709551 6473628599987894894564327)
  ·
    refine ⟨9710442899981842341846491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6473628599987894894564327 9710442899981842341846491)
    ·
      refine ⟨14565664349972763512769737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9710442899981842341846491 14565664349972763512769737)
      ·
        refine ⟨10924248262479572634577303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14565664349972763512769737 10924248262479572634577303)
        ·
          refine ⟨16386372393719358951865955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10924248262479572634577303 16386372393719358951865955)
          ·
            refine ⟨24579558590579038427798933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16386372393719358951865955 24579558590579038427798933)
            ·
              refine ⟨1152166808933392426303075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24579558590579038427798933 1152166808933392426303075)
              ·
                refine ⟨1728250213400088639454613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152166808933392426303075 1728250213400088639454613)
                ·
                  refine ⟨81011728753129154974435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1728250213400088639454613 81011728753129154974435)
                  ·
                    rfl

theorem cell20_177491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_177491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177491 prefixEnd_177491 := by exact prefixLift 177491
  have htrace : WordTrace (prefixWord ++ tailWord_177491) baseStart_177491 baseEnd_177491 := by
    simpa [prefixWord, tailWord_177491, baseEnd_177491] using wordTrace_append hprefix tailTrace_177491
  have hstable : (prefixWord ++ tailWord_177491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177491).length < 2 ^ (prefixWord ++ tailWord_177491).sum := by decide
  have hdescent : baseEnd_177491 < baseStart_177491 := by decide
  rcases family_descends (prefixWord ++ tailWord_177491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177539 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_177539 : Nat := 118140960795 + 177539 * 2 ^ 59
def prefixEnd_177539 : Nat := 4983230072969 + 3 ^ 40 * 177539 * 2
def baseEnd_177539 : Nat := 81033637261054321374239

theorem tailTrace_177539 : CollatzResearch.WordTrace tailWord_177539 prefixEnd_177539 81033637261054321374239 := by
  unfold tailWord_177539
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475379303813999092311671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4316919535875999394874447 6475379303813999092311671)
  ·
    refine ⟨9713068955720998638467507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475379303813999092311671 9713068955720998638467507)
    ·
      refine ⟨14569603433581497957701261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713068955720998638467507 14569603433581497957701261)
      ·
        refine ⟨5463601287593061734137973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14569603433581497957701261 5463601287593061734137973)
        ·
          refine ⟨512212620711849537575435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5463601287593061734137973 512212620711849537575435)
          ·
            refine ⟨768318931067774306363153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512212620711849537575435 768318931067774306363153)
            ·
              refine ⟨576239198300830729772365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768318931067774306363153 576239198300830729772365)
              ·
                refine ⟨216089699362811523664637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 576239198300830729772365 216089699362811523664637)
                ·
                  refine ⟨81033637261054321374239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216089699362811523664637 81033637261054321374239)
                  ·
                    rfl

theorem cell20_177539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_177539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177539 prefixEnd_177539 := by exact prefixLift 177539
  have htrace : WordTrace (prefixWord ++ tailWord_177539) baseStart_177539 baseEnd_177539 := by
    simpa [prefixWord, tailWord_177539, baseEnd_177539] using wordTrace_append hprefix tailTrace_177539
  have hstable : (prefixWord ++ tailWord_177539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177539).length < 2 ^ (prefixWord ++ tailWord_177539).sum := by decide
  have hdescent : baseEnd_177539 < baseStart_177539 := by decide
  rcases family_descends (prefixWord ++ tailWord_177539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177629 : List Nat := [1, 4, 3, 1, 1, 2, 8]
def baseStart_177629 : Nat := 118140960795 + 177629 * 2 ^ 59
def prefixEnd_177629 : Nat := 4983230072969 + 3 ^ 40 * 177629 * 2
def baseEnd_177629 : Nat := 9008301745934889819319

theorem tailTrace_177629 : CollatzResearch.WordTrace tailWord_177629 prefixEnd_177629 9008301745934889819319 := by
  unfold tailWord_177629
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478661873487944463087941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319107915658629642058627 6478661873487944463087941)
  ·
    refine ⟨1214749101278989586828989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6478661873487944463087941 1214749101278989586828989)
    ·
      refine ⟨455530912979621095060871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1214749101278989586828989 455530912979621095060871)
      ·
        refine ⟨683296369469431642591307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455530912979621095060871 683296369469431642591307)
        ·
          refine ⟨1024944554204147463886961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683296369469431642591307 1024944554204147463886961)
          ·
            refine ⟨768708415653110597915221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024944554204147463886961 768708415653110597915221)
            ·
              refine ⟨9008301745934889819319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 768708415653110597915221 9008301745934889819319)
              ·
                rfl

theorem cell20_177629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_177629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177629 prefixEnd_177629 := by exact prefixLift 177629
  have htrace : WordTrace (prefixWord ++ tailWord_177629) baseStart_177629 baseEnd_177629 := by
    simpa [prefixWord, tailWord_177629, baseEnd_177629] using wordTrace_append hprefix tailTrace_177629
  have hstable : (prefixWord ++ tailWord_177629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177629).length < 2 ^ (prefixWord ++ tailWord_177629).sum := by decide
  have hdescent : baseEnd_177629 < baseStart_177629 := by decide
  rcases family_descends (prefixWord ++ tailWord_177629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177639 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_177639 : Nat := 118140960795 + 177639 * 2 ^ 59
def prefixEnd_177639 : Nat := 4983230072969 + 3 ^ 40 * 177639 * 2
def baseEnd_177639 : Nat := 81079279985898418040497

theorem tailTrace_177639 : CollatzResearch.WordTrace tailWord_177639 prefixEnd_177639 81079279985898418040497 := by
  unfold tailWord_177639
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479026603451716170951971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319351068967810780634647 6479026603451716170951971)
  ·
    refine ⟨9718539905177574256427957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479026603451716170951971 9718539905177574256427957)
    ·
      refine ⟨911113116110397586540121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9718539905177574256427957 911113116110397586540121)
      ·
        refine ⟨683334837082798189905091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911113116110397586540121 683334837082798189905091)
        ·
          refine ⟨1025002255624197284857637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683334837082798189905091 1025002255624197284857637)
          ·
            refine ⟨192187922929536990910807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1025002255624197284857637 192187922929536990910807)
            ·
              refine ⟨288281884394305486366211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192187922929536990910807 288281884394305486366211)
              ·
                refine ⟨432422826591458229549317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288281884394305486366211 432422826591458229549317)
                ·
                  refine ⟨81079279985898418040497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432422826591458229549317 81079279985898418040497)
                  ·
                    rfl

theorem cell20_177639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_177639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177639 prefixEnd_177639 := by exact prefixLift 177639
  have htrace : WordTrace (prefixWord ++ tailWord_177639) baseStart_177639 baseEnd_177639 := by
    simpa [prefixWord, tailWord_177639, baseEnd_177639] using wordTrace_append hprefix tailTrace_177639
  have hstable : (prefixWord ++ tailWord_177639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177639).length < 2 ^ (prefixWord ++ tailWord_177639).sum := by decide
  have hdescent : baseEnd_177639 < baseStart_177639 := by decide
  rcases family_descends (prefixWord ++ tailWord_177639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177643 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_177643 : Nat := 118140960795 + 177643 * 2 ^ 59
def prefixEnd_177643 : Nat := 4983230072969 + 3 ^ 40 * 177643 * 2
def baseEnd_177643 : Nat := 81081105694892181907147

theorem tailTrace_177643 : CollatzResearch.WordTrace tailWord_177643 prefixEnd_177643 81081105694892181907147 := by
  unfold tailWord_177643
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479172495437224854097583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319448330291483236065055 6479172495437224854097583)
  ·
    refine ⟨9718758743155837281146375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479172495437224854097583 9718758743155837281146375)
    ·
      refine ⟨14578138114733755921719563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718758743155837281146375 14578138114733755921719563)
      ·
        refine ⟨21867207172100633882579345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14578138114733755921719563 21867207172100633882579345)
        ·
          refine ⟨16400405379075475411934509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21867207172100633882579345 16400405379075475411934509)
          ·
            refine ⟨6150152017153303279475441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16400405379075475411934509 6150152017153303279475441)
            ·
              refine ⟨4612614012864977459606581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6150152017153303279475441 4612614012864977459606581)
              ·
                refine ⟨432432563706091636838117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4612614012864977459606581 432432563706091636838117)
                ·
                  refine ⟨81081105694892181907147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432432563706091636838117 81081105694892181907147)
                  ·
                    rfl

theorem cell20_177643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_177643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177643 prefixEnd_177643 := by exact prefixLift 177643
  have htrace : WordTrace (prefixWord ++ tailWord_177643) baseStart_177643 baseEnd_177643 := by
    simpa [prefixWord, tailWord_177643, baseEnd_177643] using wordTrace_append hprefix tailTrace_177643
  have hstable : (prefixWord ++ tailWord_177643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177643).length < 2 ^ (prefixWord ++ tailWord_177643).sum := by decide
  have hdescent : baseEnd_177643 < baseStart_177643 := by decide
  rcases family_descends (prefixWord ++ tailWord_177643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177684 : List Nat := [2, 4, 3, 1, 2, 8]
def baseStart_177684 : Nat := 118140960795 + 177684 * 2 ^ 59
def prefixEnd_177684 : Nat := 4983230072969 + 3 ^ 40 * 177684 * 2
def baseEnd_177684 : Nat := 3003697007854750427419

theorem tailTrace_177684 : CollatzResearch.WordTrace tailWord_177684 prefixEnd_177684 3003697007854750427419 := by
  unfold tailWord_177684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240333944144344428170053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4320445258859125904226737 3240333944144344428170053)
  ·
    refine ⟨607562614527064580281885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3240333944144344428170053 607562614527064580281885)
    ·
      refine ⟨227835980447649217605707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 607562614527064580281885 227835980447649217605707)
      ·
        refine ⟨341753970671473826408561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227835980447649217605707 341753970671473826408561)
        ·
          refine ⟨256315478003605369806421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341753970671473826408561 256315478003605369806421)
          ·
            refine ⟨3003697007854750427419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 256315478003605369806421 3003697007854750427419)
            ·
              rfl

theorem cell20_177684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 8].length) (baseStart_177684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177684 prefixEnd_177684 := by exact prefixLift 177684
  have htrace : WordTrace (prefixWord ++ tailWord_177684) baseStart_177684 baseEnd_177684 := by
    simpa [prefixWord, tailWord_177684, baseEnd_177684] using wordTrace_append hprefix tailTrace_177684
  have hstable : (prefixWord ++ tailWord_177684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177684).length < 2 ^ (prefixWord ++ tailWord_177684).sum := by decide
  have hdescent : baseEnd_177684 < baseStart_177684 := by decide
  rcases family_descends (prefixWord ++ tailWord_177684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177688 : List Nat := [2, 1, 2, 3, 12]
def baseStart_177688 : Nat := 118140960795 + 177688 * 2 ^ 59
def prefixEnd_177688 : Nat := 4983230072969 + 3 ^ 40 * 177688 * 2
def baseEnd_177688 : Nat := 1001254875568790437123

theorem tailTrace_177688 : CollatzResearch.WordTrace tailWord_177688 prefixEnd_177688 1001254875568790437123 := by
  unfold tailWord_177688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240406890137098769742859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4320542520182798359657145 3240406890137098769742859)
  ·
    refine ⟨4860610335205648154614289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3240406890137098769742859 4860610335205648154614289)
    ·
      refine ⟨3645457751404236115960717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4860610335205648154614289 3645457751404236115960717)
      ·
        refine ⟨1367046656776588543485269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3645457751404236115960717 1367046656776588543485269)
        ·
          refine ⟨1001254875568790437123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1367046656776588543485269 1001254875568790437123)
          ·
            rfl

theorem cell20_177688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 12].length) (baseStart_177688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177688 prefixEnd_177688 := by exact prefixLift 177688
  have htrace : WordTrace (prefixWord ++ tailWord_177688) baseStart_177688 baseEnd_177688 := by
    simpa [prefixWord, tailWord_177688, baseEnd_177688] using wordTrace_append hprefix tailTrace_177688
  have hstable : (prefixWord ++ tailWord_177688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177688).length < 2 ^ (prefixWord ++ tailWord_177688).sum := by decide
  have hdescent : baseEnd_177688 < baseStart_177688 := by decide
  rcases family_descends (prefixWord ++ tailWord_177688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177719 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_177719 : Nat := 118140960795 + 177719 * 2 ^ 59
def prefixEnd_177719 : Nat := 4983230072969 + 3 ^ 40 * 177719 * 2
def baseEnd_177719 : Nat := 81115794165773695373503

theorem tailTrace_177719 : CollatzResearch.WordTrace tailWord_177719 prefixEnd_177719 81115794165773695373503 := by
  unfold tailWord_177719
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481944443161889833864211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4321296295441259889242807 6481944443161889833864211)
  ·
    refine ⟨9722916664742834750796317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6481944443161889833864211 9722916664742834750796317)
    ·
      refine ⟨3646093749278563031548619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9722916664742834750796317 3646093749278563031548619)
      ·
        refine ⟨5469140623917844547322929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646093749278563031548619 5469140623917844547322929)
        ·
          refine ⟨4101855467938383410492197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5469140623917844547322929 4101855467938383410492197)
          ·
            refine ⟨769097900238446889467287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4101855467938383410492197 769097900238446889467287)
            ·
              refine ⟨1153646850357670334200931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769097900238446889467287 1153646850357670334200931)
              ·
                refine ⟨1730470275536505501301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153646850357670334200931 1730470275536505501301397)
                ·
                  refine ⟨81115794165773695373503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1730470275536505501301397 81115794165773695373503)
                  ·
                    rfl

theorem cell20_177719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_177719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177719 prefixEnd_177719 := by exact prefixLift 177719
  have htrace : WordTrace (prefixWord ++ tailWord_177719) baseStart_177719 baseEnd_177719 := by
    simpa [prefixWord, tailWord_177719, baseEnd_177719] using wordTrace_append hprefix tailTrace_177719
  have hstable : (prefixWord ++ tailWord_177719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177719).length < 2 ^ (prefixWord ++ tailWord_177719).sum := by decide
  have hdescent : baseEnd_177719 < baseStart_177719 := by decide
  rcases family_descends (prefixWord ++ tailWord_177719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177746 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_177746 : Nat := 118140960795 + 177746 * 2 ^ 59
def prefixEnd_177746 : Nat := 4983230072969 + 3 ^ 40 * 177746 * 2
def baseEnd_177746 : Nat := 81128117701481601473393

theorem tailTrace_177746 : CollatzResearch.WordTrace tailWord_177746 prefixEnd_177746 81128117701481601473393 := by
  unfold tailWord_177746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620732303516018361274273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4321952809376048963398061 1620732303516018361274273)
  ·
    refine ⟨1215549227637013770955705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1620732303516018361274273 1215549227637013770955705)
    ·
      refine ⟨911661920727760328216779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1215549227637013770955705 911661920727760328216779)
      ·
        refine ⟨1367492881091640492325169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911661920727760328216779 1367492881091640492325169)
        ·
          refine ⟨1025619660818730369243877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1367492881091640492325169 1025619660818730369243877)
          ·
            refine ⟨192303686403511944233227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1025619660818730369243877 192303686403511944233227)
            ·
              refine ⟨288455529605267916349841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192303686403511944233227 288455529605267916349841)
              ·
                refine ⟨216341647203950937262381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288455529605267916349841 216341647203950937262381)
                ·
                  refine ⟨81128117701481601473393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216341647203950937262381 81128117701481601473393)
                  ·
                    rfl

theorem cell20_177746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_177746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177746 prefixEnd_177746 := by exact prefixLift 177746
  have htrace : WordTrace (prefixWord ++ tailWord_177746) baseStart_177746 baseEnd_177746 := by
    simpa [prefixWord, tailWord_177746, baseEnd_177746] using wordTrace_append hprefix tailTrace_177746
  have hstable : (prefixWord ++ tailWord_177746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177746).length < 2 ^ (prefixWord ++ tailWord_177746).sum := by decide
  have hdescent : baseEnd_177746 < baseStart_177746 := by decide
  rcases family_descends (prefixWord ++ tailWord_177746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177822 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_177822 : Nat := 118140960795 + 177822 * 2 ^ 59
def prefixEnd_177822 : Nat := 4983230072969 + 3 ^ 40 * 177822 * 2
def baseEnd_177822 : Nat := 81162806172363114939749

theorem tailTrace_177822 : CollatzResearch.WordTrace tailWord_177822 prefixEnd_177822 81162806172363114939749 := by
  unfold tailWord_177822
  simp only [CollatzResearch.WordTrace]
  refine ⟨810712645223592303107965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4323800774525825616575813 810712645223592303107965)
  ·
    refine ⟨304017241958847113665487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 810712645223592303107965 304017241958847113665487)
    ·
      refine ⟨456025862938270670498231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304017241958847113665487 456025862938270670498231)
      ·
        refine ⟨684038794407406005747347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456025862938270670498231 684038794407406005747347)
        ·
          refine ⟨1026058191611109008621021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684038794407406005747347 1026058191611109008621021)
          ·
            refine ⟨384771821854165878232883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1026058191611109008621021 384771821854165878232883)
            ·
              refine ⟨577157732781248817349325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384771821854165878232883 577157732781248817349325)
              ·
                refine ⟨216434149792968306505997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577157732781248817349325 216434149792968306505997)
                ·
                  refine ⟨81162806172363114939749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216434149792968306505997 81162806172363114939749)
                  ·
                    rfl

theorem cell20_177822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_177822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177822 prefixEnd_177822 := by exact prefixLift 177822
  have htrace : WordTrace (prefixWord ++ tailWord_177822) baseStart_177822 baseEnd_177822 := by
    simpa [prefixWord, tailWord_177822, baseEnd_177822] using wordTrace_append hprefix tailTrace_177822
  have hstable : (prefixWord ++ tailWord_177822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177822).length < 2 ^ (prefixWord ++ tailWord_177822).sum := by decide
  have hdescent : baseEnd_177822 < baseStart_177822 := by decide
  rcases family_descends (prefixWord ++ tailWord_177822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177840 : List Nat := [2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_177840 : Nat := 118140960795 + 177840 * 2 ^ 59
def prefixEnd_177840 : Nat := 4983230072969 + 3 ^ 40 * 177840 * 2
def baseEnd_177840 : Nat := 27057007287611684113225

theorem tailTrace_177840 : CollatzResearch.WordTrace tailWord_177840 prefixEnd_177840 27057007287611684113225 := by
  unfold tailWord_177840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243178837861763749509487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4324238450482351666012649 3243178837861763749509487)
  ·
    refine ⟨4864768256792645624264231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243178837861763749509487 4864768256792645624264231)
    ·
      refine ⟨7297152385188968436396347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4864768256792645624264231 7297152385188968436396347)
      ·
        refine ⟨10945728577783452654594521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297152385188968436396347 10945728577783452654594521)
        ·
          refine ⟨8209296433337589490945891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10945728577783452654594521 8209296433337589490945891)
          ·
            refine ⟨12313944650006384236418837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209296433337589490945891 12313944650006384236418837)
            ·
              refine ⟨577216155469049261082133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12313944650006384236418837 577216155469049261082133)
              ·
                refine ⟨27057007287611684113225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 577216155469049261082133 27057007287611684113225)
                ·
                  rfl

theorem cell20_177840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_177840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177840 prefixEnd_177840 := by exact prefixLift 177840
  have htrace : WordTrace (prefixWord ++ tailWord_177840) baseStart_177840 baseEnd_177840 := by
    simpa [prefixWord, tailWord_177840, baseEnd_177840] using wordTrace_append hprefix tailTrace_177840
  have hstable : (prefixWord ++ tailWord_177840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177840).length < 2 ^ (prefixWord ++ tailWord_177840).sum := by decide
  have hdescent : baseEnd_177840 < baseStart_177840 := by decide
  rcases family_descends (prefixWord ++ tailWord_177840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177874 : List Nat := [3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_177874 : Nat := 118140960795 + 177874 * 2 ^ 59
def prefixEnd_177874 : Nat := 4983230072969 + 3 ^ 40 * 177874 * 2
def baseEnd_177874 : Nat := 27062180129760681735401

theorem tailTrace_177874 : CollatzResearch.WordTrace tailWord_177874 prefixEnd_177874 27062180129760681735401 := by
  unfold tailWord_177874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621899439400087826439169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4325065171733567537171117 1621899439400087826439169)
  ·
    refine ⟨1216424579550065869829377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1621899439400087826439169 1216424579550065869829377)
    ·
      refine ⟨912318434662549402372033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216424579550065869829377 912318434662549402372033)
      ·
        refine ⟨684238825996912051779025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912318434662549402372033 684238825996912051779025)
        ·
          refine ⟨513179119497684038834269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684238825996912051779025 513179119497684038834269)
          ·
            refine ⟨192442169811631514562851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513179119497684038834269 192442169811631514562851)
            ·
              refine ⟨288663254717447271844277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192442169811631514562851 288663254717447271844277)
              ·
                refine ⟨27062180129760681735401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288663254717447271844277 27062180129760681735401)
                ·
                  rfl

theorem cell20_177874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_177874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177874 prefixEnd_177874 := by exact prefixLift 177874
  have htrace : WordTrace (prefixWord ++ tailWord_177874) baseStart_177874 baseEnd_177874 := by
    simpa [prefixWord, tailWord_177874, baseEnd_177874] using wordTrace_append hprefix tailTrace_177874
  have hstable : (prefixWord ++ tailWord_177874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177874).length < 2 ^ (prefixWord ++ tailWord_177874).sum := by decide
  have hdescent : baseEnd_177874 < baseStart_177874 := by decide
  rcases family_descends (prefixWord ++ tailWord_177874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177902 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_177902 : Nat := 118140960795 + 177902 * 2 ^ 59
def prefixEnd_177902 : Nat := 4983230072969 + 3 ^ 40 * 177902 * 2
def baseEnd_177902 : Nat := 81199320352238392272755

theorem tailTrace_177902 : CollatzResearch.WordTrace tailWord_177902 prefixEnd_177902 81199320352238392272755 := by
  unfold tailWord_177902
  simp only [CollatzResearch.WordTrace]
  refine ⟨811077375187364010971995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4325746000999274725183973 811077375187364010971995)
  ·
    refine ⟨1216616062781046016457993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811077375187364010971995 1216616062781046016457993)
    ·
      refine ⟨912462047085784512343495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216616062781046016457993 912462047085784512343495)
      ·
        refine ⟨1368693070628676768515243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912462047085784512343495 1368693070628676768515243)
        ·
          refine ⟨2053039605943015152772865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368693070628676768515243 2053039605943015152772865)
          ·
            refine ⟨1539779704457261364579649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053039605943015152772865 1539779704457261364579649)
            ·
              refine ⟨1154834778342946023434737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539779704457261364579649 1154834778342946023434737)
              ·
                refine ⟨866126083757209517576053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154834778342946023434737 866126083757209517576053)
                ·
                  refine ⟨81199320352238392272755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866126083757209517576053 81199320352238392272755)
                  ·
                    rfl

theorem cell20_177902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_177902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177902 prefixEnd_177902 := by exact prefixLift 177902
  have htrace : WordTrace (prefixWord ++ tailWord_177902) baseStart_177902 baseEnd_177902 := by
    simpa [prefixWord, tailWord_177902, baseEnd_177902] using wordTrace_append hprefix tailTrace_177902
  have hstable : (prefixWord ++ tailWord_177902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177902).length < 2 ^ (prefixWord ++ tailWord_177902).sum := by decide
  have hdescent : baseEnd_177902 < baseStart_177902 := by decide
  rcases family_descends (prefixWord ++ tailWord_177902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177905 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 2]
def baseStart_177905 : Nat := 118140960795 + 177905 * 2 ^ 59
def prefixEnd_177905 : Nat := 4983230072969 + 3 ^ 40 * 177905 * 2
def baseEnd_177905 : Nat := 81200689633983715172743

theorem tailTrace_177905 : CollatzResearch.WordTrace tailWord_177905 prefixEnd_177905 81200689633983715172743 := by
  unfold tailWord_177905
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488728420488043600135169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4325818946992029066756779 6488728420488043600135169)
  ·
    refine ⟨4866546315366032700101377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6488728420488043600135169 4866546315366032700101377)
    ·
      refine ⟨3649909736524524525076033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4866546315366032700101377 3649909736524524525076033)
      ·
        refine ⟨2737432302393393393807025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3649909736524524525076033 2737432302393393393807025)
        ·
          refine ⟨2053074226795045045355269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2737432302393393393807025 2053074226795045045355269)
          ·
            refine ⟨384951417524070946004113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2053074226795045045355269 384951417524070946004113)
            ·
              refine ⟨288713563143053209503085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384951417524070946004113 288713563143053209503085)
              ·
                refine ⟨108267586178644953563657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288713563143053209503085 108267586178644953563657)
                ·
                  refine ⟨81200689633983715172743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108267586178644953563657 81200689633983715172743)
                  ·
                    rfl

theorem cell20_177905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_177905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177905 prefixEnd_177905 := by exact prefixLift 177905
  have htrace : WordTrace (prefixWord ++ tailWord_177905) baseStart_177905 baseEnd_177905 := by
    simpa [prefixWord, tailWord_177905, baseEnd_177905] using wordTrace_append hprefix tailTrace_177905
  have hstable : (prefixWord ++ tailWord_177905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177905).length < 2 ^ (prefixWord ++ tailWord_177905).sum := by decide
  have hdescent : baseEnd_177905 < baseStart_177905 := by decide
  rcases family_descends (prefixWord ++ tailWord_177905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177916 : List Nat := [2, 2, 2, 1, 3, 1, 9]
def baseStart_177916 : Nat := 118140960795 + 177916 * 2 ^ 59
def prefixEnd_177916 : Nat := 4983230072969 + 3 ^ 40 * 177916 * 2
def baseEnd_177916 : Nat := 9022856703746285089559

theorem tailTrace_177916 : CollatzResearch.WordTrace tailWord_177916 prefixEnd_177916 9022856703746285089559 := by
  unfold tailWord_177916
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244564811724096239392801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4326086415632128319190401 3244564811724096239392801)
  ·
    refine ⟨2433423608793072179544601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3244564811724096239392801 2433423608793072179544601)
    ·
      refine ⟨1825067706594804134658451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2433423608793072179544601 1825067706594804134658451)
      ·
        refine ⟨2737601559892206201987677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825067706594804134658451 2737601559892206201987677)
        ·
          refine ⟨1026600584959577325745379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2737601559892206201987677 1026600584959577325745379)
          ·
            refine ⟨1539900877439365988618069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026600584959577325745379 1539900877439365988618069)
            ·
              refine ⟨9022856703746285089559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1539900877439365988618069 9022856703746285089559)
              ·
                rfl

theorem cell20_177916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_177916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177916 prefixEnd_177916 := by exact prefixLift 177916
  have htrace : WordTrace (prefixWord ++ tailWord_177916) baseStart_177916 baseEnd_177916 := by
    simpa [prefixWord, tailWord_177916, baseEnd_177916] using wordTrace_append hprefix tailTrace_177916
  have hstable : (prefixWord ++ tailWord_177916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177916).length < 2 ^ (prefixWord ++ tailWord_177916).sum := by decide
  have hdescent : baseEnd_177916 < baseStart_177916 := by decide
  rcases family_descends (prefixWord ++ tailWord_177916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177960 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_177960 : Nat := 118140960795 + 177960 * 2 ^ 59
def prefixEnd_177960 : Nat := 4983230072969 + 3 ^ 40 * 177960 * 2
def baseEnd_177960 : Nat := 81225793132647968339185

theorem tailTrace_177960 : CollatzResearch.WordTrace tailWord_177960 prefixEnd_177960 81225793132647968339185 := by
  unfold tailWord_177960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245367217644393996693667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4327156290192525328924889 3245367217644393996693667)
  ·
    refine ⟨4868050826466590995040501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245367217644393996693667 4868050826466590995040501)
    ·
      refine ⟨456379764981242905785047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4868050826466590995040501 456379764981242905785047)
      ·
        refine ⟨684569647471864358677571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456379764981242905785047 684569647471864358677571)
        ·
          refine ⟨1026854471207796538016357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684569647471864358677571 1026854471207796538016357)
          ·
            refine ⟨192535213351461850878067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1026854471207796538016357 192535213351461850878067)
            ·
              refine ⟨288802820027192776317101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192535213351461850878067 288802820027192776317101)
              ·
                refine ⟨108301057510197291118913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288802820027192776317101 108301057510197291118913)
                ·
                  refine ⟨81225793132647968339185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108301057510197291118913 81225793132647968339185)
                  ·
                    rfl

theorem cell20_177960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_177960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177960 prefixEnd_177960 := by exact prefixLift 177960
  have htrace : WordTrace (prefixWord ++ tailWord_177960) baseStart_177960 baseEnd_177960 := by
    simpa [prefixWord, tailWord_177960, baseEnd_177960] using wordTrace_append hprefix tailTrace_177960
  have hstable : (prefixWord ++ tailWord_177960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177960).length < 2 ^ (prefixWord ++ tailWord_177960).sum := by decide
  have hdescent : baseEnd_177960 < baseStart_177960 := by decide
  rcases family_descends (prefixWord ++ tailWord_177960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177971 : List Nat := [1, 1, 1, 2, 7, 2, 6]
def baseStart_177971 : Nat := 118140960795 + 177971 * 2 ^ 59
def prefixEnd_177971 : Nat := 4983230072969 + 3 ^ 40 * 177971 * 2
def baseEnd_177971 : Nat := 9025645981375646552497

theorem tailTrace_177971 : CollatzResearch.WordTrace tailWord_177971 prefixEnd_177971 9025645981375646552497 := by
  unfold tailWord_177971
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491135638248936872037767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4327423758832624581358511 6491135638248936872037767)
  ·
    refine ⟨9736703457373405308056651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491135638248936872037767 9736703457373405308056651)
    ·
      refine ⟨14605055186060107962084977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9736703457373405308056651 14605055186060107962084977)
      ·
        refine ⟨10953791389545080971563733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14605055186060107962084977 10953791389545080971563733)
        ·
          refine ⟨256729485692462835271025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10953791389545080971563733 256729485692462835271025)
          ·
            refine ⟨192547114269347126453269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256729485692462835271025 192547114269347126453269)
            ·
              refine ⟨9025645981375646552497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192547114269347126453269 9025645981375646552497)
              ·
                rfl

theorem cell20_177971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_177971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177971 prefixEnd_177971 := by exact prefixLift 177971
  have htrace : WordTrace (prefixWord ++ tailWord_177971) baseStart_177971 baseEnd_177971 := by
    simpa [prefixWord, tailWord_177971, baseEnd_177971] using wordTrace_append hprefix tailTrace_177971
  have hstable : (prefixWord ++ tailWord_177971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177971).length < 2 ^ (prefixWord ++ tailWord_177971).sum := by decide
  have hdescent : baseEnd_177971 < baseStart_177971 := by decide
  rcases family_descends (prefixWord ++ tailWord_177971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177977 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 2]
def baseStart_177977 : Nat := 118140960795 + 177977 * 2 ^ 59
def prefixEnd_177977 : Nat := 4983230072969 + 3 ^ 40 * 177977 * 2
def baseEnd_177977 : Nat := 81233552395871464772449

theorem tailTrace_177977 : CollatzResearch.WordTrace tailWord_177977 prefixEnd_177977 81233552395871464772449 := by
  unfold tailWord_177977
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491354476227199896756185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4327569650818133264504123 6491354476227199896756185)
  ·
    refine ⟨4868515857170399922567139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6491354476227199896756185 4868515857170399922567139)
    ·
      refine ⟨7302773785755599883850709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868515857170399922567139 7302773785755599883850709)
      ·
        refine ⟨171158760603646872277751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7302773785755599883850709 171158760603646872277751)
        ·
          refine ⟨256738140905470308416627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171158760603646872277751 256738140905470308416627)
          ·
            refine ⟨385107211358205462624941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256738140905470308416627 385107211358205462624941)
            ·
              refine ⟨144415204259327048484353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385107211358205462624941 144415204259327048484353)
              ·
                refine ⟨108311403194495286363265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144415204259327048484353 108311403194495286363265)
                ·
                  refine ⟨81233552395871464772449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108311403194495286363265 81233552395871464772449)
                  ·
                    rfl

theorem cell20_177977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_177977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177977 prefixEnd_177977 := by exact prefixLift 177977
  have htrace : WordTrace (prefixWord ++ tailWord_177977) baseStart_177977 baseEnd_177977 := by
    simpa [prefixWord, tailWord_177977, baseEnd_177977] using wordTrace_append hprefix tailTrace_177977
  have hstable : (prefixWord ++ tailWord_177977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177977).length < 2 ^ (prefixWord ++ tailWord_177977).sum := by decide
  have hdescent : baseEnd_177977 < baseStart_177977 := by decide
  rcases family_descends (prefixWord ++ tailWord_177977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177978 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_177978 : Nat := 118140960795 + 177978 * 2 ^ 59
def prefixEnd_177978 : Nat := 4983230072969 + 3 ^ 40 * 177978 * 2
def baseEnd_177978 : Nat := 81234008823119905739111

theorem tailTrace_177978 : CollatzResearch.WordTrace tailWord_177978 prefixEnd_177978 81234008823119905739111 := by
  unfold tailWord_177978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622847737305894266885647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4327593966149051378361725 1622847737305894266885647)
  ·
    refine ⟨2434271605958841400328471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622847737305894266885647 2434271605958841400328471)
    ·
      refine ⟨3651407408938262100492707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434271605958841400328471 3651407408938262100492707)
      ·
        refine ⟨5477111113407393150739061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651407408938262100492707 5477111113407393150739061)
        ·
          refine ⟨513479166881943107881787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5477111113407393150739061 513479166881943107881787)
          ·
            refine ⟨770218750322914661822681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513479166881943107881787 770218750322914661822681)
            ·
              refine ⟨577664062742185996367011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770218750322914661822681 577664062742185996367011)
              ·
                refine ⟨866496094113278994550517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577664062742185996367011 866496094113278994550517)
                ·
                  refine ⟨81234008823119905739111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866496094113278994550517 81234008823119905739111)
                  ·
                    rfl

theorem cell20_177978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_177978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177978 prefixEnd_177978 := by exact prefixLift 177978
  have htrace : WordTrace (prefixWord ++ tailWord_177978) baseStart_177978 baseEnd_177978 := by
    simpa [prefixWord, tailWord_177978, baseEnd_177978] using wordTrace_append hprefix tailTrace_177978
  have hstable : (prefixWord ++ tailWord_177978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177978).length < 2 ^ (prefixWord ++ tailWord_177978).sum := by decide
  have hdescent : baseEnd_177978 < baseStart_177978 := by decide
  rcases family_descends (prefixWord ++ tailWord_177978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177981 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_177981 : Nat := 118140960795 + 177981 * 2 ^ 59
def prefixEnd_177981 : Nat := 4983230072969 + 3 ^ 40 * 177981 * 2
def baseEnd_177981 : Nat := 81235378104865228639099

theorem tailTrace_177981 : CollatzResearch.WordTrace tailWord_177981 prefixEnd_177981 81235378104865228639099 := by
  unfold tailWord_177981
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491500368212708579901797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4327666912141805719934531 6491500368212708579901797)
  ·
    refine ⟨1217156319039882858731587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6491500368212708579901797 1217156319039882858731587)
    ·
      refine ⟨1825734478559824288097381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217156319039882858731587 1825734478559824288097381)
      ·
        refine ⟨342325214729967054018259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1825734478559824288097381 342325214729967054018259)
        ·
          refine ⟨513487822094950581027389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342325214729967054018259 513487822094950581027389)
          ·
            refine ⟨192557933285606467885271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513487822094950581027389 192557933285606467885271)
            ·
              refine ⟨288836899928409701827907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192557933285606467885271 288836899928409701827907)
              ·
                refine ⟨433255349892614552741861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288836899928409701827907 433255349892614552741861)
                ·
                  refine ⟨81235378104865228639099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433255349892614552741861 81235378104865228639099)
                  ·
                    rfl

theorem cell20_177981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_177981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177981 prefixEnd_177981 := by exact prefixLift 177981
  have htrace : WordTrace (prefixWord ++ tailWord_177981) baseStart_177981 baseEnd_177981 := by
    simpa [prefixWord, tailWord_177981, baseEnd_177981] using wordTrace_append hprefix tailTrace_177981
  have hstable : (prefixWord ++ tailWord_177981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177981).length < 2 ^ (prefixWord ++ tailWord_177981).sum := by decide
  have hdescent : baseEnd_177981 < baseStart_177981 := by decide
  rcases family_descends (prefixWord ++ tailWord_177981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177992 : List Nat := [2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_177992 : Nat := 118140960795 + 177992 * 2 ^ 59
def prefixEnd_177992 : Nat := 4983230072969 + 3 ^ 40 * 177992 * 2
def baseEnd_177992 : Nat := 27080132934866026424129

theorem tailTrace_177992 : CollatzResearch.WordTrace tailWord_177992 prefixEnd_177992 27080132934866026424129 := by
  unfold tailWord_177992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245950785586428729276115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4327934380781904972368153 3245950785586428729276115)
  ·
    refine ⟨4868926178379643093914173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245950785586428729276115 4868926178379643093914173)
    ·
      refine ⟨1825847316892366160217815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4868926178379643093914173 1825847316892366160217815)
      ·
        refine ⟨2738770975338549240326723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825847316892366160217815 2738770975338549240326723)
        ·
          refine ⟨4108156463007823860490085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738770975338549240326723 4108156463007823860490085)
          ·
            refine ⟨770279336813966973841891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4108156463007823860490085 770279336813966973841891)
            ·
              refine ⟨1155419005220950460762837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770279336813966973841891 1155419005220950460762837)
              ·
                refine ⟨27080132934866026424129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1155419005220950460762837 27080132934866026424129)
                ·
                  rfl

theorem cell20_177992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_177992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_177992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_177992 prefixEnd_177992 := by exact prefixLift 177992
  have htrace : WordTrace (prefixWord ++ tailWord_177992) baseStart_177992 baseEnd_177992 := by
    simpa [prefixWord, tailWord_177992, baseEnd_177992] using wordTrace_append hprefix tailTrace_177992
  have hstable : (prefixWord ++ tailWord_177992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177992).length < 2 ^ (prefixWord ++ tailWord_177992).sum := by decide
  have hdescent : baseEnd_177992 < baseStart_177992 := by decide
  rcases family_descends (prefixWord ++ tailWord_177992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178026 : List Nat := [3, 1, 3, 4, 2, 7]
def baseStart_178026 : Nat := 118140960795 + 178026 * 2 ^ 59
def prefixEnd_178026 : Nat := 4983230072969 + 3 ^ 40 * 178026 * 2
def baseEnd_178026 : Nat := 3009478419668336005145

theorem tailTrace_178026 : CollatzResearch.WordTrace tailWord_178026 prefixEnd_178026 3009478419668336005145 := by
  unfold tailWord_178026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623285413262420316322483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4328761102033120843526621 1623285413262420316322483)
  ·
    refine ⟨2434928119893630474483725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623285413262420316322483 2434928119893630474483725)
    ·
      refine ⟨913098044960111427931397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2434928119893630474483725 913098044960111427931397)
      ·
        refine ⟨171205883430020892737137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 913098044960111427931397 171205883430020892737137)
        ·
          refine ⟨128404412572515669552853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171205883430020892737137 128404412572515669552853)
          ·
            refine ⟨3009478419668336005145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128404412572515669552853 3009478419668336005145)
            ·
              rfl

theorem cell20_178026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 7].length) (baseStart_178026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178026 prefixEnd_178026 := by exact prefixLift 178026
  have htrace : WordTrace (prefixWord ++ tailWord_178026) baseStart_178026 baseEnd_178026 := by
    simpa [prefixWord, tailWord_178026, baseEnd_178026] using wordTrace_append hprefix tailTrace_178026
  have hstable : (prefixWord ++ tailWord_178026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178026).length < 2 ^ (prefixWord ++ tailWord_178026).sum := by decide
  have hdescent : baseEnd_178026 < baseStart_178026 := by decide
  rcases family_descends (prefixWord ++ tailWord_178026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178070 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_178070 : Nat := 118140960795 + 178070 * 2 ^ 59
def prefixEnd_178070 : Nat := 4983230072969 + 3 ^ 40 * 178070 * 2
def baseEnd_178070 : Nat := 81276000129976474672069

theorem tailTrace_178070 : CollatzResearch.WordTrace tailWord_178070 prefixEnd_178070 81276000129976474672069 := by
  unfold tailWord_178070
  simp only [CollatzResearch.WordTrace]
  refine ⟨405921654055642298743229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4329830976593517853261109 405921654055642298743229)
  ·
    refine ⟨152220620270865862028711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 405921654055642298743229 152220620270865862028711)
    ·
      refine ⟨228330930406298793043067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152220620270865862028711 228330930406298793043067)
      ·
        refine ⟨342496395609448189564601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228330930406298793043067 342496395609448189564601)
        ·
          refine ⟨256872296707086142173451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342496395609448189564601 256872296707086142173451)
          ·
            refine ⟨385308445060629213260177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256872296707086142173451 385308445060629213260177)
            ·
              refine ⟨288981333795471909945133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385308445060629213260177 288981333795471909945133)
              ·
                refine ⟨108368000173301966229425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288981333795471909945133 108368000173301966229425)
                ·
                  refine ⟨81276000129976474672069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108368000173301966229425 81276000129976474672069)
                  ·
                    rfl

theorem cell20_178070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_178070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178070 prefixEnd_178070 := by exact prefixLift 178070
  have htrace : WordTrace (prefixWord ++ tailWord_178070) baseStart_178070 baseEnd_178070 := by
    simpa [prefixWord, tailWord_178070, baseEnd_178070] using wordTrace_append hprefix tailTrace_178070
  have hstable : (prefixWord ++ tailWord_178070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178070).length < 2 ^ (prefixWord ++ tailWord_178070).sum := by decide
  have hdescent : baseEnd_178070 < baseStart_178070 := by decide
  rcases family_descends (prefixWord ++ tailWord_178070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178088 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_178088 : Nat := 118140960795 + 178088 * 2 ^ 59
def prefixEnd_178088 : Nat := 4983230072969 + 3 ^ 40 * 178088 * 2
def baseEnd_178088 : Nat := 81284215820448412071995

theorem tailTrace_178088 : CollatzResearch.WordTrace tailWord_178088 prefixEnd_178088 81284215820448412071995 := by
  unfold tailWord_178088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247701489412532927023459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4330268652550043902697945 3247701489412532927023459)
  ·
    refine ⟨4871552234118799390535189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3247701489412532927023459 4871552234118799390535189)
    ·
      refine ⟨228354010974318721431337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4871552234118799390535189 228354010974318721431337)
      ·
        refine ⟨171265508230739041073503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228354010974318721431337 171265508230739041073503)
        ·
          refine ⟨256898262346108561610255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171265508230739041073503 256898262346108561610255)
          ·
            refine ⟨385347393519162842415383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256898262346108561610255 385347393519162842415383)
            ·
              refine ⟨578021090278744263623075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385347393519162842415383 578021090278744263623075)
              ·
                refine ⟨867031635418116395434613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578021090278744263623075 867031635418116395434613)
                ·
                  refine ⟨81284215820448412071995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867031635418116395434613 81284215820448412071995)
                  ·
                    rfl

theorem cell20_178088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_178088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178088 prefixEnd_178088 := by exact prefixLift 178088
  have htrace : WordTrace (prefixWord ++ tailWord_178088) baseStart_178088 baseEnd_178088 := by
    simpa [prefixWord, tailWord_178088, baseEnd_178088] using wordTrace_append hprefix tailTrace_178088
  have hstable : (prefixWord ++ tailWord_178088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178088).length < 2 ^ (prefixWord ++ tailWord_178088).sum := by decide
  have hdescent : baseEnd_178088 < baseStart_178088 := by decide
  rcases family_descends (prefixWord ++ tailWord_178088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178099 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_178099 : Nat := 118140960795 + 178099 * 2 ^ 59
def prefixEnd_178099 : Nat := 4983230072969 + 3 ^ 40 * 178099 * 2
def baseEnd_178099 : Nat := 81289236520181262705283

theorem tailTrace_178099 : CollatzResearch.WordTrace tailWord_178099 prefixEnd_178099 81289236520181262705283 := by
  unfold tailWord_178099
  simp only [CollatzResearch.WordTrace]
  refine ⟨6495804181785214732697351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4330536121190143155131567 6495804181785214732697351)
  ·
    refine ⟨9743706272677822099046027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6495804181785214732697351 9743706272677822099046027)
    ·
      refine ⟨14615559409016733148569041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9743706272677822099046027 14615559409016733148569041)
      ·
        refine ⟨10961669556762549861426781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14615559409016733148569041 10961669556762549861426781)
        ·
          refine ⟨4110626083785956198035043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10961669556762549861426781 4110626083785956198035043)
          ·
            refine ⟨6165939125678934297052565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110626083785956198035043 6165939125678934297052565)
            ·
              refine ⟨289028396516200045174339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6165939125678934297052565 289028396516200045174339)
              ·
                refine ⟨433542594774300067761509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289028396516200045174339 433542594774300067761509)
                ·
                  refine ⟨81289236520181262705283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433542594774300067761509 81289236520181262705283)
                  ·
                    rfl

theorem cell20_178099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_178099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178099 prefixEnd_178099 := by exact prefixLift 178099
  have htrace : WordTrace (prefixWord ++ tailWord_178099) baseStart_178099 baseEnd_178099 := by
    simpa [prefixWord, tailWord_178099, baseEnd_178099] using wordTrace_append hprefix tailTrace_178099
  have hstable : (prefixWord ++ tailWord_178099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178099).length < 2 ^ (prefixWord ++ tailWord_178099).sum := by decide
  have hdescent : baseEnd_178099 < baseStart_178099 := by decide
  rcases family_descends (prefixWord ++ tailWord_178099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178133 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 2]
def baseStart_178133 : Nat := 118140960795 + 178133 * 2 ^ 59
def prefixEnd_178133 : Nat := 4983230072969 + 3 ^ 40 * 178133 * 2
def baseEnd_178133 : Nat := 81304755046628255571811

theorem tailTrace_178133 : CollatzResearch.WordTrace tailWord_178133 prefixEnd_178133 81304755046628255571811 := by
  unfold tailWord_178133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497044263662038539435053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4331362842441359026290035 6497044263662038539435053)
  ·
    refine ⟨2436391598873264452288145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6497044263662038539435053 2436391598873264452288145)
    ·
      refine ⟨1827293699154948339216109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436391598873264452288145 1827293699154948339216109)
      ·
        refine ⟨685235137183105627206041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1827293699154948339216109 685235137183105627206041)
        ·
          refine ⟨513926352887329220404531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685235137183105627206041 513926352887329220404531)
          ·
            refine ⟨770889529330993830606797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513926352887329220404531 770889529330993830606797)
            ·
              refine ⟨289083573499122686477549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770889529330993830606797 289083573499122686477549)
              ·
                refine ⟨108406340062171007429081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289083573499122686477549 108406340062171007429081)
                ·
                  refine ⟨81304755046628255571811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108406340062171007429081 81304755046628255571811)
                  ·
                    rfl

theorem cell20_178133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_178133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178133 prefixEnd_178133 := by exact prefixLift 178133
  have htrace : WordTrace (prefixWord ++ tailWord_178133) baseStart_178133 baseEnd_178133 := by
    simpa [prefixWord, tailWord_178133, baseEnd_178133] using wordTrace_append hprefix tailTrace_178133
  have hstable : (prefixWord ++ tailWord_178133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178133).length < 2 ^ (prefixWord ++ tailWord_178133).sum := by decide
  have hdescent : baseEnd_178133 < baseStart_178133 := by decide
  rcases family_descends (prefixWord ++ tailWord_178133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178161 : List Nat := [1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_178161 : Nat := 118140960795 + 178161 * 2 ^ 59
def prefixEnd_178161 : Nat := 4983230072969 + 3 ^ 40 * 178161 * 2
def baseEnd_178161 : Nat := 27105845003194867546121

theorem tailTrace_178161 : CollatzResearch.WordTrace tailWord_178161 prefixEnd_178161 27105845003194867546121 := by
  unfold tailWord_178161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498065507560599321454337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4332043671707066214302891 6498065507560599321454337)
  ·
    refine ⟨4873549130670449491090753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6498065507560599321454337 4873549130670449491090753)
    ·
      refine ⟨3655161848002837118318065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4873549130670449491090753 3655161848002837118318065)
      ·
        refine ⟨2741371386002127838738549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3655161848002837118318065 2741371386002127838738549)
        ·
          refine ⟨257003567437699484881739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2741371386002127838738549 257003567437699484881739)
          ·
            refine ⟨385505351156549227322609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257003567437699484881739 385505351156549227322609)
            ·
              refine ⟨289129013367411920491957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385505351156549227322609 289129013367411920491957)
              ·
                refine ⟨27105845003194867546121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 289129013367411920491957 27105845003194867546121)
                ·
                  rfl

theorem cell20_178161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_178161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178161 prefixEnd_178161 := by exact prefixLift 178161
  have htrace : WordTrace (prefixWord ++ tailWord_178161) baseStart_178161 baseEnd_178161 := by
    simpa [prefixWord, tailWord_178161, baseEnd_178161] using wordTrace_append hprefix tailTrace_178161
  have hstable : (prefixWord ++ tailWord_178161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178161).length < 2 ^ (prefixWord ++ tailWord_178161).sum := by decide
  have hdescent : baseEnd_178161 < baseStart_178161 := by decide
  rcases family_descends (prefixWord ++ tailWord_178161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178199 : List Nat := [1, 1, 3, 5, 3, 7]
def baseStart_178199 : Nat := 118140960795 + 178199 * 2 ^ 59
def prefixEnd_178199 : Nat := 4983230072969 + 3 ^ 40 * 178199 * 2
def baseEnd_178199 : Nat := 3012402935000939235983

theorem tailTrace_178199 : CollatzResearch.WordTrace tailWord_178199 prefixEnd_178199 3012402935000939235983 := by
  unfold tailWord_178199
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499451481422931811337651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4332967654281954540891767 6499451481422931811337651)
  ·
    refine ⟨9749177222134397717006477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499451481422931811337651 9749177222134397717006477)
    ·
      refine ⟨3655941458300399143877429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9749177222134397717006477 3655941458300399143877429)
      ·
        refine ⟨342744511715662419738509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3655941458300399143877429 342744511715662419738509)
        ·
          refine ⟨128529191893373407401941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342744511715662419738509 128529191893373407401941)
          ·
            refine ⟨3012402935000939235983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128529191893373407401941 3012402935000939235983)
            ·
              rfl

theorem cell20_178199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 7].length) (baseStart_178199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178199 prefixEnd_178199 := by exact prefixLift 178199
  have htrace : WordTrace (prefixWord ++ tailWord_178199) baseStart_178199 baseEnd_178199 := by
    simpa [prefixWord, tailWord_178199, baseEnd_178199] using wordTrace_append hprefix tailTrace_178199
  have hstable : (prefixWord ++ tailWord_178199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178199).length < 2 ^ (prefixWord ++ tailWord_178199).sum := by decide
  have hdescent : baseEnd_178199 < baseStart_178199 := by decide
  rcases family_descends (prefixWord ++ tailWord_178199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178209 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 2]
def baseStart_178209 : Nat := 118140960795 + 178209 * 2 ^ 59
def prefixEnd_178209 : Nat := 4983230072969 + 3 ^ 40 * 178209 * 2
def baseEnd_178209 : Nat := 81339443517509769038167

theorem tailTrace_178209 : CollatzResearch.WordTrace tailWord_178209 prefixEnd_178209 81339443517509769038167 := by
  unfold tailWord_178209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499816211386703519201681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4333210807591135679467787 6499816211386703519201681)
  ·
    refine ⟨4874862158540027639401261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6499816211386703519201681 4874862158540027639401261)
    ·
      refine ⟨1828073309452510364775473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4874862158540027639401261 1828073309452510364775473)
      ·
        refine ⟨1371054982089382773581605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1828073309452510364775473 1371054982089382773581605)
        ·
          refine ⟨257072809141759270046551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1371054982089382773581605 257072809141759270046551)
          ·
            refine ⟨385609213712638905069827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257072809141759270046551 385609213712638905069827)
            ·
              refine ⟨578413820568958357604741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385609213712638905069827 578413820568958357604741)
              ·
                refine ⟨108452591356679692050889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578413820568958357604741 108452591356679692050889)
                ·
                  refine ⟨81339443517509769038167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108452591356679692050889 81339443517509769038167)
                  ·
                    rfl

theorem cell20_178209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_178209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178209 prefixEnd_178209 := by exact prefixLift 178209
  have htrace : WordTrace (prefixWord ++ tailWord_178209) baseStart_178209 baseEnd_178209 := by
    simpa [prefixWord, tailWord_178209, baseEnd_178209] using wordTrace_append hprefix tailTrace_178209
  have hstable : (prefixWord ++ tailWord_178209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178209).length < 2 ^ (prefixWord ++ tailWord_178209).sum := by decide
  have hdescent : baseEnd_178209 < baseStart_178209 := by decide
  rcases family_descends (prefixWord ++ tailWord_178209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178230 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_178230 : Nat := 118140960795 + 178230 * 2 ^ 59
def prefixEnd_178230 : Nat := 4983230072969 + 3 ^ 40 * 178230 * 2
def baseEnd_178230 : Nat := 81349028489727029338081

theorem tailTrace_178230 : CollatzResearch.WordTrace tailWord_178230 prefixEnd_178230 81349028489727029338081 := by
  unfold tailWord_178230
  simp only [CollatzResearch.WordTrace]
  refine ⟨406286384019414006607259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4333721429540416070477429 406286384019414006607259)
  ·
    refine ⟨609429576029121009910889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406286384019414006607259 609429576029121009910889)
    ·
      refine ⟨457072182021840757433167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 609429576029121009910889 457072182021840757433167)
      ·
        refine ⟨685608273032761136149751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457072182021840757433167 685608273032761136149751)
        ·
          refine ⟨1028412409549141704224627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685608273032761136149751 1028412409549141704224627)
          ·
            refine ⟨1542618614323712556336941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028412409549141704224627 1542618614323712556336941)
            ·
              refine ⟨578481980371392208626353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1542618614323712556336941 578481980371392208626353)
              ·
                refine ⟨433861485278544156469765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578481980371392208626353 433861485278544156469765)
                ·
                  refine ⟨81349028489727029338081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433861485278544156469765 81349028489727029338081)
                  ·
                    rfl

theorem cell20_178230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_178230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178230 prefixEnd_178230 := by exact prefixLift 178230
  have htrace : WordTrace (prefixWord ++ tailWord_178230) baseStart_178230 baseEnd_178230 := by
    simpa [prefixWord, tailWord_178230, baseEnd_178230] using wordTrace_append hprefix tailTrace_178230
  have hstable : (prefixWord ++ tailWord_178230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178230).length < 2 ^ (prefixWord ++ tailWord_178230).sum := by decide
  have hdescent : baseEnd_178230 < baseStart_178230 := by decide
  rcases family_descends (prefixWord ++ tailWord_178230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178237 : List Nat := [1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_178237 : Nat := 118140960795 + 178237 * 2 ^ 59
def prefixEnd_178237 : Nat := 4983230072969 + 3 ^ 40 * 178237 * 2
def baseEnd_178237 : Nat := 27117407826822038701573

theorem tailTrace_178237 : CollatzResearch.WordTrace tailWord_178237 prefixEnd_178237 27117407826822038701573 := by
  unfold tailWord_178237
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500837455285264301220965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4333891636856842867480643 6500837455285264301220965)
  ·
    refine ⟨1218907022865987056478931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6500837455285264301220965 1218907022865987056478931)
    ·
      refine ⟨1828360534298980584718397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218907022865987056478931 1828360534298980584718397)
      ·
        refine ⟨685635200362117719269399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1828360534298980584718397 685635200362117719269399)
        ·
          refine ⟨1028452800543176578904099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685635200362117719269399 1028452800543176578904099)
          ·
            refine ⟨1542679200814764868356149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028452800543176578904099 1542679200814764868356149)
            ·
              refine ⟨144626175076384206408389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1542679200814764868356149 144626175076384206408389)
              ·
                refine ⟨27117407826822038701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144626175076384206408389 27117407826822038701573)
                ·
                  rfl

theorem cell20_178237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_178237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178237 prefixEnd_178237 := by exact prefixLift 178237
  have htrace : WordTrace (prefixWord ++ tailWord_178237) baseStart_178237 baseEnd_178237 := by
    simpa [prefixWord, tailWord_178237, baseEnd_178237] using wordTrace_append hprefix tailTrace_178237
  have hstable : (prefixWord ++ tailWord_178237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178237).length < 2 ^ (prefixWord ++ tailWord_178237).sum := by decide
  have hdescent : baseEnd_178237 < baseStart_178237 := by decide
  rcases family_descends (prefixWord ++ tailWord_178237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178261 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_178261 : Nat := 118140960795 + 178261 * 2 ^ 59
def prefixEnd_178261 : Nat := 4983230072969 + 3 ^ 40 * 178261 * 2
def baseEnd_178261 : Nat := 81363177734428699304621

theorem tailTrace_178261 : CollatzResearch.WordTrace tailWord_178261 prefixEnd_178261 81363177734428699304621 := by
  unfold tailWord_178261
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501712807198316400094637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4334475204798877600063091 6501712807198316400094637)
  ·
    refine ⟨2438142302699368650035489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6501712807198316400094637 2438142302699368650035489)
    ·
      refine ⟨1828606727024526487526617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2438142302699368650035489 1828606727024526487526617)
      ·
        refine ⟨1371455045268394865644963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1828606727024526487526617 1371455045268394865644963)
        ·
          refine ⟨2057182567902592298467445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371455045268394865644963 2057182567902592298467445)
          ·
            refine ⟨192860865740868027981323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2057182567902592298467445 192860865740868027981323)
            ·
              refine ⟨289291298611302041971985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192860865740868027981323 289291298611302041971985)
              ·
                refine ⟨216968473958476531478989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289291298611302041971985 216968473958476531478989)
                ·
                  refine ⟨81363177734428699304621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216968473958476531478989 81363177734428699304621)
                  ·
                    rfl

theorem cell20_178261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_178261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178261 prefixEnd_178261 := by exact prefixLift 178261
  have htrace : WordTrace (prefixWord ++ tailWord_178261) baseStart_178261 baseEnd_178261 := by
    simpa [prefixWord, tailWord_178261, baseEnd_178261] using wordTrace_append hprefix tailTrace_178261
  have hstable : (prefixWord ++ tailWord_178261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178261).length < 2 ^ (prefixWord ++ tailWord_178261).sum := by decide
  have hdescent : baseEnd_178261 < baseStart_178261 := by decide
  rcases family_descends (prefixWord ++ tailWord_178261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178265 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_178265 : Nat := 118140960795 + 178265 * 2 ^ 59
def prefixEnd_178265 : Nat := 4983230072969 + 3 ^ 40 * 178265 * 2
def baseEnd_178265 : Nat := 81365003443422463171271

theorem tailTrace_178265 : CollatzResearch.WordTrace tailWord_178265 prefixEnd_178265 81365003443422463171271 := by
  unfold tailWord_178265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501858699183825083240249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4334572466122550055493499 6501858699183825083240249)
  ·
    refine ⟨4876394024387868812430187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6501858699183825083240249 4876394024387868812430187)
    ·
      refine ⟨7314591036581803218645281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876394024387868812430187 7314591036581803218645281)
      ·
        refine ⟨5485943277436352413983961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314591036581803218645281 5485943277436352413983961)
        ·
          refine ⟨4114457458077264310487971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485943277436352413983961 4114457458077264310487971)
          ·
            refine ⟨6171686187115896465731957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114457458077264310487971 6171686187115896465731957)
            ·
              refine ⟨578595580042115293662371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6171686187115896465731957 578595580042115293662371)
              ·
                refine ⟨867893370063172940493557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578595580042115293662371 867893370063172940493557)
                ·
                  refine ⟨81365003443422463171271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867893370063172940493557 81365003443422463171271)
                  ·
                    rfl

theorem cell20_178265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_178265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178265 prefixEnd_178265 := by exact prefixLift 178265
  have htrace : WordTrace (prefixWord ++ tailWord_178265) baseStart_178265 baseEnd_178265 := by
    simpa [prefixWord, tailWord_178265, baseEnd_178265] using wordTrace_append hprefix tailTrace_178265
  have hstable : (prefixWord ++ tailWord_178265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178265).length < 2 ^ (prefixWord ++ tailWord_178265).sum := by decide
  have hdescent : baseEnd_178265 < baseStart_178265 := by decide
  rcases family_descends (prefixWord ++ tailWord_178265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178268 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_178268 : Nat := 118140960795 + 178268 * 2 ^ 59
def prefixEnd_178268 : Nat := 4983230072969 + 3 ^ 40 * 178268 * 2
def baseEnd_178268 : Nat := 81366372725167786071259

theorem tailTrace_178268 : CollatzResearch.WordTrace tailWord_178268 prefixEnd_178268 81366372725167786071259 := by
  unfold tailWord_178268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250984059086478297799729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4334645412115304397066305 3250984059086478297799729)
  ·
    refine ⟨2438238044314858723349797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3250984059086478297799729 2438238044314858723349797)
    ·
      refine ⟨457169633309036010628087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2438238044314858723349797 457169633309036010628087)
      ·
        refine ⟨685754449963554015942131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457169633309036010628087 685754449963554015942131)
        ·
          refine ⟨1028631674945331023913197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685754449963554015942131 1028631674945331023913197)
          ·
            refine ⟨385736878104499133967449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1028631674945331023913197 385736878104499133967449)
            ·
              refine ⟨289302658578374350475587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385736878104499133967449 289302658578374350475587)
              ·
                refine ⟨433953987867561525713381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289302658578374350475587 433953987867561525713381)
                ·
                  refine ⟨81366372725167786071259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433953987867561525713381 81366372725167786071259)
                  ·
                    rfl

theorem cell20_178268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_178268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178268 prefixEnd_178268 := by exact prefixLift 178268
  have htrace : WordTrace (prefixWord ++ tailWord_178268) baseStart_178268 baseEnd_178268 := by
    simpa [prefixWord, tailWord_178268, baseEnd_178268] using wordTrace_append hprefix tailTrace_178268
  have hstable : (prefixWord ++ tailWord_178268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178268).length < 2 ^ (prefixWord ++ tailWord_178268).sum := by decide
  have hdescent : baseEnd_178268 < baseStart_178268 := by decide
  rcases family_descends (prefixWord ++ tailWord_178268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178337 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 3]
def baseStart_178337 : Nat := 118140960795 + 178337 * 2 ^ 59
def prefixEnd_178337 : Nat := 4983230072969 + 3 ^ 40 * 178337 * 2
def baseEnd_178337 : Nat := 81397866205310212770977

theorem tailTrace_178337 : CollatzResearch.WordTrace tailWord_178337 prefixEnd_178337 81397866205310212770977 := by
  unfold tailWord_178337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504484754922981379861265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4336323169948654253240843 6504484754922981379861265)
  ·
    refine ⟨4878363566192236034895949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6504484754922981379861265 4878363566192236034895949)
    ·
      refine ⟨1829386337322088513085981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4878363566192236034895949 1829386337322088513085981)
      ·
        refine ⟨686019876495783192407243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1829386337322088513085981 686019876495783192407243)
        ·
          refine ⟨1029029814743674788610865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686019876495783192407243 1029029814743674788610865)
          ·
            refine ⟨771772361057756091458149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1029029814743674788610865 771772361057756091458149)
            ·
              refine ⟨144707317698329267148403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 771772361057756091458149 144707317698329267148403)
              ·
                refine ⟨217060976547493900722605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144707317698329267148403 217060976547493900722605)
                ·
                  refine ⟨81397866205310212770977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217060976547493900722605 81397866205310212770977)
                  ·
                    rfl

theorem cell20_178337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_178337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178337 prefixEnd_178337 := by exact prefixLift 178337
  have htrace : WordTrace (prefixWord ++ tailWord_178337) baseStart_178337 baseEnd_178337 := by
    simpa [prefixWord, tailWord_178337, baseEnd_178337] using wordTrace_append hprefix tailTrace_178337
  have hstable : (prefixWord ++ tailWord_178337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178337).length < 2 ^ (prefixWord ++ tailWord_178337).sum := by decide
  have hdescent : baseEnd_178337 < baseStart_178337 := by decide
  rcases family_descends (prefixWord ++ tailWord_178337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178372 : List Nat := [2, 3, 3, 1, 2, 9]
def baseStart_178372 : Nat := 118140960795 + 178372 * 2 ^ 59
def prefixEnd_178372 : Nat := 4983230072969 + 3 ^ 40 * 178372 * 2
def baseEnd_178372 : Nat := 3015327450333542466821

theorem tailTrace_178372 : CollatzResearch.WordTrace tailWord_178372 prefixEnd_178372 3015327450333542466821 := by
  unfold tailWord_178372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3252880654898091178692685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4337174206530788238256913 3252880654898091178692685)
  ·
    refine ⟨1219830245586784192009757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3252880654898091178692685 1219830245586784192009757)
    ·
      refine ⟨457436342095044072003659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1219830245586784192009757 457436342095044072003659)
      ·
        refine ⟨686154513142566108005489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457436342095044072003659 686154513142566108005489)
        ·
          refine ⟨514615884856924581004117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686154513142566108005489 514615884856924581004117)
          ·
            refine ⟨3015327450333542466821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 514615884856924581004117 3015327450333542466821)
            ·
              rfl

theorem cell20_178372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 9].length) (baseStart_178372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178372 prefixEnd_178372 := by exact prefixLift 178372
  have htrace : WordTrace (prefixWord ++ tailWord_178372) baseStart_178372 baseEnd_178372 := by
    simpa [prefixWord, tailWord_178372, baseEnd_178372] using wordTrace_append hprefix tailTrace_178372
  have hstable : (prefixWord ++ tailWord_178372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178372).length < 2 ^ (prefixWord ++ tailWord_178372).sum := by decide
  have hdescent : baseEnd_178372 < baseStart_178372 := by decide
  rcases family_descends (prefixWord ++ tailWord_178372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178402 : List Nat := [3, 3, 4, 1, 1, 1, 3, 4]
def baseStart_178402 : Nat := 118140960795 + 178402 * 2 ^ 59
def prefixEnd_178402 : Nat := 4983230072969 + 3 ^ 40 * 178402 * 2
def baseEnd_178402 : Nat := 27142511325486291868015

theorem tailTrace_178402 : CollatzResearch.WordTrace tailWord_178402 prefixEnd_178402 27142511325486291868015 := by
  unfold tailWord_178402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626713874921874370244365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4337903666458331653984973 1626713874921874370244365)
  ·
    refine ⟨610017703095702888841637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1626713874921874370244365 610017703095702888841637)
    ·
      refine ⟨114378319330444291657807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 610017703095702888841637 114378319330444291657807)
      ·
        refine ⟨171567478995666437486711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114378319330444291657807 171567478995666437486711)
        ·
          refine ⟨257351218493499656230067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171567478995666437486711 257351218493499656230067)
          ·
            refine ⟨386026827740249484345101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257351218493499656230067 386026827740249484345101)
            ·
              refine ⟨144760060402593556629413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386026827740249484345101 144760060402593556629413)
              ·
                refine ⟨27142511325486291868015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144760060402593556629413 27142511325486291868015)
                ·
                  rfl

theorem cell20_178402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_178402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178402 prefixEnd_178402 := by exact prefixLift 178402
  have htrace : WordTrace (prefixWord ++ tailWord_178402) baseStart_178402 baseEnd_178402 := by
    simpa [prefixWord, tailWord_178402, baseEnd_178402] using wordTrace_append hprefix tailTrace_178402
  have hstable : (prefixWord ++ tailWord_178402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178402).length < 2 ^ (prefixWord ++ tailWord_178402).sum := by decide
  have hdescent : baseEnd_178402 < baseStart_178402 := by decide
  rcases family_descends (prefixWord ++ tailWord_178402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178431 : List Nat := [1, 1, 2, 2, 1, 4, 9]
def baseStart_178431 : Nat := 118140960795 + 178431 * 2 ^ 59
def prefixEnd_178431 : Nat := 4983230072969 + 3 ^ 40 * 178431 * 2
def baseEnd_178431 : Nat := 9048974485184851515251

theorem tailTrace_178431 : CollatzResearch.WordTrace tailWord_178431 prefixEnd_178431 9048974485184851515251 := by
  unfold tailWord_178431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507913216582435433783147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4338608811054956955855431 6507913216582435433783147)
  ·
    refine ⟨9761869824873653150674721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6507913216582435433783147 9761869824873653150674721)
    ·
      refine ⟨7321402368655239863006041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9761869824873653150674721 7321402368655239863006041)
      ·
        refine ⟨5491051776491429897254531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7321402368655239863006041 5491051776491429897254531)
        ·
          refine ⟨8236577664737144845881797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491051776491429897254531 8236577664737144845881797)
          ·
            refine ⟨1544358312138214658602837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8236577664737144845881797 1544358312138214658602837)
            ·
              refine ⟨9048974485184851515251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1544358312138214658602837 9048974485184851515251)
              ·
                rfl

theorem cell20_178431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_178431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178431 prefixEnd_178431 := by exact prefixLift 178431
  have htrace : WordTrace (prefixWord ++ tailWord_178431) baseStart_178431 baseEnd_178431 := by
    simpa [prefixWord, tailWord_178431, baseEnd_178431] using wordTrace_append hprefix tailTrace_178431
  have hstable : (prefixWord ++ tailWord_178431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178431).length < 2 ^ (prefixWord ++ tailWord_178431).sum := by decide
  have hdescent : baseEnd_178431 < baseStart_178431 := by decide
  rcases family_descends (prefixWord ++ tailWord_178431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178441 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_178441 : Nat := 118140960795 + 178441 * 2 ^ 59
def prefixEnd_178441 : Nat := 4983230072969 + 3 ^ 40 * 178441 * 2
def baseEnd_178441 : Nat := 81445334639148073303885

theorem tailTrace_178441 : CollatzResearch.WordTrace tailWord_178441 prefixEnd_178441 81445334639148073303885 := by
  unfold tailWord_178441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508277946546207141647177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4338851964364138094431451 6508277946546207141647177)
  ·
    refine ⟨4881208459909655356235383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6508277946546207141647177 4881208459909655356235383)
    ·
      refine ⟨7321812689864483034353075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881208459909655356235383 7321812689864483034353075)
      ·
        refine ⟨10982719034796724551529613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7321812689864483034353075 10982719034796724551529613)
        ·
          refine ⟨4118519638048771706823605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10982719034796724551529613 4118519638048771706823605)
          ·
            refine ⟨386111216067072347514713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4118519638048771706823605 386111216067072347514713)
            ·
              refine ⟨289583412050304260636035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386111216067072347514713 289583412050304260636035)
              ·
                refine ⟨434375118075456390954053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289583412050304260636035 434375118075456390954053)
                ·
                  refine ⟨81445334639148073303885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434375118075456390954053 81445334639148073303885)
                  ·
                    rfl

theorem cell20_178441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_178441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178441 prefixEnd_178441 := by exact prefixLift 178441
  have htrace : WordTrace (prefixWord ++ tailWord_178441) baseStart_178441 baseEnd_178441 := by
    simpa [prefixWord, tailWord_178441, baseEnd_178441] using wordTrace_append hprefix tailTrace_178441
  have hstable : (prefixWord ++ tailWord_178441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178441).length < 2 ^ (prefixWord ++ tailWord_178441).sum := by decide
  have hdescent : baseEnd_178441 < baseStart_178441 := by decide
  rcases family_descends (prefixWord ++ tailWord_178441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178461 : List Nat := [1, 4, 2, 3, 3, 1, 2, 4]
def baseStart_178461 : Nat := 118140960795 + 178461 * 2 ^ 59
def prefixEnd_178461 : Nat := 4983230072969 + 3 ^ 40 * 178461 * 2
def baseEnd_178461 : Nat := 27151487728038964212379

theorem tailTrace_178461 : CollatzResearch.WordTrace tailWord_178461 prefixEnd_178461 27151487728038964212379 := by
  unfold tailWord_178461
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509007406473750557375237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4339338270982500371583491 6509007406473750557375237)
  ·
    refine ⟨1220438888713828229507857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6509007406473750557375237 1220438888713828229507857)
    ·
      refine ⟨915329166535371172130893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1220438888713828229507857 915329166535371172130893)
      ·
        refine ⟨343248437450764189549085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 915329166535371172130893 343248437450764189549085)
        ·
          refine ⟨128718164044036571080907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343248437450764189549085 128718164044036571080907)
          ·
            refine ⟨193077246066054856621361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128718164044036571080907 193077246066054856621361)
            ·
              refine ⟨144807934549541142466021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193077246066054856621361 144807934549541142466021)
              ·
                refine ⟨27151487728038964212379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144807934549541142466021 27151487728038964212379)
                ·
                  rfl

theorem cell20_178461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_178461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178461 prefixEnd_178461 := by exact prefixLift 178461
  have htrace : WordTrace (prefixWord ++ tailWord_178461) baseStart_178461 baseEnd_178461 := by
    simpa [prefixWord, tailWord_178461, baseEnd_178461] using wordTrace_append hprefix tailTrace_178461
  have hstable : (prefixWord ++ tailWord_178461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178461).length < 2 ^ (prefixWord ++ tailWord_178461).sum := by decide
  have hdescent : baseEnd_178461 < baseStart_178461 := by decide
  rcases family_descends (prefixWord ++ tailWord_178461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178583 : List Nat := [1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_178583 : Nat := 118140960795 + 178583 * 2 ^ 59
def prefixEnd_178583 : Nat := 4983230072969 + 3 ^ 40 * 178583 * 2
def baseEnd_178583 : Nat := 27170049102808896856657

theorem tailTrace_178583 : CollatzResearch.WordTrace tailWord_178583 prefixEnd_178583 27170049102808896856657 := by
  unfold tailWord_178583
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513457112031765393316403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4342304741354510262210935 6513457112031765393316403)
  ·
    refine ⟨9770185668047648089974605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6513457112031765393316403 9770185668047648089974605)
    ·
      refine ⟨3663819625517868033740477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9770185668047648089974605 3663819625517868033740477)
      ·
        refine ⟨1373932359569200512652679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3663819625517868033740477 1373932359569200512652679)
        ·
          refine ⟨2060898539353800768979019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373932359569200512652679 2060898539353800768979019)
          ·
            refine ⟨3091347809030701153468529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060898539353800768979019 3091347809030701153468529)
            ·
              refine ⟨2318510856773025865101397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3091347809030701153468529 2318510856773025865101397)
              ·
                refine ⟨27170049102808896856657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2318510856773025865101397 27170049102808896856657)
                ·
                  rfl

theorem cell20_178583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_178583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178583 prefixEnd_178583 := by exact prefixLift 178583
  have htrace : WordTrace (prefixWord ++ tailWord_178583) baseStart_178583 baseEnd_178583 := by
    simpa [prefixWord, tailWord_178583, baseEnd_178583] using wordTrace_append hprefix tailTrace_178583
  have hstable : (prefixWord ++ tailWord_178583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178583).length < 2 ^ (prefixWord ++ tailWord_178583).sum := by decide
  have hdescent : baseEnd_178583 < baseStart_178583 := by decide
  rcases family_descends (prefixWord ++ tailWord_178583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178589 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 2]
def baseStart_178589 : Nat := 118140960795 + 178589 * 2 ^ 59
def prefixEnd_178589 : Nat := 4983230072969 + 3 ^ 40 * 178589 * 2
def baseEnd_178589 : Nat := 81512885871917336369947

theorem tailTrace_178589 : CollatzResearch.WordTrace tailWord_178589 prefixEnd_178589 81512885871917336369947 := by
  unfold tailWord_178589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513675950010028418034821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4342450633340018945356547 6513675950010028418034821)
  ·
    refine ⟨1221314240626880328381529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6513675950010028418034821 1221314240626880328381529)
    ·
      refine ⟨915985680470160246286147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221314240626880328381529 915985680470160246286147)
      ·
        refine ⟨1373978520705240369429221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915985680470160246286147 1373978520705240369429221)
        ·
          refine ⟨257620972632232569267979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1373978520705240369429221 257620972632232569267979)
          ·
            refine ⟨386431458948348853901969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257620972632232569267979 386431458948348853901969)
            ·
              refine ⟨289823594211261640426477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386431458948348853901969 289823594211261640426477)
              ·
                refine ⟨108683847829223115159929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289823594211261640426477 108683847829223115159929)
                ·
                  refine ⟨81512885871917336369947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108683847829223115159929 81512885871917336369947)
                  ·
                    rfl

theorem cell20_178589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_178589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178589 prefixEnd_178589 := by exact prefixLift 178589
  have htrace : WordTrace (prefixWord ++ tailWord_178589) baseStart_178589 baseEnd_178589 := by
    simpa [prefixWord, tailWord_178589, baseEnd_178589] using wordTrace_append hprefix tailTrace_178589
  have hstable : (prefixWord ++ tailWord_178589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178589).length < 2 ^ (prefixWord ++ tailWord_178589).sum := by decide
  have hdescent : baseEnd_178589 < baseStart_178589 := by decide
  rcases family_descends (prefixWord ++ tailWord_178589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178645 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_178645 : Nat := 118140960795 + 178645 * 2 ^ 59
def prefixEnd_178645 : Nat := 4983230072969 + 3 ^ 40 * 178645 * 2
def baseEnd_178645 : Nat := 81538445797830030503051

theorem tailTrace_178645 : CollatzResearch.WordTrace tailWord_178645 prefixEnd_178645 81538445797830030503051 := by
  unfold tailWord_178645
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515718437807149982073389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4343812291871433321382259 6515718437807149982073389)
  ·
    refine ⟨2443394414177681243277521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6515718437807149982073389 2443394414177681243277521)
    ·
      refine ⟨1832545810633260932458141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2443394414177681243277521 1832545810633260932458141)
      ·
        refine ⟨687204678987472849671803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1832545810633260932458141 687204678987472849671803)
        ·
          refine ⟨1030807018481209274507705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687204678987472849671803 1030807018481209274507705)
          ·
            refine ⟨773105263860906955880779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030807018481209274507705 773105263860906955880779)
            ·
              refine ⟨1159657895791360433821169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773105263860906955880779 1159657895791360433821169)
              ·
                refine ⟨869743421843520325365877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159657895791360433821169 869743421843520325365877)
                ·
                  refine ⟨81538445797830030503051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 869743421843520325365877 81538445797830030503051)
                  ·
                    rfl

theorem cell20_178645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_178645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178645 prefixEnd_178645 := by exact prefixLift 178645
  have htrace : WordTrace (prefixWord ++ tailWord_178645) baseStart_178645 baseEnd_178645 := by
    simpa [prefixWord, tailWord_178645, baseEnd_178645] using wordTrace_append hprefix tailTrace_178645
  have hstable : (prefixWord ++ tailWord_178645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178645).length < 2 ^ (prefixWord ++ tailWord_178645).sum := by decide
  have hdescent : baseEnd_178645 < baseStart_178645 := by decide
  rcases family_descends (prefixWord ++ tailWord_178645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178707 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 2]
def baseStart_178707 : Nat := 118140960795 + 178707 * 2 ^ 59
def prefixEnd_178707 : Nat := 4983230072969 + 3 ^ 40 * 178707 * 2
def baseEnd_178707 : Nat := 81566744287233370436131

theorem tailTrace_178707 : CollatzResearch.WordTrace tailWord_178707 prefixEnd_178707 81566744287233370436131 := by
  unfold tailWord_178707
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517979763582534570830375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4345319842388356380553583 6517979763582534570830375)
  ·
    refine ⟨9776969645373801856245563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6517979763582534570830375 9776969645373801856245563)
    ·
      refine ⟨14665454468060702784368345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776969645373801856245563 14665454468060702784368345)
      ·
        refine ⟨10999090851045527088276259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14665454468060702784368345 10999090851045527088276259)
        ·
          refine ⟨16498636276568290632414389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999090851045527088276259 16498636276568290632414389)
          ·
            refine ⟨1546747150928277246788849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16498636276568290632414389 1546747150928277246788849)
            ·
              refine ⟨1160060363196207935091637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546747150928277246788849 1160060363196207935091637)
              ·
                refine ⟨108755659049644493914841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1160060363196207935091637 108755659049644493914841)
                ·
                  refine ⟨81566744287233370436131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108755659049644493914841 81566744287233370436131)
                  ·
                    rfl

theorem cell20_178707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2].length) (baseStart_178707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178707 prefixEnd_178707 := by exact prefixLift 178707
  have htrace : WordTrace (prefixWord ++ tailWord_178707) baseStart_178707 baseEnd_178707 := by
    simpa [prefixWord, tailWord_178707, baseEnd_178707] using wordTrace_append hprefix tailTrace_178707
  have hstable : (prefixWord ++ tailWord_178707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178707).length < 2 ^ (prefixWord ++ tailWord_178707).sum := by decide
  have hdescent : baseEnd_178707 < baseStart_178707 := by decide
  rcases family_descends (prefixWord ++ tailWord_178707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178720 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_178720 : Nat := 118140960795 + 178720 * 2 ^ 59
def prefixEnd_178720 : Nat := 4983230072969 + 3 ^ 40 * 178720 * 2
def baseEnd_178720 : Nat := 81572677841463103002745

theorem tailTrace_178720 : CollatzResearch.WordTrace tailWord_178720 prefixEnd_178720 81572677841463103002745 := by
  unfold tailWord_178720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3259226956267718895526807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4345635941690291860702409 3259226956267718895526807)
  ·
    refine ⟨4888840434401578343290211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3259226956267718895526807 4888840434401578343290211)
    ·
      refine ⟨7333260651602367514935317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888840434401578343290211 7333260651602367514935317)
      ·
        refine ⟨343746593043860977262593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7333260651602367514935317 343746593043860977262593)
        ·
          refine ⟨257809944782895732946945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343746593043860977262593 257809944782895732946945)
          ·
            refine ⟨193357458587171799710209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257809944782895732946945 193357458587171799710209)
            ·
              refine ⟨145018093940378849782657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193357458587171799710209 145018093940378849782657)
              ·
                refine ⟨108763570455284137336993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145018093940378849782657 108763570455284137336993)
                ·
                  refine ⟨81572677841463103002745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108763570455284137336993 81572677841463103002745)
                  ·
                    rfl

theorem cell20_178720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_178720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178720 prefixEnd_178720 := by exact prefixLift 178720
  have htrace : WordTrace (prefixWord ++ tailWord_178720) baseStart_178720 baseEnd_178720 := by
    simpa [prefixWord, tailWord_178720, baseEnd_178720] using wordTrace_append hprefix tailTrace_178720
  have hstable : (prefixWord ++ tailWord_178720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178720).length < 2 ^ (prefixWord ++ tailWord_178720).sum := by decide
  have hdescent : baseEnd_178720 < baseStart_178720 := by decide
  rcases family_descends (prefixWord ++ tailWord_178720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178727 : List Nat := [1, 1, 7, 2, 2, 1, 1, 5]
def baseStart_178727 : Nat := 118140960795 + 178727 * 2 ^ 59
def prefixEnd_178727 : Nat := 4983230072969 + 3 ^ 40 * 178727 * 2
def baseEnd_178727 : Nat := 27191957610734063256461

theorem tailTrace_178727 : CollatzResearch.WordTrace tailWord_178727 prefixEnd_178727 27191957610734063256461 := by
  unfold tailWord_178727
  simp only [CollatzResearch.WordTrace]
  refine ⟨6518709223510077986558435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4345806149006718657705623 6518709223510077986558435)
  ·
    refine ⟨9778063835265116979837653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6518709223510077986558435 9778063835265116979837653)
    ·
      refine ⟨229173371139026179214945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9778063835265116979837653 229173371139026179214945)
      ·
        refine ⟨171880028354269634411209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229173371139026179214945 171880028354269634411209)
        ·
          refine ⟨128910021265702225808407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171880028354269634411209 128910021265702225808407)
          ·
            refine ⟨193365031898553338712611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128910021265702225808407 193365031898553338712611)
            ·
              refine ⟨290047547847830008068917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193365031898553338712611 290047547847830008068917)
              ·
                refine ⟨27191957610734063256461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290047547847830008068917 27191957610734063256461)
                ·
                  rfl

theorem cell20_178727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_178727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178727 prefixEnd_178727 := by exact prefixLift 178727
  have htrace : WordTrace (prefixWord ++ tailWord_178727) baseStart_178727 baseEnd_178727 := by
    simpa [prefixWord, tailWord_178727, baseEnd_178727] using wordTrace_append hprefix tailTrace_178727
  have hstable : (prefixWord ++ tailWord_178727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178727).length < 2 ^ (prefixWord ++ tailWord_178727).sum := by decide
  have hdescent : baseEnd_178727 < baseStart_178727 := by decide
  rcases family_descends (prefixWord ++ tailWord_178727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178758 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_178758 : Nat := 118140960795 + 178758 * 2 ^ 59
def prefixEnd_178758 : Nat := 4983230072969 + 3 ^ 40 * 178758 * 2
def baseEnd_178758 : Nat := 81590022076903859735923

theorem tailTrace_178758 : CollatzResearch.WordTrace tailWord_178758 prefixEnd_178758 81590022076903859735923 := by
  unfold tailWord_178758
  simp only [CollatzResearch.WordTrace]
  refine ⟨203744996449930321279279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4346559924265180187291285 203744996449930321279279)
  ·
    refine ⟨305617494674895481918919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203744996449930321279279 305617494674895481918919)
    ·
      refine ⟨458426242012343222878379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305617494674895481918919 458426242012343222878379)
      ·
        refine ⟨687639363018514834317569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458426242012343222878379 687639363018514834317569)
        ·
          refine ⟨515729522263886125738177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687639363018514834317569 515729522263886125738177)
          ·
            refine ⟨386797141697914594303633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515729522263886125738177 386797141697914594303633)
            ·
              refine ⟨290097856273435945727725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386797141697914594303633 290097856273435945727725)
              ·
                refine ⟨108786696102538479647897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290097856273435945727725 108786696102538479647897)
                ·
                  refine ⟨81590022076903859735923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108786696102538479647897 81590022076903859735923)
                  ·
                    rfl

theorem cell20_178758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_178758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178758 prefixEnd_178758 := by exact prefixLift 178758
  have htrace : WordTrace (prefixWord ++ tailWord_178758) baseStart_178758 baseEnd_178758 := by
    simpa [prefixWord, tailWord_178758, baseEnd_178758] using wordTrace_append hprefix tailTrace_178758
  have hstable : (prefixWord ++ tailWord_178758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178758).length < 2 ^ (prefixWord ++ tailWord_178758).sum := by decide
  have hdescent : baseEnd_178758 < baseStart_178758 := by decide
  rcases family_descends (prefixWord ++ tailWord_178758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178762 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_178762 : Nat := 118140960795 + 178762 * 2 ^ 59
def prefixEnd_178762 : Nat := 4983230072969 + 3 ^ 40 * 178762 * 2
def baseEnd_178762 : Nat := 81591847785897623602573

theorem tailTrace_178762 : CollatzResearch.WordTrace tailWord_178762 prefixEnd_178762 81591847785897623602573 := by
  unfold tailWord_178762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629996444595819741020635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4346657185588852642721693 1629996444595819741020635)
  ·
    refine ⟨2444994666893729611530953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1629996444595819741020635 2444994666893729611530953)
    ·
      refine ⟨1833746000170297208648215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2444994666893729611530953 1833746000170297208648215)
      ·
        refine ⟨2750619000255445812972323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833746000170297208648215 2750619000255445812972323)
        ·
          refine ⟨4125928500383168719458485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750619000255445812972323 4125928500383168719458485)
          ·
            refine ⟨386805796910922067449233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4125928500383168719458485 386805796910922067449233)
            ·
              refine ⟨290104347683191550586925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386805796910922067449233 290104347683191550586925)
              ·
                refine ⟨108789130381196831470097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290104347683191550586925 108789130381196831470097)
                ·
                  refine ⟨81591847785897623602573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108789130381196831470097 81591847785897623602573)
                  ·
                    rfl

theorem cell20_178762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_178762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178762 prefixEnd_178762 := by exact prefixLift 178762
  have htrace : WordTrace (prefixWord ++ tailWord_178762) baseStart_178762 baseEnd_178762 := by
    simpa [prefixWord, tailWord_178762, baseEnd_178762] using wordTrace_append hprefix tailTrace_178762
  have hstable : (prefixWord ++ tailWord_178762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178762).length < 2 ^ (prefixWord ++ tailWord_178762).sum := by decide
  have hdescent : baseEnd_178762 < baseStart_178762 := by decide
  rcases family_descends (prefixWord ++ tailWord_178762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178848 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_178848 : Nat := 118140960795 + 178848 * 2 ^ 59
def prefixEnd_178848 : Nat := 4983230072969 + 3 ^ 40 * 178848 * 2
def baseEnd_178848 : Nat := 81631100529263546735555

theorem tailTrace_178848 : CollatzResearch.WordTrace tailWord_178848 prefixEnd_178848 81631100529263546735555 := by
  unfold tailWord_178848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261561228035857825856599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4348748304047810434475465 3261561228035857825856599)
  ·
    refine ⟨4892341842053786738784899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3261561228035857825856599 4892341842053786738784899)
    ·
      refine ⟨7338512763080680108177349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4892341842053786738784899 7338512763080680108177349)
      ·
        refine ⟨1375971143077627520283253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7338512763080680108177349 1375971143077627520283253)
        ·
          refine ⟨128997294663527580026555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1375971143077627520283253 128997294663527580026555)
          ·
            refine ⟨193495941995291370039833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128997294663527580026555 193495941995291370039833)
            ·
              refine ⟨145121956496468527529875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193495941995291370039833 145121956496468527529875)
              ·
                refine ⟨217682934744702791294813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145121956496468527529875 217682934744702791294813)
                ·
                  refine ⟨81631100529263546735555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217682934744702791294813 81631100529263546735555)
                  ·
                    rfl

theorem cell20_178848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_178848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178848 prefixEnd_178848 := by exact prefixLift 178848
  have htrace : WordTrace (prefixWord ++ tailWord_178848) baseStart_178848 baseEnd_178848 := by
    simpa [prefixWord, tailWord_178848, baseEnd_178848] using wordTrace_append hprefix tailTrace_178848
  have hstable : (prefixWord ++ tailWord_178848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178848).length < 2 ^ (prefixWord ++ tailWord_178848).sum := by decide
  have hdescent : baseEnd_178848 < baseStart_178848 := by decide
  rcases family_descends (prefixWord ++ tailWord_178848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178890 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_178890 : Nat := 118140960795 + 178890 * 2 ^ 59
def prefixEnd_178890 : Nat := 4983230072969 + 3 ^ 40 * 178890 * 2
def baseEnd_178890 : Nat := 81650270473698067335383

theorem tailTrace_178890 : CollatzResearch.WordTrace tailWord_178890 prefixEnd_178890 81650270473698067335383 := by
  unfold tailWord_178890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631163580479889206185531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4349769547946371216494749 1631163580479889206185531)
  ·
    refine ⟨2446745370719833809278297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631163580479889206185531 2446745370719833809278297)
    ·
      refine ⟨1835059028039875356958723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446745370719833809278297 1835059028039875356958723)
      ·
        refine ⟨2752588542059813035438085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835059028039875356958723 2752588542059813035438085)
        ·
          refine ⟨516110351636214944144641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2752588542059813035438085 516110351636214944144641)
          ·
            refine ⟨387082763727161208108481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516110351636214944144641 387082763727161208108481)
            ·
              refine ⟨290312072795370906081361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387082763727161208108481 290312072795370906081361)
              ·
                refine ⟨217734054596528179561021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290312072795370906081361 217734054596528179561021)
                ·
                  refine ⟨81650270473698067335383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217734054596528179561021 81650270473698067335383)
                  ·
                    rfl

theorem cell20_178890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_178890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178890 prefixEnd_178890 := by exact prefixLift 178890
  have htrace : WordTrace (prefixWord ++ tailWord_178890) baseStart_178890 baseEnd_178890 := by
    simpa [prefixWord, tailWord_178890, baseEnd_178890] using wordTrace_append hprefix tailTrace_178890
  have hstable : (prefixWord ++ tailWord_178890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178890).length < 2 ^ (prefixWord ++ tailWord_178890).sum := by decide
  have hdescent : baseEnd_178890 < baseStart_178890 := by decide
  rcases family_descends (prefixWord ++ tailWord_178890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178897 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 2]
def baseStart_178897 : Nat := 118140960795 + 178897 * 2 ^ 59
def prefixEnd_178897 : Nat := 4983230072969 + 3 ^ 40 * 178897 * 2
def baseEnd_178897 : Nat := 81653465464437154102021

theorem tailTrace_178897 : CollatzResearch.WordTrace tailWord_178897 prefixEnd_178897 81653465464437154102021 := by
  unfold tailWord_178897
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524909632894197020246945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4349939755262798013497963 6524909632894197020246945)
  ·
    refine ⟨4893682224670647765185209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6524909632894197020246945 4893682224670647765185209)
    ·
      refine ⟨3670261668502985823888907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4893682224670647765185209 3670261668502985823888907)
      ·
        refine ⟨5505392502754478735833361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670261668502985823888907 5505392502754478735833361)
        ·
          refine ⟨4129044377065859051875021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5505392502754478735833361 4129044377065859051875021)
          ·
            refine ⟨1548391641399697144453133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4129044377065859051875021 1548391641399697144453133)
            ·
              refine ⟨580646865524886429169925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548391641399697144453133 580646865524886429169925)
              ·
                refine ⟨108871287285916205469361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580646865524886429169925 108871287285916205469361)
                ·
                  refine ⟨81653465464437154102021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108871287285916205469361 81653465464437154102021)
                  ·
                    rfl

theorem cell20_178897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_178897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178897 prefixEnd_178897 := by exact prefixLift 178897
  have htrace : WordTrace (prefixWord ++ tailWord_178897) baseStart_178897 baseEnd_178897 := by
    simpa [prefixWord, tailWord_178897, baseEnd_178897] using wordTrace_append hprefix tailTrace_178897
  have hstable : (prefixWord ++ tailWord_178897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178897).length < 2 ^ (prefixWord ++ tailWord_178897).sum := by decide
  have hdescent : baseEnd_178897 < baseStart_178897 := by decide
  rcases family_descends (prefixWord ++ tailWord_178897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178900 : List Nat := [2, 4, 1, 3, 3, 1, 1, 5]
def baseStart_178900 : Nat := 118140960795 + 178900 * 2 ^ 59
def prefixEnd_178900 : Nat := 4983230072969 + 3 ^ 40 * 178900 * 2
def baseEnd_178900 : Nat := 27218278248727492334003

theorem tailTrace_178900 : CollatzResearch.WordTrace tailWord_178900 prefixEnd_178900 27218278248727492334003 := by
  unfold tailWord_178900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262509525941664266303077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4350012701255552355070769 3262509525941664266303077)
  ·
    refine ⟨611720536114062049931827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3262509525941664266303077 611720536114062049931827)
    ·
      refine ⟨917580804171093074897741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611720536114062049931827 917580804171093074897741)
      ·
        refine ⟨344092801564159903086653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 917580804171093074897741 344092801564159903086653)
        ·
          refine ⟨129034800586559963657495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344092801564159903086653 129034800586559963657495)
          ·
            refine ⟨193552200879839945486243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129034800586559963657495 193552200879839945486243)
            ·
              refine ⟨290328301319759918229365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193552200879839945486243 290328301319759918229365)
              ·
                refine ⟨27218278248727492334003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290328301319759918229365 27218278248727492334003)
                ·
                  rfl

theorem cell20_178900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_178900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178900 prefixEnd_178900 := by exact prefixLift 178900
  have htrace : WordTrace (prefixWord ++ tailWord_178900) baseStart_178900 baseEnd_178900 := by
    simpa [prefixWord, tailWord_178900, baseEnd_178900] using wordTrace_append hprefix tailTrace_178900
  have hstable : (prefixWord ++ tailWord_178900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178900).length < 2 ^ (prefixWord ++ tailWord_178900).sum := by decide
  have hdescent : baseEnd_178900 < baseStart_178900 := by decide
  rcases family_descends (prefixWord ++ tailWord_178900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178904 : List Nat := [2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_178904 : Nat := 118140960795 + 178904 * 2 ^ 59
def prefixEnd_178904 : Nat := 4983230072969 + 3 ^ 40 * 178904 * 2
def baseEnd_178904 : Nat := 27218886818392080289553

theorem tailTrace_178904 : CollatzResearch.WordTrace tailWord_178904 prefixEnd_178904 27218886818392080289553 := by
  unfold tailWord_178904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262582471934418607875883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4350109962579224810501177 3262582471934418607875883)
  ·
    refine ⟨4893873707901627911813825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262582471934418607875883 4893873707901627911813825)
    ·
      refine ⟨3670405280926220933860369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4893873707901627911813825 3670405280926220933860369)
      ·
        refine ⟨2752803960694665700395277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3670405280926220933860369 2752803960694665700395277)
        ·
          refine ⟨1032301485260499637648229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2752803960694665700395277 1032301485260499637648229)
          ·
            refine ⟨193556528486343682059043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1032301485260499637648229 193556528486343682059043)
            ·
              refine ⟨290334792729515523088565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193556528486343682059043 290334792729515523088565)
              ·
                refine ⟨27218886818392080289553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290334792729515523088565 27218886818392080289553)
                ·
                  rfl

theorem cell20_178904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_178904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178904 prefixEnd_178904 := by exact prefixLift 178904
  have htrace : WordTrace (prefixWord ++ tailWord_178904) baseStart_178904 baseEnd_178904 := by
    simpa [prefixWord, tailWord_178904, baseEnd_178904] using wordTrace_append hprefix tailTrace_178904
  have hstable : (prefixWord ++ tailWord_178904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178904).length < 2 ^ (prefixWord ++ tailWord_178904).sum := by decide
  have hdescent : baseEnd_178904 < baseStart_178904 := by decide
  rcases family_descends (prefixWord ++ tailWord_178904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178911 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_178911 : Nat := 118140960795 + 178911 * 2 ^ 59
def prefixEnd_178911 : Nat := 4983230072969 + 3 ^ 40 * 178911 * 2
def baseEnd_178911 : Nat := 81659855445915327635297

theorem tailTrace_178911 : CollatzResearch.WordTrace tailWord_178911 prefixEnd_178911 81659855445915327635297 := by
  unfold tailWord_178911
  simp only [CollatzResearch.WordTrace]
  refine ⟨6525420254843477411256587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4350280169895651607504391 6525420254843477411256587)
  ·
    refine ⟨9788130382265216116884881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6525420254843477411256587 9788130382265216116884881)
    ·
      refine ⟨7341097786698912087663661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9788130382265216116884881 7341097786698912087663661)
      ·
        refine ⟨2752911670012092032873873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7341097786698912087663661 2752911670012092032873873)
        ·
          refine ⟨2064683752509069024655405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2752911670012092032873873 2064683752509069024655405)
          ·
            refine ⟨774256407190900884245777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2064683752509069024655405 774256407190900884245777)
            ·
              refine ⟨580692305393175663184333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774256407190900884245777 580692305393175663184333)
              ·
                refine ⟨217759614522440873694125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580692305393175663184333 217759614522440873694125)
                ·
                  refine ⟨81659855445915327635297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217759614522440873694125 81659855445915327635297)
                  ·
                    rfl

theorem cell20_178911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_178911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178911 prefixEnd_178911 := by exact prefixLift 178911
  have htrace : WordTrace (prefixWord ++ tailWord_178911) baseStart_178911 baseEnd_178911 := by
    simpa [prefixWord, tailWord_178911, baseEnd_178911] using wordTrace_append hprefix tailTrace_178911
  have hstable : (prefixWord ++ tailWord_178911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178911).length < 2 ^ (prefixWord ++ tailWord_178911).sum := by decide
  have hdescent : baseEnd_178911 < baseStart_178911 := by decide
  rcases family_descends (prefixWord ++ tailWord_178911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178942 : List Nat := [4, 2, 2, 1, 2, 2, 7]
def baseStart_178942 : Nat := 118140960795 + 178942 * 2 ^ 59
def prefixEnd_178942 : Nat := 4983230072969 + 3 ^ 40 * 178942 * 2
def baseEnd_178942 : Nat := 9074889410068555289093

theorem tailTrace_178942 : CollatzResearch.WordTrace tailWord_178942 prefixEnd_178942 9074889410068555289093 := by
  unfold tailWord_178942
  simp only [CollatzResearch.WordTrace]
  refine ⟨815818864716396213204385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4351033945154113137090053 815818864716396213204385)
  ·
    refine ⟨611864148537297159903289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 815818864716396213204385 611864148537297159903289)
    ·
      refine ⟨458898111402972869927467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 611864148537297159903289 458898111402972869927467)
      ·
        refine ⟨688347167104459304891201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458898111402972869927467 688347167104459304891201)
        ·
          refine ⟨516260375328344478668401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688347167104459304891201 516260375328344478668401)
          ·
            refine ⟨387195281496258359001301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516260375328344478668401 387195281496258359001301)
            ·
              refine ⟨9074889410068555289093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 387195281496258359001301 9074889410068555289093)
              ·
                rfl

theorem cell20_178942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_178942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178942 prefixEnd_178942 := by exact prefixLift 178942
  have htrace : WordTrace (prefixWord ++ tailWord_178942) baseStart_178942 baseEnd_178942 := by
    simpa [prefixWord, tailWord_178942, baseEnd_178942] using wordTrace_append hprefix tailTrace_178942
  have hstable : (prefixWord ++ tailWord_178942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178942).length < 2 ^ (prefixWord ++ tailWord_178942).sum := by decide
  have hdescent : baseEnd_178942 < baseStart_178942 := by decide
  rcases family_descends (prefixWord ++ tailWord_178942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178962 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_178962 : Nat := 118140960795 + 178962 * 2 ^ 59
def prefixEnd_178962 : Nat := 4983230072969 + 3 ^ 40 * 178962 * 2
def baseEnd_178962 : Nat := 81683133235585816935089

theorem tailTrace_178962 : CollatzResearch.WordTrace tailWord_178962 prefixEnd_178962 81683133235585816935089 := by
  unfold tailWord_178962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631820094414678280340785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4351520251772475414242093 1631820094414678280340785)
  ·
    refine ⟨1223865070811008710255589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1631820094414678280340785 1223865070811008710255589)
    ·
      refine ⟨229474700777064133172923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1223865070811008710255589 229474700777064133172923)
      ·
        refine ⟨344212051165596199759385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229474700777064133172923 344212051165596199759385)
        ·
          refine ⟨258159038374197149819539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344212051165596199759385 258159038374197149819539)
          ·
            refine ⟨387238557561295724729309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258159038374197149819539 387238557561295724729309)
            ·
              refine ⟨145214459085485896773491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387238557561295724729309 145214459085485896773491)
              ·
                refine ⟨217821688628228845160237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145214459085485896773491 217821688628228845160237)
                ·
                  refine ⟨81683133235585816935089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217821688628228845160237 81683133235585816935089)
                  ·
                    rfl

theorem cell20_178962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_178962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178962 prefixEnd_178962 := by exact prefixLift 178962
  have htrace : WordTrace (prefixWord ++ tailWord_178962) baseStart_178962 baseEnd_178962 := by
    simpa [prefixWord, tailWord_178962, baseEnd_178962] using wordTrace_append hprefix tailTrace_178962
  have hstable : (prefixWord ++ tailWord_178962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178962).length < 2 ^ (prefixWord ++ tailWord_178962).sum := by decide
  have hdescent : baseEnd_178962 < baseStart_178962 := by decide
  rcases family_descends (prefixWord ++ tailWord_178962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178980 : List Nat := [2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_178980 : Nat := 118140960795 + 178980 * 2 ^ 59
def prefixEnd_178980 : Nat := 4983230072969 + 3 ^ 40 * 178980 * 2
def baseEnd_178980 : Nat := 27230449642019251445005

theorem tailTrace_178980 : CollatzResearch.WordTrace tailWord_178980 prefixEnd_178980 27230449642019251445005 := by
  unfold tailWord_178980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263968445796751097759197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4351957927729001463678929 3263968445796751097759197)
  ·
    refine ⟨1223988167173781661659699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3263968445796751097759197 1223988167173781661659699)
    ·
      refine ⟨1835982250760672492489549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223988167173781661659699 1835982250760672492489549)
      ·
        refine ⟨688493344035252184683581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1835982250760672492489549 688493344035252184683581)
        ·
          refine ⟨258185004013219569256343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 688493344035252184683581 258185004013219569256343)
          ·
            refine ⟨387277506019829353884515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258185004013219569256343 387277506019829353884515)
            ·
              refine ⟨580916259029744030826773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387277506019829353884515 580916259029744030826773)
              ·
                refine ⟨27230449642019251445005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 580916259029744030826773 27230449642019251445005)
                ·
                  rfl

theorem cell20_178980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_178980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178980 prefixEnd_178980 := by exact prefixLift 178980
  have htrace : WordTrace (prefixWord ++ tailWord_178980) baseStart_178980 baseEnd_178980 := by
    simpa [prefixWord, tailWord_178980, baseEnd_178980] using wordTrace_append hprefix tailTrace_178980
  have hstable : (prefixWord ++ tailWord_178980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178980).length < 2 ^ (prefixWord ++ tailWord_178980).sum := by decide
  have hdescent : baseEnd_178980 < baseStart_178980 := by decide
  rcases family_descends (prefixWord ++ tailWord_178980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178986 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_178986 : Nat := 118140960795 + 178986 * 2 ^ 59
def prefixEnd_178986 : Nat := 4983230072969 + 3 ^ 40 * 178986 * 2
def baseEnd_178986 : Nat := 81694087489548400134991

theorem tailTrace_178986 : CollatzResearch.WordTrace tailWord_178986 prefixEnd_178986 81694087489548400134991 := by
  unfold tailWord_178986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632038932392941305059203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4352103819714510146824541 1632038932392941305059203)
  ·
    refine ⟨2448058398589411957588805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632038932392941305059203 2448058398589411957588805)
    ·
      refine ⟨459010949735514742047901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2448058398589411957588805 459010949735514742047901)
      ·
        refine ⟨172129106150818028267963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 459010949735514742047901 172129106150818028267963)
        ·
          refine ⟨258193659226227042401945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172129106150818028267963 258193659226227042401945)
          ·
            refine ⟨193645244419670281801459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258193659226227042401945 193645244419670281801459)
            ·
              refine ⟨290467866629505422702189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193645244419670281801459 290467866629505422702189)
              ·
                refine ⟨108925449986064533513321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290467866629505422702189 108925449986064533513321)
                ·
                  refine ⟨81694087489548400134991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108925449986064533513321 81694087489548400134991)
                  ·
                    rfl

theorem cell20_178986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_178986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_178986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_178986 prefixEnd_178986 := by exact prefixLift 178986
  have htrace : WordTrace (prefixWord ++ tailWord_178986) baseStart_178986 baseEnd_178986 := by
    simpa [prefixWord, tailWord_178986, baseEnd_178986] using wordTrace_append hprefix tailTrace_178986
  have hstable : (prefixWord ++ tailWord_178986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178986).length < 2 ^ (prefixWord ++ tailWord_178986).sum := by decide
  have hdescent : baseEnd_178986 < baseStart_178986 := by decide
  rcases family_descends (prefixWord ++ tailWord_178986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179014 : List Nat := [6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_179014 : Nat := 118140960795 + 179014 * 2 ^ 59
def prefixEnd_179014 : Nat := 4983230072969 + 3 ^ 40 * 179014 * 2
def baseEnd_179014 : Nat := 27235622484168249067181

theorem tailTrace_179014 : CollatzResearch.WordTrace tailWord_179014 prefixEnd_179014 27235622484168249067181 := by
  unfold tailWord_179014
  simp only [CollatzResearch.WordTrace]
  refine ⟨204036780420947687570503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4352784648980217334837397 204036780420947687570503)
  ·
    refine ⟨306055170631421531355755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204036780420947687570503 306055170631421531355755)
    ·
      refine ⟨459082755947132297033633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306055170631421531355755 459082755947132297033633)
      ·
        refine ⟨344312066960349222775225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459082755947132297033633 344312066960349222775225)
        ·
          refine ⟨258234050220261917081419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344312066960349222775225 258234050220261917081419)
          ·
            refine ⟨387351075330392875622129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258234050220261917081419 387351075330392875622129)
            ·
              refine ⟨290513306497794656716597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387351075330392875622129 290513306497794656716597)
              ·
                refine ⟨27235622484168249067181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290513306497794656716597 27235622484168249067181)
                ·
                  rfl

theorem cell20_179014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_179014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179014 prefixEnd_179014 := by exact prefixLift 179014
  have htrace : WordTrace (prefixWord ++ tailWord_179014) baseStart_179014 baseEnd_179014 := by
    simpa [prefixWord, tailWord_179014, baseEnd_179014] using wordTrace_append hprefix tailTrace_179014
  have hstable : (prefixWord ++ tailWord_179014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179014).length < 2 ^ (prefixWord ++ tailWord_179014).sum := by decide
  have hdescent : baseEnd_179014 < baseStart_179014 := by decide
  rcases family_descends (prefixWord ++ tailWord_179014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179021 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_179021 : Nat := 118140960795 + 179021 * 2 ^ 59
def prefixEnd_179021 : Nat := 4983230072969 + 3 ^ 40 * 179021 * 2
def baseEnd_179021 : Nat := 81710062443243833968181

theorem tailTrace_179021 : CollatzResearch.WordTrace tailWord_179021 prefixEnd_179021 81710062443243833968181 := by
  unfold tailWord_179021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529432284444966197760917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4352954856296644131840611 6529432284444966197760917)
  ·
    refine ⟨306067138333357790520043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6529432284444966197760917 306067138333357790520043)
    ·
      refine ⟨459100707500036685780065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306067138333357790520043 459100707500036685780065)
      ·
        refine ⟨344325530625027514335049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459100707500036685780065 344325530625027514335049)
        ·
          refine ⟨258244147968770635751287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344325530625027514335049 258244147968770635751287)
          ·
            refine ⟨387366221953155953626931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258244147968770635751287 387366221953155953626931)
            ·
              refine ⟨581049332929733930440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387366221953155953626931 581049332929733930440397)
              ·
                refine ⟨217893499848650223915149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581049332929733930440397 217893499848650223915149)
                ·
                  refine ⟨81710062443243833968181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217893499848650223915149 81710062443243833968181)
                  ·
                    rfl

theorem cell20_179021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_179021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179021 prefixEnd_179021 := by exact prefixLift 179021
  have htrace : WordTrace (prefixWord ++ tailWord_179021) baseStart_179021 baseEnd_179021 := by
    simpa [prefixWord, tailWord_179021, baseEnd_179021] using wordTrace_append hprefix tailTrace_179021
  have hstable : (prefixWord ++ tailWord_179021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179021).length < 2 ^ (prefixWord ++ tailWord_179021).sum := by decide
  have hdescent : baseEnd_179021 < baseStart_179021 := by decide
  rcases family_descends (prefixWord ++ tailWord_179021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179060 : List Nat := [2, 18]
def baseStart_179060 : Nat := 118140960795 + 179060 * 2 ^ 59
def prefixEnd_179060 : Nat := 4983230072969 + 3 ^ 40 * 179060 * 2
def baseEnd_179060 : Nat := 37369850528547339583

theorem tailTrace_179060 : CollatzResearch.WordTrace tailWord_179060 prefixEnd_179060 37369850528547339583 := by
  unfold tailWord_179060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265427365651837929215317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4353903154202450572287089 3265427365651837929215317)
  ·
    refine ⟨37369850528547339583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 18 3265427365651837929215317 37369850528547339583)
    ·
      rfl

theorem cell20_179060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 18].length) (baseStart_179060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179060 prefixEnd_179060 := by exact prefixLift 179060
  have htrace : WordTrace (prefixWord ++ tailWord_179060) baseStart_179060 baseEnd_179060 := by
    simpa [prefixWord, tailWord_179060, baseEnd_179060] using wordTrace_append hprefix tailTrace_179060
  have hstable : (prefixWord ++ tailWord_179060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179060).length < 2 ^ (prefixWord ++ tailWord_179060).sum := by decide
  have hdescent : baseEnd_179060 < baseStart_179060 := by decide
  rcases family_descends (prefixWord ++ tailWord_179060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179062 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_179062 : Nat := 118140960795 + 179062 * 2 ^ 59
def prefixEnd_179062 : Nat := 4983230072969 + 3 ^ 40 * 179062 * 2
def baseEnd_179062 : Nat := 81728775960429913601347

theorem tailTrace_179062 : CollatzResearch.WordTrace tailWord_179062 prefixEnd_179062 81728775960429913601347 := by
  unfold tailWord_179062
  simp only [CollatzResearch.WordTrace]
  refine ⟨408182979831026887500215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4353951784864286800002293 408182979831026887500215)
  ·
    refine ⟨612274469746540331250323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408182979831026887500215 612274469746540331250323)
    ·
      refine ⟨918411704619810496875485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612274469746540331250323 918411704619810496875485)
      ·
        refine ⟨344404389232428936328307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 918411704619810496875485 344404389232428936328307)
        ·
          refine ⟨516606583848643404492461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344404389232428936328307 516606583848643404492461)
          ·
            refine ⟨193727468943241276684673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516606583848643404492461 193727468943241276684673)
            ·
              refine ⟨145295601707430957513505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193727468943241276684673 145295601707430957513505)
              ·
                refine ⟨108971701280573218135129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145295601707430957513505 108971701280573218135129)
                ·
                  refine ⟨81728775960429913601347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108971701280573218135129 81728775960429913601347)
                  ·
                    rfl

theorem cell20_179062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_179062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179062 prefixEnd_179062 := by exact prefixLift 179062
  have htrace : WordTrace (prefixWord ++ tailWord_179062) baseStart_179062 baseEnd_179062 := by
    simpa [prefixWord, tailWord_179062, baseEnd_179062] using wordTrace_append hprefix tailTrace_179062
  have hstable : (prefixWord ++ tailWord_179062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179062).length < 2 ^ (prefixWord ++ tailWord_179062).sum := by decide
  have hdescent : baseEnd_179062 < baseStart_179062 := by decide
  rcases family_descends (prefixWord ++ tailWord_179062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179077 : List Nat := [1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_179077 : Nat := 118140960795 + 179077 * 2 ^ 59
def prefixEnd_179077 : Nat := 4983230072969 + 3 ^ 40 * 179077 * 2
def baseEnd_179077 : Nat := 27245207456385509367095

theorem tailTrace_179077 : CollatzResearch.WordTrace tailWord_179077 prefixEnd_179077 27245207456385509367095 := by
  unfold tailWord_179077
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531474772242087761799485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4354316514828058507866323 6531474772242087761799485)
  ·
    refine ⟨2449303039590782910674807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6531474772242087761799485 2449303039590782910674807)
    ·
      refine ⟨3673954559386174366012211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2449303039590782910674807 3673954559386174366012211)
      ·
        refine ⟨5510931839079261549018317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673954559386174366012211 5510931839079261549018317)
        ·
          refine ⟨2066599439654723080881869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5510931839079261549018317 2066599439654723080881869)
          ·
            refine ⟨774974789870521155330701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2066599439654723080881869 774974789870521155330701)
            ·
              refine ⟨290615546201445433249013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 774974789870521155330701 290615546201445433249013)
              ·
                refine ⟨27245207456385509367095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290615546201445433249013 27245207456385509367095)
                ·
                  rfl

theorem cell20_179077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_179077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179077 prefixEnd_179077 := by exact prefixLift 179077
  have htrace : WordTrace (prefixWord ++ tailWord_179077) baseStart_179077 baseEnd_179077 := by
    simpa [prefixWord, tailWord_179077, baseEnd_179077] using wordTrace_append hprefix tailTrace_179077
  have hstable : (prefixWord ++ tailWord_179077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179077).length < 2 ^ (prefixWord ++ tailWord_179077).sum := by decide
  have hdescent : baseEnd_179077 < baseStart_179077 := by decide
  rcases family_descends (prefixWord ++ tailWord_179077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179125 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 2]
def baseStart_179125 : Nat := 118140960795 + 179125 * 2 ^ 59
def prefixEnd_179125 : Nat := 4983230072969 + 3 ^ 40 * 179125 * 2
def baseEnd_179125 : Nat := 81757530877081694501089

theorem tailTrace_179125 : CollatzResearch.WordTrace tailWord_179125 prefixEnd_179125 81757530877081694501089 := by
  unfold tailWord_179125
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533225476068191959546829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4355483650712127973031219 6533225476068191959546829)
  ·
    refine ⟨2449959553525571984830061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6533225476068191959546829 2449959553525571984830061)
    ·
      refine ⟨918734832572089494311273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2449959553525571984830061 918734832572089494311273)
      ·
        refine ⟨689051124429067120733455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918734832572089494311273 689051124429067120733455)
        ·
          refine ⟨1033576686643600681100183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689051124429067120733455 1033576686643600681100183)
          ·
            refine ⟨1550365029965401021650275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033576686643600681100183 1550365029965401021650275)
            ·
              refine ⟨2325547544948101532475413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550365029965401021650275 2325547544948101532475413)
              ·
                refine ⟨109010041169442259334785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2325547544948101532475413 109010041169442259334785)
                ·
                  refine ⟨81757530877081694501089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109010041169442259334785 81757530877081694501089)
                  ·
                    rfl

theorem cell20_179125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_179125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179125 prefixEnd_179125 := by exact prefixLift 179125
  have htrace : WordTrace (prefixWord ++ tailWord_179125) baseStart_179125 baseEnd_179125 := by
    simpa [prefixWord, tailWord_179125, baseEnd_179125] using wordTrace_append hprefix tailTrace_179125
  have hstable : (prefixWord ++ tailWord_179125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179125).length < 2 ^ (prefixWord ++ tailWord_179125).sum := by decide
  have hdescent : baseEnd_179125 < baseStart_179125 := by decide
  rcases family_descends (prefixWord ++ tailWord_179125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179160 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_179160 : Nat := 118140960795 + 179160 * 2 ^ 59
def prefixEnd_179160 : Nat := 4983230072969 + 3 ^ 40 * 179160 * 2
def baseEnd_179160 : Nat := 81773505830777128334279

theorem tailTrace_179160 : CollatzResearch.WordTrace tailWord_179160 prefixEnd_179160 81773505830777128334279 := by
  unfold tailWord_179160
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267251015470696468535467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4356334687294261958047289 3267251015470696468535467)
  ·
    refine ⟨4900876523206044702803201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3267251015470696468535467 4900876523206044702803201)
    ·
      refine ⟨3675657392404533527102401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4900876523206044702803201 3675657392404533527102401)
      ·
        refine ⟨2756743044303400145326801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3675657392404533527102401 2756743044303400145326801)
        ·
          refine ⟨2067557283227550108995101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756743044303400145326801 2067557283227550108995101)
          ·
            refine ⟨775333981210331290873163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2067557283227550108995101 775333981210331290873163)
            ·
              refine ⟨1163000971815496936309745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775333981210331290873163 1163000971815496936309745)
              ·
                refine ⟨872250728861622702232309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163000971815496936309745 872250728861622702232309)
                ·
                  refine ⟨81773505830777128334279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872250728861622702232309 81773505830777128334279)
                  ·
                    rfl

theorem cell20_179160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_179160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179160 prefixEnd_179160 := by exact prefixLift 179160
  have htrace : WordTrace (prefixWord ++ tailWord_179160) baseStart_179160 baseEnd_179160 := by
    simpa [prefixWord, tailWord_179160, baseEnd_179160] using wordTrace_append hprefix tailTrace_179160
  have hstable : (prefixWord ++ tailWord_179160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179160).length < 2 ^ (prefixWord ++ tailWord_179160).sum := by decide
  have hdescent : baseEnd_179160 < baseStart_179160 := by decide
  rcases family_descends (prefixWord ++ tailWord_179160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179170 : List Nat := [3, 3, 3, 1, 1, 1, 8]
def baseStart_179170 : Nat := 118140960795 + 179170 * 2 ^ 59
def prefixEnd_179170 : Nat := 4983230072969 + 3 ^ 40 * 179170 * 2
def baseEnd_179170 : Nat := 9086452233695726444545

theorem tailTrace_179170 : CollatzResearch.WordTrace tailWord_179170 prefixEnd_179170 9086452233695726444545 := by
  unfold tailWord_179170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633716690226291161233741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4356577840603443096623309 1633716690226291161233741)
  ·
    refine ⟨612643758834859185462653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1633716690226291161233741 612643758834859185462653)
    ·
      refine ⟨229741409563072194548495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 612643758834859185462653 229741409563072194548495)
      ·
        refine ⟨344612114344608291822743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229741409563072194548495 344612114344608291822743)
        ·
          refine ⟨516918171516912437734115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344612114344608291822743 516918171516912437734115)
          ·
            refine ⟨775377257275368656601173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516918171516912437734115 775377257275368656601173)
            ·
              refine ⟨9086452233695726444545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 775377257275368656601173 9086452233695726444545)
              ·
                rfl

theorem cell20_179170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_179170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179170 prefixEnd_179170 := by exact prefixLift 179170
  have htrace : WordTrace (prefixWord ++ tailWord_179170) baseStart_179170 baseEnd_179170 := by
    simpa [prefixWord, tailWord_179170, baseEnd_179170] using wordTrace_append hprefix tailTrace_179170
  have hstable : (prefixWord ++ tailWord_179170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179170).length < 2 ^ (prefixWord ++ tailWord_179170).sum := by decide
  have hdescent : baseEnd_179170 < baseStart_179170 := by decide
  rcases family_descends (prefixWord ++ tailWord_179170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179205 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_179205 : Nat := 118140960795 + 179205 * 2 ^ 59
def prefixEnd_179205 : Nat := 4983230072969 + 3 ^ 40 * 179205 * 2
def baseEnd_179205 : Nat := 81794045056956971834095

theorem tailTrace_179205 : CollatzResearch.WordTrace tailWord_179205 prefixEnd_179205 81794045056956971834095 := by
  unfold tailWord_179205
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536143315778365622459069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4357428877185577081639379 6536143315778365622459069)
  ·
    refine ⟨2451053743416887108422151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6536143315778365622459069 2451053743416887108422151)
    ·
      refine ⟨3676580615125330662633227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451053743416887108422151 3676580615125330662633227)
      ·
        refine ⟨5514870922687995993949841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676580615125330662633227 5514870922687995993949841)
        ·
          refine ⟨4136153192015996995462381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5514870922687995993949841 4136153192015996995462381)
          ·
            refine ⟨1551057447005998873298393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4136153192015996995462381 1551057447005998873298393)
            ·
              refine ⟨1163293085254499154973795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551057447005998873298393 1163293085254499154973795)
              ·
                refine ⟨1744939627881748732460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163293085254499154973795 1744939627881748732460693)
                ·
                  refine ⟨81794045056956971834095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1744939627881748732460693 81794045056956971834095)
                  ·
                    rfl

theorem cell20_179205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_179205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179205 prefixEnd_179205 := by exact prefixLift 179205
  have htrace : WordTrace (prefixWord ++ tailWord_179205) baseStart_179205 baseEnd_179205 := by
    simpa [prefixWord, tailWord_179205, baseEnd_179205] using wordTrace_append hprefix tailTrace_179205
  have hstable : (prefixWord ++ tailWord_179205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179205).length < 2 ^ (prefixWord ++ tailWord_179205).sum := by decide
  have hdescent : baseEnd_179205 < baseStart_179205 := by decide
  rcases family_descends (prefixWord ++ tailWord_179205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179229 : List Nat := [1, 4, 2, 2, 3, 8]
def baseStart_179229 : Nat := 118140960795 + 179229 * 2 ^ 59
def prefixEnd_179229 : Nat := 4983230072969 + 3 ^ 40 * 179229 * 2
def baseEnd_179229 : Nat := 3029814789293316853111

theorem tailTrace_179229 : CollatzResearch.WordTrace tailWord_179229 prefixEnd_179229 3029814789293316853111 := by
  unfold tailWord_179229
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537018667691417721332741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4358012445127611814221827 6537018667691417721332741)
  ·
    refine ⟨1225691000192140822749889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6537018667691417721332741 1225691000192140822749889)
    ·
      refine ⟨919268250144105617062417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1225691000192140822749889 919268250144105617062417)
      ·
        refine ⟨689451187608079212796813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 919268250144105617062417 689451187608079212796813)
        ·
          refine ⟨258544195353029704798805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689451187608079212796813 258544195353029704798805)
          ·
            refine ⟨3029814789293316853111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 258544195353029704798805 3029814789293316853111)
            ·
              rfl

theorem cell20_179229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 8].length) (baseStart_179229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179229 prefixEnd_179229 := by exact prefixLift 179229
  have htrace : WordTrace (prefixWord ++ tailWord_179229) baseStart_179229 baseEnd_179229 := by
    simpa [prefixWord, tailWord_179229, baseEnd_179229] using wordTrace_append hprefix tailTrace_179229
  have hstable : (prefixWord ++ tailWord_179229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179229).length < 2 ^ (prefixWord ++ tailWord_179229).sum := by decide
  have hdescent : baseEnd_179229 < baseStart_179229 := by decide
  rcases family_descends (prefixWord ++ tailWord_179229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179243 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_179243 : Nat := 118140960795 + 179243 * 2 ^ 59
def prefixEnd_179243 : Nat := 4983230072969 + 3 ^ 40 * 179243 * 2
def baseEnd_179243 : Nat := 81811389292397728567273

theorem tailTrace_179243 : CollatzResearch.WordTrace tailWord_179243 prefixEnd_179243 81811389292397728567273 := by
  unfold tailWord_179243
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537529289640698112342383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4358352859760465408228255 6537529289640698112342383)
  ·
    refine ⟨9806293934461047168513575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6537529289640698112342383 9806293934461047168513575)
    ·
      refine ⟨14709440901691570752770363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806293934461047168513575 14709440901691570752770363)
      ·
        refine ⟨22064161352537356129155545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14709440901691570752770363 22064161352537356129155545)
        ·
          refine ⟨16548121014403017096866659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22064161352537356129155545 16548121014403017096866659)
          ·
            refine ⟨24822181521604525645299989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16548121014403017096866659 24822181521604525645299989)
            ·
              refine ⟨1163539758825212139623437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24822181521604525645299989 1163539758825212139623437)
              ·
                refine ⟨436327409559454552358789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163539758825212139623437 436327409559454552358789)
                ·
                  refine ⟨81811389292397728567273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436327409559454552358789 81811389292397728567273)
                  ·
                    rfl

theorem cell20_179243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_179243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179243 prefixEnd_179243 := by exact prefixLift 179243
  have htrace : WordTrace (prefixWord ++ tailWord_179243) baseStart_179243 baseEnd_179243 := by
    simpa [prefixWord, tailWord_179243, baseEnd_179243] using wordTrace_append hprefix tailTrace_179243
  have hstable : (prefixWord ++ tailWord_179243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179243).length < 2 ^ (prefixWord ++ tailWord_179243).sum := by decide
  have hdescent : baseEnd_179243 < baseStart_179243 := by decide
  rcases family_descends (prefixWord ++ tailWord_179243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179260 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_179260 : Nat := 118140960795 + 179260 * 2 ^ 59
def prefixEnd_179260 : Nat := 4983230072969 + 3 ^ 40 * 179260 * 2
def baseEnd_179260 : Nat := 81819148555621225000537

theorem tailTrace_179260 : CollatzResearch.WordTrace tailWord_179260 prefixEnd_179260 81819148555621225000537 := by
  unfold tailWord_179260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269074665289555007855617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4358766220386073343807489 3269074665289555007855617)
  ·
    refine ⟨2451805998967166255891713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3269074665289555007855617 2451805998967166255891713)
    ·
      refine ⟨1838854499225374691918785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2451805998967166255891713 1838854499225374691918785)
      ·
        refine ⟨1379140874419031018939089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1838854499225374691918785 1379140874419031018939089)
        ·
          refine ⟨1034355655814273264204317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379140874419031018939089 1034355655814273264204317)
          ·
            refine ⟨387883370930352474076619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1034355655814273264204317 387883370930352474076619)
            ·
              refine ⟨581825056395528711114929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387883370930352474076619 581825056395528711114929)
              ·
                refine ⟨436368792296646533336197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581825056395528711114929 436368792296646533336197)
                ·
                  refine ⟨81819148555621225000537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436368792296646533336197 81819148555621225000537)
                  ·
                    rfl

theorem cell20_179260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_179260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179260 prefixEnd_179260 := by exact prefixLift 179260
  have htrace : WordTrace (prefixWord ++ tailWord_179260) baseStart_179260 baseEnd_179260 := by
    simpa [prefixWord, tailWord_179260, baseEnd_179260] using wordTrace_append hprefix tailTrace_179260
  have hstable : (prefixWord ++ tailWord_179260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179260).length < 2 ^ (prefixWord ++ tailWord_179260).sum := by decide
  have hdescent : baseEnd_179260 < baseStart_179260 := by decide
  rcases family_descends (prefixWord ++ tailWord_179260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179267 : List Nat := [1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_179267 : Nat := 118140960795 + 179267 * 2 ^ 59
def prefixEnd_179267 : Nat := 4983230072969 + 3 ^ 40 * 179267 * 2
def baseEnd_179267 : Nat := 27274114515453437255725

theorem tailTrace_179267 : CollatzResearch.WordTrace tailWord_179267 prefixEnd_179267 27274114515453437255725 := by
  unfold tailWord_179267
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538404641553750211216055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4358936427702500140810703 6538404641553750211216055)
  ·
    refine ⟨9807606962330625316824083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6538404641553750211216055 9807606962330625316824083)
    ·
      refine ⟨14711410443495937975236125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9807606962330625316824083 14711410443495937975236125)
      ·
        refine ⟨5516778916310976740713547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14711410443495937975236125 5516778916310976740713547)
        ·
          refine ⟨8275168374466465111070321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516778916310976740713547 8275168374466465111070321)
          ·
            refine ⟨6206376280849848833302741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8275168374466465111070321 6206376280849848833302741)
            ·
              refine ⟨145461944082418332030533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6206376280849848833302741 145461944082418332030533)
              ·
                refine ⟨27274114515453437255725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145461944082418332030533 27274114515453437255725)
                ·
                  rfl

theorem cell20_179267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_179267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179267 prefixEnd_179267 := by exact prefixLift 179267
  have htrace : WordTrace (prefixWord ++ tailWord_179267) baseStart_179267 baseEnd_179267 := by
    simpa [prefixWord, tailWord_179267, baseEnd_179267] using wordTrace_append hprefix tailTrace_179267
  have hstable : (prefixWord ++ tailWord_179267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179267).length < 2 ^ (prefixWord ++ tailWord_179267).sum := by decide
  have hdescent : baseEnd_179267 < baseStart_179267 := by decide
  rcases family_descends (prefixWord ++ tailWord_179267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179288 : List Nat := [2, 1, 2, 2, 1, 3, 9]
def baseStart_179288 : Nat := 118140960795 + 179288 * 2 ^ 59
def prefixEnd_179288 : Nat := 4983230072969 + 3 ^ 40 * 179288 * 2
def baseEnd_179288 : Nat := 9092436502064174674121

theorem tailTrace_179288 : CollatzResearch.WordTrace tailWord_179288 prefixEnd_179288 9092436502064174674121 := by
  unfold tailWord_179288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269585287238835398865259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4359447049651780531820345 3269585287238835398865259)
  ·
    refine ⟨4904377930858253098297889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269585287238835398865259 4904377930858253098297889)
    ·
      refine ⟨3678283448143689823723417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4904377930858253098297889 3678283448143689823723417)
      ·
        refine ⟨2758712586107767367792563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3678283448143689823723417 2758712586107767367792563)
        ·
          refine ⟨4138068879161651051688845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758712586107767367792563 4138068879161651051688845)
          ·
            refine ⟨1551775829685619144383317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4138068879161651051688845 1551775829685619144383317)
            ·
              refine ⟨9092436502064174674121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1551775829685619144383317 9092436502064174674121)
              ·
                rfl

theorem cell20_179288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_179288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179288 prefixEnd_179288 := by exact prefixLift 179288
  have htrace : WordTrace (prefixWord ++ tailWord_179288) baseStart_179288 baseEnd_179288 := by
    simpa [prefixWord, tailWord_179288, baseEnd_179288] using wordTrace_append hprefix tailTrace_179288
  have hstable : (prefixWord ++ tailWord_179288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179288).length < 2 ^ (prefixWord ++ tailWord_179288).sum := by decide
  have hdescent : baseEnd_179288 < baseStart_179288 := by decide
  rcases family_descends (prefixWord ++ tailWord_179288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179294 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_179294 : Nat := 118140960795 + 179294 * 2 ^ 59
def prefixEnd_179294 : Nat := 4983230072969 + 3 ^ 40 * 179294 * 2
def baseEnd_179294 : Nat := 81834667082068217867065

theorem tailTrace_179294 : CollatzResearch.WordTrace tailWord_179294 prefixEnd_179294 81834667082068217867065 := by
  unfold tailWord_179294
  simp only [CollatzResearch.WordTrace]
  refine ⟨817423676556991727806117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4359592941637289214965957 817423676556991727806117)
  ·
    refine ⟨153266939354435948963647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 817423676556991727806117 153266939354435948963647)
    ·
      refine ⟨229900409031653923445471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153266939354435948963647 229900409031653923445471)
      ·
        refine ⟨344850613547480885168207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229900409031653923445471 344850613547480885168207)
        ·
          refine ⟨517275920321221327752311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344850613547480885168207 517275920321221327752311)
          ·
            refine ⟨775913880481831991628467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517275920321221327752311 775913880481831991628467)
            ·
              refine ⟨1163870820722747987442701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775913880481831991628467 1163870820722747987442701)
              ·
                refine ⟨436451557771030495291013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163870820722747987442701 436451557771030495291013)
                ·
                  refine ⟨81834667082068217867065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436451557771030495291013 81834667082068217867065)
                  ·
                    rfl

theorem cell20_179294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_179294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179294 prefixEnd_179294 := by exact prefixLift 179294
  have htrace : WordTrace (prefixWord ++ tailWord_179294) baseStart_179294 baseEnd_179294 := by
    simpa [prefixWord, tailWord_179294, baseEnd_179294] using wordTrace_append hprefix tailTrace_179294
  have hstable : (prefixWord ++ tailWord_179294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179294).length < 2 ^ (prefixWord ++ tailWord_179294).sum := by decide
  have hdescent : baseEnd_179294 < baseStart_179294 := by decide
  rcases family_descends (prefixWord ++ tailWord_179294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179319 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_179319 : Nat := 118140960795 + 179319 * 2 ^ 59
def prefixEnd_179319 : Nat := 4983230072969 + 3 ^ 40 * 179319 * 2
def baseEnd_179319 : Nat := 81846077763279242033629

theorem tailTrace_179319 : CollatzResearch.WordTrace tailWord_179319 prefixEnd_179319 81846077763279242033629 := by
  unfold tailWord_179319
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540301237365363092109011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4360200824910242061406007 6540301237365363092109011)
  ·
    refine ⟨9810451856048044638163517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540301237365363092109011 9810451856048044638163517)
    ·
      refine ⟨3678919446018016739311319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9810451856048044638163517 3678919446018016739311319)
      ·
        refine ⟨5518379169027025108966979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678919446018016739311319 5518379169027025108966979)
        ·
          refine ⟨8277568753540537663450469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518379169027025108966979 8277568753540537663450469)
          ·
            refine ⟨1552044141288850811896963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8277568753540537663450469 1552044141288850811896963)
            ·
              refine ⟨2328066211933276217845445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552044141288850811896963 2328066211933276217845445)
              ·
                refine ⟨436512414737489290846021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2328066211933276217845445 436512414737489290846021)
                ·
                  refine ⟨81846077763279242033629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436512414737489290846021 81846077763279242033629)
                  ·
                    rfl

theorem cell20_179319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_179319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179319 prefixEnd_179319 := by exact prefixLift 179319
  have htrace : WordTrace (prefixWord ++ tailWord_179319) baseStart_179319 baseEnd_179319 := by
    simpa [prefixWord, tailWord_179319, baseEnd_179319] using wordTrace_append hprefix tailTrace_179319
  have hstable : (prefixWord ++ tailWord_179319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179319).length < 2 ^ (prefixWord ++ tailWord_179319).sum := by decide
  have hdescent : baseEnd_179319 < baseStart_179319 := by decide
  rcases family_descends (prefixWord ++ tailWord_179319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179332 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_179332 : Nat := 118140960795 + 179332 * 2 ^ 59
def prefixEnd_179332 : Nat := 4983230072969 + 3 ^ 40 * 179332 * 2
def baseEnd_179332 : Nat := 81852011317508974600243

theorem tailTrace_179332 : CollatzResearch.WordTrace tailWord_179332 prefixEnd_179332 81852011317508974600243 := by
  unfold tailWord_179332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270387693159133156166125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4360516924212177541554833 3270387693159133156166125)
  ·
    refine ⟨1226395384934674933562297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3270387693159133156166125 1226395384934674933562297)
    ·
      refine ⟨919796538701006200171723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1226395384934674933562297 919796538701006200171723)
      ·
        refine ⟨1379694808051509300257585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919796538701006200171723 1379694808051509300257585)
        ·
          refine ⟨1034771106038631975193189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379694808051509300257585 1034771106038631975193189)
          ·
            refine ⟨194019582382243495348723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1034771106038631975193189 194019582382243495348723)
            ·
              refine ⟨291029373573365243023085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194019582382243495348723 291029373573365243023085)
              ·
                refine ⟨109136015090011966133657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291029373573365243023085 109136015090011966133657)
                ·
                  refine ⟨81852011317508974600243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109136015090011966133657 81852011317508974600243)
                  ·
                    rfl

theorem cell20_179332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_179332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179332 prefixEnd_179332 := by exact prefixLift 179332
  have htrace : WordTrace (prefixWord ++ tailWord_179332) baseStart_179332 baseEnd_179332 := by
    simpa [prefixWord, tailWord_179332, baseEnd_179332] using wordTrace_append hprefix tailTrace_179332
  have hstable : (prefixWord ++ tailWord_179332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179332).length < 2 ^ (prefixWord ++ tailWord_179332).sum := by decide
  have hdescent : baseEnd_179332 < baseStart_179332 := by decide
  rcases family_descends (prefixWord ++ tailWord_179332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179402 : List Nat := [3, 1, 2, 1, 3, 10]
def baseStart_179402 : Nat := 118140960795 + 179402 * 2 ^ 59
def prefixEnd_179402 : Nat := 4983230072969 + 3 ^ 40 * 179402 * 2
def baseEnd_179402 : Nat := 3032739304625920083949

theorem tailTrace_179402 : CollatzResearch.WordTrace tailWord_179402 prefixEnd_179402 3032739304625920083949 := by
  unfold tailWord_179402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635832124016167066845115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4362218997376445511586973 1635832124016167066845115)
  ·
    refine ⟨2453748186024250600267673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1635832124016167066845115 2453748186024250600267673)
    ·
      refine ⟨1840311139518187950200755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2453748186024250600267673 1840311139518187950200755)
      ·
        refine ⟨2760466709277281925301133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840311139518187950200755 2760466709277281925301133)
        ·
          refine ⟨1035175015978980721987925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2760466709277281925301133 1035175015978980721987925)
          ·
            refine ⟨3032739304625920083949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1035175015978980721987925 3032739304625920083949)
            ·
              rfl

theorem cell20_179402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 10].length) (baseStart_179402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179402 prefixEnd_179402 := by exact prefixLift 179402
  have htrace : WordTrace (prefixWord ++ tailWord_179402) baseStart_179402 baseEnd_179402 := by
    simpa [prefixWord, tailWord_179402, baseEnd_179402] using wordTrace_append hprefix tailTrace_179402
  have hstable : (prefixWord ++ tailWord_179402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179402).length < 2 ^ (prefixWord ++ tailWord_179402).sum := by decide
  have hdescent : baseEnd_179402 < baseStart_179402 := by decide
  rcases family_descends (prefixWord ++ tailWord_179402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179447 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_179447 : Nat := 118140960795 + 179447 * 2 ^ 59
def prefixEnd_179447 : Nat := 4983230072969 + 3 ^ 40 * 179447 * 2
def baseEnd_179447 : Nat := 81904500451079685766439

theorem tailTrace_179447 : CollatzResearch.WordTrace tailWord_179447 prefixEnd_179447 81904500451079685766439 := by
  unfold tailWord_179447
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544969780901640952768595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4363313187267760635179063 6544969780901640952768595)
  ·
    refine ⟨9817454671352461429152893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6544969780901640952768595 9817454671352461429152893)
    ·
      refine ⟨3681545501757173035932335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9817454671352461429152893 3681545501757173035932335)
      ·
        refine ⟨5522318252635759553898503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681545501757173035932335 5522318252635759553898503)
        ·
          refine ⟨8283477378953639330847755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5522318252635759553898503 8283477378953639330847755)
          ·
            refine ⟨12425216068430458996271633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8283477378953639330847755 12425216068430458996271633)
            ·
              refine ⟨9318912051322844247203725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12425216068430458996271633 9318912051322844247203725)
              ·
                refine ⟨3494592019246066592701397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9318912051322844247203725 3494592019246066592701397)
                ·
                  refine ⟨81904500451079685766439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3494592019246066592701397 81904500451079685766439)
                  ·
                    rfl

theorem cell20_179447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_179447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179447 prefixEnd_179447 := by exact prefixLift 179447
  have htrace : WordTrace (prefixWord ++ tailWord_179447) baseStart_179447 baseEnd_179447 := by
    simpa [prefixWord, tailWord_179447, baseEnd_179447] using wordTrace_append hprefix tailTrace_179447
  have hstable : (prefixWord ++ tailWord_179447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179447).length < 2 ^ (prefixWord ++ tailWord_179447).sum := by decide
  have hdescent : baseEnd_179447 < baseStart_179447 := by decide
  rcases family_descends (prefixWord ++ tailWord_179447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179460 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_179460 : Nat := 118140960795 + 179460 * 2 ^ 59
def prefixEnd_179460 : Nat := 4983230072969 + 3 ^ 40 * 179460 * 2
def baseEnd_179460 : Nat := 81910434005309418333053

theorem tailTrace_179460 : CollatzResearch.WordTrace tailWord_179460 prefixEnd_179460 81910434005309418333053 := by
  unfold tailWord_179460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272721964927272086495917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4363629286569696115327889 3272721964927272086495917)
  ·
    refine ⟨1227270736847727032435969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3272721964927272086495917 1227270736847727032435969)
    ·
      refine ⟨920453052635795274326977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1227270736847727032435969 920453052635795274326977)
      ·
        refine ⟨690339789476846455745233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920453052635795274326977 690339789476846455745233)
        ·
          refine ⟨517754842107634841808925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690339789476846455745233 517754842107634841808925)
          ·
            refine ⟨194158065790363065678347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517754842107634841808925 194158065790363065678347)
            ·
              refine ⟨291237098685544598517521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194158065790363065678347 291237098685544598517521)
              ·
                refine ⟨218427824014158448888141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291237098685544598517521 218427824014158448888141)
                ·
                  refine ⟨81910434005309418333053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218427824014158448888141 81910434005309418333053)
                  ·
                    rfl

theorem cell20_179460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_179460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179460 prefixEnd_179460 := by exact prefixLift 179460
  have htrace : WordTrace (prefixWord ++ tailWord_179460) baseStart_179460 baseEnd_179460 := by
    simpa [prefixWord, tailWord_179460, baseEnd_179460] using wordTrace_append hprefix tailTrace_179460
  have hstable : (prefixWord ++ tailWord_179460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179460).length < 2 ^ (prefixWord ++ tailWord_179460).sum := by decide
  have hdescent : baseEnd_179460 < baseStart_179460 := by decide
  rcases family_descends (prefixWord ++ tailWord_179460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179501 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 2]
def baseStart_179501 : Nat := 118140960795 + 179501 * 2 ^ 59
def prefixEnd_179501 : Nat := 4983230072969 + 3 ^ 40 * 179501 * 2
def baseEnd_179501 : Nat := 81929147522495497966219

theorem tailTrace_179501 : CollatzResearch.WordTrace tailWord_179501 prefixEnd_179501 81929147522495497966219 := by
  unfold tailWord_179501
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546939322706008175234357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4364626215137338783489571 6546939322706008175234357)
  ·
    refine ⟨613775561503688266428221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6546939322706008175234357 613775561503688266428221)
    ·
      refine ⟨230165835563883099910583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 613775561503688266428221 230165835563883099910583)
      ·
        refine ⟨345248753345824649865875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230165835563883099910583 345248753345824649865875)
        ·
          refine ⟨517873130018736974798813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345248753345824649865875 517873130018736974798813)
          ·
            refine ⟨194202423757026365549555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517873130018736974798813 194202423757026365549555)
            ·
              refine ⟨291303635635539548324333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194202423757026365549555 291303635635539548324333)
              ·
                refine ⟨109238863363327330621625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291303635635539548324333 109238863363327330621625)
                ·
                  refine ⟨81929147522495497966219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109238863363327330621625 81929147522495497966219)
                  ·
                    rfl

theorem cell20_179501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_179501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179501 prefixEnd_179501 := by exact prefixLift 179501
  have htrace : WordTrace (prefixWord ++ tailWord_179501) baseStart_179501 baseEnd_179501 := by
    simpa [prefixWord, tailWord_179501, baseEnd_179501] using wordTrace_append hprefix tailTrace_179501
  have hstable : (prefixWord ++ tailWord_179501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179501).length < 2 ^ (prefixWord ++ tailWord_179501).sum := by decide
  have hdescent : baseEnd_179501 < baseStart_179501 := by decide
  rcases family_descends (prefixWord ++ tailWord_179501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179505 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 2]
def baseStart_179505 : Nat := 118140960795 + 179505 * 2 ^ 59
def prefixEnd_179505 : Nat := 4983230072969 + 3 ^ 40 * 179505 * 2
def baseEnd_179505 : Nat := 81930973231489261832869

theorem tailTrace_179505 : CollatzResearch.WordTrace tailWord_179505 prefixEnd_179505 81930973231489261832869 := by
  unfold tailWord_179505
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547085214691516858379969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4364723476461011238919979 6547085214691516858379969)
  ·
    refine ⟨4910313911018637643784977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6547085214691516858379969 4910313911018637643784977)
    ·
      refine ⟨3682735433263978232838733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4910313911018637643784977 3682735433263978232838733)
      ·
        refine ⟨1381025787473991837314525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3682735433263978232838733 1381025787473991837314525)
        ·
          refine ⟨517884670302746938992947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1381025787473991837314525 517884670302746938992947)
          ·
            refine ⟨776827005454120408489421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517884670302746938992947 776827005454120408489421)
            ·
              refine ⟨291310127045295153183533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776827005454120408489421 291310127045295153183533)
              ·
                refine ⟨109241297641985682443825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291310127045295153183533 109241297641985682443825)
                ·
                  refine ⟨81930973231489261832869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109241297641985682443825 81930973231489261832869)
                  ·
                    rfl

theorem cell20_179505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_179505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179505 prefixEnd_179505 := by exact prefixLift 179505
  have htrace : WordTrace (prefixWord ++ tailWord_179505) baseStart_179505 baseEnd_179505 := by
    simpa [prefixWord, tailWord_179505, baseEnd_179505] using wordTrace_append hprefix tailTrace_179505
  have hstable : (prefixWord ++ tailWord_179505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179505).length < 2 ^ (prefixWord ++ tailWord_179505).sum := by decide
  have hdescent : baseEnd_179505 < baseStart_179505 := by decide
  rcases family_descends (prefixWord ++ tailWord_179505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179516 : List Nat := [2, 2, 2, 2, 1, 3, 8]
def baseStart_179516 : Nat := 118140960795 + 179516 * 2 ^ 59
def prefixEnd_179516 : Nat := 4983230072969 + 3 ^ 40 * 179516 * 2
def baseEnd_179516 : Nat := 9103999325691345829573

theorem tailTrace_179516 : CollatzResearch.WordTrace tailWord_179516 prefixEnd_179516 9103999325691345829573 := by
  unfold tailWord_179516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273743208825832868515201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4364990945101110491353601 3273743208825832868515201)
  ·
    refine ⟨2455307406619374651386401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3273743208825832868515201 2455307406619374651386401)
    ·
      refine ⟨1841480554964530988539801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2455307406619374651386401 1841480554964530988539801)
      ·
        refine ⟨1381110416223398241404851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1841480554964530988539801 1381110416223398241404851)
        ·
          refine ⟨2071665624335097362107277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381110416223398241404851 2071665624335097362107277)
          ·
            refine ⟨776874609125661510790229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2071665624335097362107277 776874609125661510790229)
            ·
              refine ⟨9103999325691345829573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 776874609125661510790229 9103999325691345829573)
              ·
                rfl

theorem cell20_179516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_179516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179516 prefixEnd_179516 := by exact prefixLift 179516
  have htrace : WordTrace (prefixWord ++ tailWord_179516) baseStart_179516 baseEnd_179516 := by
    simpa [prefixWord, tailWord_179516, baseEnd_179516] using wordTrace_append hprefix tailTrace_179516
  have hstable : (prefixWord ++ tailWord_179516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179516).length < 2 ^ (prefixWord ++ tailWord_179516).sum := by decide
  have hdescent : baseEnd_179516 < baseStart_179516 := by decide
  rcases family_descends (prefixWord ++ tailWord_179516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179561 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_179561 : Nat := 118140960795 + 179561 * 2 ^ 59
def prefixEnd_179561 : Nat := 4983230072969 + 3 ^ 40 * 179561 * 2
def baseEnd_179561 : Nat := 81956533157401955965973

theorem tailTrace_179561 : CollatzResearch.WordTrace tailWord_179561 prefixEnd_179561 81956533157401955965973 := by
  unfold tailWord_179561
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549127702488638422418537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4366085134992425614945691 6549127702488638422418537)
  ·
    refine ⟨4911845776866478816813903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6549127702488638422418537 4911845776866478816813903)
    ·
      refine ⟨7367768665299718225220855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4911845776866478816813903 7367768665299718225220855)
      ·
        refine ⟨11051652997949577337831283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367768665299718225220855 11051652997949577337831283)
        ·
          refine ⟨16577479496924366006746925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051652997949577337831283 16577479496924366006746925)
          ·
            refine ⟨6216554811346637252530097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16577479496924366006746925 6216554811346637252530097)
            ·
              refine ⟨4662416108509977939397573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6216554811346637252530097 4662416108509977939397573)
              ·
                refine ⟨874203020345620863637045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4662416108509977939397573 874203020345620863637045)
                ·
                  refine ⟨81956533157401955965973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874203020345620863637045 81956533157401955965973)
                  ·
                    rfl

theorem cell20_179561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_179561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179561 prefixEnd_179561 := by exact prefixLift 179561
  have htrace : WordTrace (prefixWord ++ tailWord_179561) baseStart_179561 baseEnd_179561 := by
    simpa [prefixWord, tailWord_179561, baseEnd_179561] using wordTrace_append hprefix tailTrace_179561
  have hstable : (prefixWord ++ tailWord_179561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179561).length < 2 ^ (prefixWord ++ tailWord_179561).sum := by decide
  have hdescent : baseEnd_179561 < baseStart_179561 := by decide
  rcases family_descends (prefixWord ++ tailWord_179561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179609 : List Nat := [1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_179609 : Nat := 118140960795 + 179609 * 2 ^ 59
def prefixEnd_179609 : Nat := 4983230072969 + 3 ^ 40 * 179609 * 2
def baseEnd_179609 : Nat := 27326147221775707455259

theorem tailTrace_179609 : CollatzResearch.WordTrace tailWord_179609 prefixEnd_179609 27326147221775707455259 := by
  unfold tailWord_179609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550878406314742620165881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4367252270876495080110587 6550878406314742620165881)
  ·
    refine ⟨4913158804736056965124411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6550878406314742620165881 4913158804736056965124411)
    ·
      refine ⟨7369738207104085447686617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913158804736056965124411 7369738207104085447686617)
      ·
        refine ⟨5527303655328064085764963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7369738207104085447686617 5527303655328064085764963)
        ·
          refine ⟨8290955482992096128647445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527303655328064085764963 8290955482992096128647445)
          ·
            refine ⟨388638538265254506030349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8290955482992096128647445 388638538265254506030349)
            ·
              refine ⟨145739451849470439761381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388638538265254506030349 145739451849470439761381)
              ·
                refine ⟨27326147221775707455259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145739451849470439761381 27326147221775707455259)
                ·
                  rfl

theorem cell20_179609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_179609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179609 prefixEnd_179609 := by exact prefixLift 179609
  have htrace : WordTrace (prefixWord ++ tailWord_179609) baseStart_179609 baseEnd_179609 := by
    simpa [prefixWord, tailWord_179609, baseEnd_179609] using wordTrace_append hprefix tailTrace_179609
  have hstable : (prefixWord ++ tailWord_179609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179609).length < 2 ^ (prefixWord ++ tailWord_179609).sum := by decide
  have hdescent : baseEnd_179609 < baseStart_179609 := by decide
  rcases family_descends (prefixWord ++ tailWord_179609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179623 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_179623 : Nat := 118140960795 + 179623 * 2 ^ 59
def prefixEnd_179623 : Nat := 4983230072969 + 3 ^ 40 * 179623 * 2
def baseEnd_179623 : Nat := 81984831646805295899053

theorem tailTrace_179623 : CollatzResearch.WordTrace tailWord_179623 prefixEnd_179623 81984831646805295899053 := by
  unfold tailWord_179623
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551389028264023011175523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4367592685509348674117015 6551389028264023011175523)
  ·
    refine ⟨9827083542396034516763285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6551389028264023011175523 9827083542396034516763285)
    ·
      refine ⟨460644541049814117973279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9827083542396034516763285 460644541049814117973279)
      ·
        refine ⟨690966811574721176959919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460644541049814117973279 690966811574721176959919)
        ·
          refine ⟨1036450217362081765439879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690966811574721176959919 1036450217362081765439879)
          ·
            refine ⟨1554675326043122648159819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036450217362081765439879 1554675326043122648159819)
            ·
              refine ⟨2332012989064683972239729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554675326043122648159819 2332012989064683972239729)
              ·
                refine ⟨1749009741798512979179797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332012989064683972239729 1749009741798512979179797)
                ·
                  refine ⟨81984831646805295899053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1749009741798512979179797 81984831646805295899053)
                  ·
                    rfl

theorem cell20_179623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_179623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179623 prefixEnd_179623 := by exact prefixLift 179623
  have htrace : WordTrace (prefixWord ++ tailWord_179623) baseStart_179623 baseEnd_179623 := by
    simpa [prefixWord, tailWord_179623, baseEnd_179623] using wordTrace_append hprefix tailTrace_179623
  have hstable : (prefixWord ++ tailWord_179623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179623).length < 2 ^ (prefixWord ++ tailWord_179623).sum := by decide
  have hdescent : baseEnd_179623 < baseStart_179623 := by decide
  rcases family_descends (prefixWord ++ tailWord_179623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179640 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_179640 : Nat := 118140960795 + 179640 * 2 ^ 59
def prefixEnd_179640 : Nat := 4983230072969 + 3 ^ 40 * 179640 * 2
def baseEnd_179640 : Nat := 81992590910028792332317

theorem tailTrace_179640 : CollatzResearch.WordTrace tailWord_179640 prefixEnd_179640 81992590910028792332317 := by
  unfold tailWord_179640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276004534601217457272187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4368006046134956609696249 3276004534601217457272187)
  ·
    refine ⟨4914006801901826185908281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276004534601217457272187 4914006801901826185908281)
    ·
      refine ⟨3685505101426369639431211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4914006801901826185908281 3685505101426369639431211)
      ·
        refine ⟨5528257652139554459146817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685505101426369639431211 5528257652139554459146817)
        ·
          refine ⟨4146193239104665844360113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5528257652139554459146817 4146193239104665844360113)
          ·
            refine ⟨3109644929328499383270085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146193239104665844360113 3109644929328499383270085)
            ·
              refine ⟨583058424249093634363141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3109644929328499383270085 583058424249093634363141)
              ·
                refine ⟨109323454546705056443089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583058424249093634363141 109323454546705056443089)
                ·
                  refine ⟨81992590910028792332317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109323454546705056443089 81992590910028792332317)
                  ·
                    rfl

theorem cell20_179640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_179640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179640 prefixEnd_179640 := by exact prefixLift 179640
  have htrace : WordTrace (prefixWord ++ tailWord_179640) baseStart_179640 baseEnd_179640 := by
    simpa [prefixWord, tailWord_179640, baseEnd_179640] using wordTrace_append hprefix tailTrace_179640
  have hstable : (prefixWord ++ tailWord_179640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179640).length < 2 ^ (prefixWord ++ tailWord_179640).sum := by decide
  have hdescent : baseEnd_179640 < baseStart_179640 := by decide
  rcases family_descends (prefixWord ++ tailWord_179640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179685 : List Nat := [1, 3, 1, 5, 1, 3, 6]
def baseStart_179685 : Nat := 118140960795 + 179685 * 2 ^ 59
def prefixEnd_179685 : Nat := 4983230072969 + 3 ^ 40 * 179685 * 2
def baseEnd_179685 : Nat := 9112570015134292870237

theorem tailTrace_179685 : CollatzResearch.WordTrace tailWord_179685 prefixEnd_179685 9112570015134292870237 := by
  unfold tailWord_179685
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553650354039407599932509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4369100236026271733288339 6553650354039407599932509)
  ·
    refine ⟨2457618882764777849974691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6553650354039407599932509 2457618882764777849974691)
    ·
      refine ⟨3686428324147166774962037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457618882764777849974691 3686428324147166774962037)
      ·
        refine ⟨345602655388796885152691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3686428324147166774962037 345602655388796885152691)
        ·
          refine ⟨518403983083195327729037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345602655388796885152691 518403983083195327729037)
          ·
            refine ⟨194401493656198247898389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518403983083195327729037 194401493656198247898389)
            ·
              refine ⟨9112570015134292870237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194401493656198247898389 9112570015134292870237)
              ·
                rfl

theorem cell20_179685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_179685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179685 prefixEnd_179685 := by exact prefixLift 179685
  have htrace : WordTrace (prefixWord ++ tailWord_179685) baseStart_179685 baseEnd_179685 := by
    simpa [prefixWord, tailWord_179685, baseEnd_179685] using wordTrace_append hprefix tailTrace_179685
  have hstable : (prefixWord ++ tailWord_179685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179685).length < 2 ^ (prefixWord ++ tailWord_179685).sum := by decide
  have hdescent : baseEnd_179685 < baseStart_179685 := by decide
  rcases family_descends (prefixWord ++ tailWord_179685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179706 : List Nat := [3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_179706 : Nat := 118140960795 + 179706 * 2 ^ 59
def prefixEnd_179706 : Nat := 4983230072969 + 3 ^ 40 * 179706 * 2
def baseEnd_179706 : Nat := 27340905036141965377349

theorem tailTrace_179706 : CollatzResearch.WordTrace tailWord_179706 prefixEnd_179706 27340905036141965377349 := by
  unfold tailWord_179706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638604071740832046611743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4369610857975552124297981 1638604071740832046611743)
  ·
    refine ⟨2457906107611248069917615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1638604071740832046611743 2457906107611248069917615)
    ·
      refine ⟨3686859161416872104876423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457906107611248069917615 3686859161416872104876423)
      ·
        refine ⟨5530288742125308157314635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686859161416872104876423 5530288742125308157314635)
        ·
          refine ⟨8295433113187962235971953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530288742125308157314635 8295433113187962235971953)
          ·
            refine ⟨6221574834890971676978965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8295433113187962235971953 6221574834890971676978965)
            ·
              refine ⟨291636320385514297358389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6221574834890971676978965 291636320385514297358389)
              ·
                refine ⟨27340905036141965377349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291636320385514297358389 27340905036141965377349)
                ·
                  rfl

theorem cell20_179706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_179706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179706 prefixEnd_179706 := by exact prefixLift 179706
  have htrace : WordTrace (prefixWord ++ tailWord_179706) baseStart_179706 baseEnd_179706 := by
    simpa [prefixWord, tailWord_179706, baseEnd_179706] using wordTrace_append hprefix tailTrace_179706
  have hstable : (prefixWord ++ tailWord_179706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179706).length < 2 ^ (prefixWord ++ tailWord_179706).sum := by decide
  have hdescent : baseEnd_179706 < baseStart_179706 := by decide
  rcases family_descends (prefixWord ++ tailWord_179706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179709 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 3]
def baseStart_179709 : Nat := 118140960795 + 179709 * 2 ^ 59
def prefixEnd_179709 : Nat := 4983230072969 + 3 ^ 40 * 179709 * 2
def baseEnd_179709 : Nat := 82024084390171219032035

theorem tailTrace_179709 : CollatzResearch.WordTrace tailWord_179709 prefixEnd_179709 82024084390171219032035 := by
  unfold tailWord_179709
  simp only [CollatzResearch.WordTrace]
  refine ⟨6554525705952459698806181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4369683803968306465870787 6554525705952459698806181)
  ·
    refine ⟨1228973569866086193526159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6554525705952459698806181 1228973569866086193526159)
    ·
      refine ⟨1843460354799129290289239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228973569866086193526159 1843460354799129290289239)
      ·
        refine ⟨2765190532198693935433859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843460354799129290289239 2765190532198693935433859)
        ·
          refine ⟨4147785798298040903150789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2765190532198693935433859 4147785798298040903150789)
          ·
            refine ⟨777709837180882669340773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4147785798298040903150789 777709837180882669340773)
            ·
              refine ⟨145820594471415500501395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 777709837180882669340773 145820594471415500501395)
              ·
                refine ⟨218730891707123250752093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145820594471415500501395 218730891707123250752093)
                ·
                  refine ⟨82024084390171219032035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218730891707123250752093 82024084390171219032035)
                  ·
                    rfl

theorem cell20_179709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_179709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179709 prefixEnd_179709 := by exact prefixLift 179709
  have htrace : WordTrace (prefixWord ++ tailWord_179709) baseStart_179709 baseEnd_179709 := by
    simpa [prefixWord, tailWord_179709, baseEnd_179709] using wordTrace_append hprefix tailTrace_179709
  have hstable : (prefixWord ++ tailWord_179709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179709).length < 2 ^ (prefixWord ++ tailWord_179709).sum := by decide
  have hdescent : baseEnd_179709 < baseStart_179709 := by decide
  rcases family_descends (prefixWord ++ tailWord_179709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179742 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_179742 : Nat := 118140960795 + 179742 * 2 ^ 59
def prefixEnd_179742 : Nat := 4983230072969 + 3 ^ 40 * 179742 * 2
def baseEnd_179742 : Nat := 82039146489369770931901

theorem tailTrace_179742 : CollatzResearch.WordTrace tailWord_179742 prefixEnd_179742 82039146489369770931901 := by
  unfold tailWord_179742
  simp only [CollatzResearch.WordTrace]
  refine ⟨819466164354113291844685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4370486209888604223171653 819466164354113291844685)
  ·
    refine ⟨307299811632792484441757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 819466164354113291844685 307299811632792484441757)
    ·
      refine ⟨115237429362297181665659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307299811632792484441757 115237429362297181665659)
      ·
        refine ⟨172856144043445772498489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115237429362297181665659 172856144043445772498489)
        ·
          refine ⟨129642108032584329373867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172856144043445772498489 129642108032584329373867)
          ·
            refine ⟨194463162048876494060801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129642108032584329373867 194463162048876494060801)
            ·
              refine ⟨145847371536657370545601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194463162048876494060801 145847371536657370545601)
              ·
                refine ⟨109385528652493027909201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145847371536657370545601 109385528652493027909201)
                ·
                  refine ⟨82039146489369770931901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109385528652493027909201 82039146489369770931901)
                  ·
                    rfl

theorem cell20_179742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_179742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179742 prefixEnd_179742 := by exact prefixLift 179742
  have htrace : WordTrace (prefixWord ++ tailWord_179742) baseStart_179742 baseEnd_179742 := by
    simpa [prefixWord, tailWord_179742, baseEnd_179742] using wordTrace_append hprefix tailTrace_179742
  have hstable : (prefixWord ++ tailWord_179742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179742).length < 2 ^ (prefixWord ++ tailWord_179742).sum := by decide
  have hdescent : baseEnd_179742 < baseStart_179742 := by decide
  rcases family_descends (prefixWord ++ tailWord_179742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179744 : List Nat := [2, 1, 1, 6, 1, 9]
def baseStart_179744 : Nat := 118140960795 + 179744 * 2 ^ 59
def prefixEnd_179744 : Nat := 4983230072969 + 3 ^ 40 * 179744 * 2
def baseEnd_179744 : Nat := 3038520716439505661675

theorem tailTrace_179744 : CollatzResearch.WordTrace tailWord_179744 prefixEnd_179744 3038520716439505661675 := by
  unfold tailWord_179744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277901130412830338165143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4370534840550440450886857 3277901130412830338165143)
  ·
    refine ⟨4916851695619245507247715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277901130412830338165143 4916851695619245507247715)
    ·
      refine ⟨7375277543428868260871573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916851695619245507247715 7375277543428868260871573)
      ·
        refine ⟨345716134848228199728355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7375277543428868260871573 345716134848228199728355)
        ·
          refine ⟨518574202272342299592533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345716134848228199728355 518574202272342299592533)
          ·
            refine ⟨3038520716439505661675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 518574202272342299592533 3038520716439505661675)
            ·
              rfl

theorem cell20_179744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 9].length) (baseStart_179744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179744 prefixEnd_179744 := by exact prefixLift 179744
  have htrace : WordTrace (prefixWord ++ tailWord_179744) baseStart_179744 baseEnd_179744 := by
    simpa [prefixWord, tailWord_179744, baseEnd_179744] using wordTrace_append hprefix tailTrace_179744
  have hstable : (prefixWord ++ tailWord_179744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179744).length < 2 ^ (prefixWord ++ tailWord_179744).sum := by decide
  have hdescent : baseEnd_179744 < baseStart_179744 := by decide
  rcases family_descends (prefixWord ++ tailWord_179744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179747 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_179747 : Nat := 118140960795 + 179747 * 2 ^ 59
def prefixEnd_179747 : Nat := 4983230072969 + 3 ^ 40 * 179747 * 2
def baseEnd_179747 : Nat := 82041428625611975765213

theorem tailTrace_179747 : CollatzResearch.WordTrace tailWord_179747 prefixEnd_179747 82041428625611975765213 := by
  unfold tailWord_179747
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555911679814792188689495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4370607786543194792459663 6555911679814792188689495)
  ·
    refine ⟨9833867519722188283034243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6555911679814792188689495 9833867519722188283034243)
    ·
      refine ⟨14750801279583282424551365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9833867519722188283034243 14750801279583282424551365)
      ·
        refine ⟨2765775239921865454603381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14750801279583282424551365 2765775239921865454603381)
        ·
          refine ⟨259291428742674886369067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2765775239921865454603381 259291428742674886369067)
          ·
            refine ⟨388937143114012329553601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259291428742674886369067 388937143114012329553601)
            ·
              refine ⟨291702857335509247165201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388937143114012329553601 291702857335509247165201)
              ·
                refine ⟨218777143001631935373901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291702857335509247165201 218777143001631935373901)
                ·
                  refine ⟨82041428625611975765213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218777143001631935373901 82041428625611975765213)
                  ·
                    rfl

theorem cell20_179747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_179747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179747 prefixEnd_179747 := by exact prefixLift 179747
  have htrace : WordTrace (prefixWord ++ tailWord_179747) baseStart_179747 baseEnd_179747 := by
    simpa [prefixWord, tailWord_179747, baseEnd_179747] using wordTrace_append hprefix tailTrace_179747
  have hstable : (prefixWord ++ tailWord_179747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179747).length < 2 ^ (prefixWord ++ tailWord_179747).sum := by decide
  have hdescent : baseEnd_179747 < baseStart_179747 := by decide
  rcases family_descends (prefixWord ++ tailWord_179747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179768 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_179768 : Nat := 118140960795 + 179768 * 2 ^ 59
def prefixEnd_179768 : Nat := 4983230072969 + 3 ^ 40 * 179768 * 2
def baseEnd_179768 : Nat := 82051013597829236065127

theorem tailTrace_179768 : CollatzResearch.WordTrace tailWord_179768 prefixEnd_179768 82051013597829236065127 := by
  unfold tailWord_179768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278338806369356387601979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4371118408492475183469305 3278338806369356387601979)
  ·
    refine ⟨4917508209554034581402969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3278338806369356387601979 4917508209554034581402969)
    ·
      refine ⟨3688131157165525936052227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4917508209554034581402969 3688131157165525936052227)
      ·
        refine ⟨5532196735748288904078341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688131157165525936052227 5532196735748288904078341)
        ·
          refine ⟨1037286887952804169514689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5532196735748288904078341 1037286887952804169514689)
          ·
            refine ⟨777965165964603127136017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037286887952804169514689 777965165964603127136017)
            ·
              refine ⟨583473874473452345352013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777965165964603127136017 583473874473452345352013)
              ·
                refine ⟨218802702927544629507005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583473874473452345352013 218802702927544629507005)
                ·
                  refine ⟨82051013597829236065127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218802702927544629507005 82051013597829236065127)
                  ·
                    rfl

theorem cell20_179768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_179768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179768 prefixEnd_179768 := by exact prefixLift 179768
  have htrace : WordTrace (prefixWord ++ tailWord_179768) baseStart_179768 baseEnd_179768 := by
    simpa [prefixWord, tailWord_179768, baseEnd_179768] using wordTrace_append hprefix tailTrace_179768
  have hstable : (prefixWord ++ tailWord_179768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179768).length < 2 ^ (prefixWord ++ tailWord_179768).sum := by decide
  have hdescent : baseEnd_179768 < baseStart_179768 := by decide
  rcases family_descends (prefixWord ++ tailWord_179768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179775 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_179775 : Nat := 118140960795 + 179775 * 2 ^ 59
def prefixEnd_179775 : Nat := 4983230072969 + 3 ^ 40 * 179775 * 2
def baseEnd_179775 : Nat := 82054208588568322831765

theorem tailTrace_179775 : CollatzResearch.WordTrace tailWord_179775 prefixEnd_179775 82054208588568322831765 := by
  unfold tailWord_179775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6556932923713352970708779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4371288615808901980472519 6556932923713352970708779)
  ·
    refine ⟨9835399385570029456063169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6556932923713352970708779 9835399385570029456063169)
    ·
      refine ⟨7376549539177522092047377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9835399385570029456063169 7376549539177522092047377)
      ·
        refine ⟨5532412154383141569035533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7376549539177522092047377 5532412154383141569035533)
        ·
          refine ⟨2074654557893678088388325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5532412154383141569035533 2074654557893678088388325)
          ·
            refine ⟨388997729605064641572811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2074654557893678088388325 388997729605064641572811)
            ·
              refine ⟨583496594407596962359217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388997729605064641572811 583496594407596962359217)
              ·
                refine ⟨437622445805697721769413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583496594407596962359217 437622445805697721769413)
                ·
                  refine ⟨82054208588568322831765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437622445805697721769413 82054208588568322831765)
                  ·
                    rfl

theorem cell20_179775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_179775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179775 prefixEnd_179775 := by exact prefixLift 179775
  have htrace : WordTrace (prefixWord ++ tailWord_179775) baseStart_179775 baseEnd_179775 := by
    simpa [prefixWord, tailWord_179775, baseEnd_179775] using wordTrace_append hprefix tailTrace_179775
  have hstable : (prefixWord ++ tailWord_179775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179775).length < 2 ^ (prefixWord ++ tailWord_179775).sum := by decide
  have hdescent : baseEnd_179775 < baseStart_179775 := by decide
  rcases family_descends (prefixWord ++ tailWord_179775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179792 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_179792 : Nat := 118140960795 + 179792 * 2 ^ 59
def prefixEnd_179792 : Nat := 4983230072969 + 3 ^ 40 * 179792 * 2
def baseEnd_179792 : Nat := 82061967851791819265029

theorem tailTrace_179792 : CollatzResearch.WordTrace tailWord_179792 prefixEnd_179792 82061967851791819265029 := by
  unfold tailWord_179792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278776482325882437038815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4371701976434509916051753 3278776482325882437038815)
  ·
    refine ⟨4918164723488823655558223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3278776482325882437038815 4918164723488823655558223)
    ·
      refine ⟨7377247085233235483337335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918164723488823655558223 7377247085233235483337335)
      ·
        refine ⟨11065870627849853225006003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377247085233235483337335 11065870627849853225006003)
        ·
          refine ⟨16598805941774779837509005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11065870627849853225006003 16598805941774779837509005)
          ·
            refine ⟨6224552228165542439065877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16598805941774779837509005 6224552228165542439065877)
            ·
              refine ⟨291775885695259801831213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6224552228165542439065877 291775885695259801831213)
              ·
                refine ⟨109415957135722425686705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291775885695259801831213 109415957135722425686705)
                ·
                  refine ⟨82061967851791819265029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109415957135722425686705 82061967851791819265029)
                  ·
                    rfl

theorem cell20_179792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_179792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179792 prefixEnd_179792 := by exact prefixLift 179792
  have htrace : WordTrace (prefixWord ++ tailWord_179792) baseStart_179792 baseEnd_179792 := by
    simpa [prefixWord, tailWord_179792, baseEnd_179792] using wordTrace_append hprefix tailTrace_179792
  have hstable : (prefixWord ++ tailWord_179792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179792).length < 2 ^ (prefixWord ++ tailWord_179792).sum := by decide
  have hdescent : baseEnd_179792 < baseStart_179792 := by decide
  rcases family_descends (prefixWord ++ tailWord_179792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179798 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_179798 : Nat := 118140960795 + 179798 * 2 ^ 59
def prefixEnd_179798 : Nat := 4983230072969 + 3 ^ 40 * 179798 * 2
def baseEnd_179798 : Nat := 82064706415282465065005

theorem tailTrace_179798 : CollatzResearch.WordTrace tailWord_179798 prefixEnd_179798 82064706415282465065005 := by
  unfold tailWord_179798
  simp only [CollatzResearch.WordTrace]
  refine ⟨409860737664376743674753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4371847868420018599197365 409860737664376743674753)
  ·
    refine ⟨307395553248282557756065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409860737664376743674753 307395553248282557756065)
    ·
      refine ⟨230546664936211918317049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307395553248282557756065 230546664936211918317049)
      ·
        refine ⟨172909998702158938737787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230546664936211918317049 172909998702158938737787)
        ·
          refine ⟨259364998053238408106681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172909998702158938737787 259364998053238408106681)
          ·
            refine ⟨194523748539928806080011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259364998053238408106681 194523748539928806080011)
            ·
              refine ⟨291785622809893209120017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194523748539928806080011 291785622809893209120017)
              ·
                refine ⟨218839217107419906840013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291785622809893209120017 218839217107419906840013)
                ·
                  refine ⟨82064706415282465065005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218839217107419906840013 82064706415282465065005)
                  ·
                    rfl

theorem cell20_179798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_179798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179798 prefixEnd_179798 := by exact prefixLift 179798
  have htrace : WordTrace (prefixWord ++ tailWord_179798) baseStart_179798 baseEnd_179798 := by
    simpa [prefixWord, tailWord_179798, baseEnd_179798] using wordTrace_append hprefix tailTrace_179798
  have hstable : (prefixWord ++ tailWord_179798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179798).length < 2 ^ (prefixWord ++ tailWord_179798).sum := by decide
  have hdescent : baseEnd_179798 < baseStart_179798 := by decide
  rcases family_descends (prefixWord ++ tailWord_179798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179813 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_179813 : Nat := 118140960795 + 179813 * 2 ^ 59
def prefixEnd_179813 : Nat := 4983230072969 + 3 ^ 40 * 179813 * 2
def baseEnd_179813 : Nat := 82071552824009079564943

theorem tailTrace_179813 : CollatzResearch.WordTrace tailWord_179813 prefixEnd_179813 82071552824009079564943 := by
  unfold tailWord_179813
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558318897575685460592093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4372212598383790307061395 6558318897575685460592093)
  ·
    refine ⟨2459369586590882047722035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6558318897575685460592093 2459369586590882047722035)
    ·
      refine ⟨3689054379886323071583053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459369586590882047722035 3689054379886323071583053)
      ·
        refine ⟨1383395392457371151843645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3689054379886323071583053 1383395392457371151843645)
        ·
          refine ⟨518773272171514181941367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1383395392457371151843645 518773272171514181941367)
          ·
            refine ⟨778159908257271272912051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518773272171514181941367 778159908257271272912051)
            ·
              refine ⟨1167239862385906909368077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778159908257271272912051 1167239862385906909368077)
              ·
                refine ⟨437714948394715091013029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167239862385906909368077 437714948394715091013029)
                ·
                  refine ⟨82071552824009079564943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437714948394715091013029 82071552824009079564943)
                  ·
                    rfl

theorem cell20_179813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_179813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179813 prefixEnd_179813 := by exact prefixLift 179813
  have htrace : WordTrace (prefixWord ++ tailWord_179813) baseStart_179813 baseEnd_179813 := by
    simpa [prefixWord, tailWord_179813, baseEnd_179813] using wordTrace_append hprefix tailTrace_179813
  have hstable : (prefixWord ++ tailWord_179813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179813).length < 2 ^ (prefixWord ++ tailWord_179813).sum := by decide
  have hdescent : baseEnd_179813 < baseStart_179813 := by decide
  rcases family_descends (prefixWord ++ tailWord_179813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179830 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_179830 : Nat := 118140960795 + 179830 * 2 ^ 59
def prefixEnd_179830 : Nat := 4983230072969 + 3 ^ 40 * 179830 * 2
def baseEnd_179830 : Nat := 82079312087232575998207

theorem tailTrace_179830 : CollatzResearch.WordTrace tailWord_179830 prefixEnd_179830 82079312087232575998207 := by
  unfold tailWord_179830
  simp only [CollatzResearch.WordTrace]
  refine ⟨409933683657131085247559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4372625959009398242640629 409933683657131085247559)
  ·
    refine ⟨614900525485696627871339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409933683657131085247559 614900525485696627871339)
    ·
      refine ⟨922350788228544941807009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614900525485696627871339 922350788228544941807009)
      ·
        refine ⟨691763091171408706355257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922350788228544941807009 691763091171408706355257)
        ·
          refine ⟨518822318378556529766443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691763091171408706355257 518822318378556529766443)
          ·
            refine ⟨778233477567834794649665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518822318378556529766443 778233477567834794649665)
            ·
              refine ⟨583675108175876095987249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778233477567834794649665 583675108175876095987249)
              ·
                refine ⟨437756331131907071990437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583675108175876095987249 437756331131907071990437)
                ·
                  refine ⟨82079312087232575998207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437756331131907071990437 82079312087232575998207)
                  ·
                    rfl

theorem cell20_179830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_179830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179830 prefixEnd_179830 := by exact prefixLift 179830
  have htrace : WordTrace (prefixWord ++ tailWord_179830) baseStart_179830 baseEnd_179830 := by
    simpa [prefixWord, tailWord_179830, baseEnd_179830] using wordTrace_append hprefix tailTrace_179830
  have hstable : (prefixWord ++ tailWord_179830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179830).length < 2 ^ (prefixWord ++ tailWord_179830).sum := by decide
  have hdescent : baseEnd_179830 < baseStart_179830 := by decide
  rcases family_descends (prefixWord ++ tailWord_179830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179834 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_179834 : Nat := 118140960795 + 179834 * 2 ^ 59
def prefixEnd_179834 : Nat := 4983230072969 + 3 ^ 40 * 179834 * 2
def baseEnd_179834 : Nat := 82081137796226339864857

theorem tailTrace_179834 : CollatzResearch.WordTrace tailWord_179834 prefixEnd_179834 82081137796226339864857 := by
  unfold tailWord_179834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639771207624901511776639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4372723220333070698071037 1639771207624901511776639)
  ·
    refine ⟨2459656811437352267664959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639771207624901511776639 2459656811437352267664959)
    ·
      refine ⟨3689485217156028401497439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459656811437352267664959 3689485217156028401497439)
      ·
        refine ⟨5534227825734042602246159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689485217156028401497439 5534227825734042602246159)
        ·
          refine ⟨8301341738601063903369239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534227825734042602246159 8301341738601063903369239)
          ·
            refine ⟨12452012607901595855053859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301341738601063903369239 12452012607901595855053859)
            ·
              refine ⟨18678018911852393782580789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12452012607901595855053859 18678018911852393782580789)
              ·
                refine ⟨1751064272986161917116949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18678018911852393782580789 1751064272986161917116949)
                ·
                  refine ⟨82081137796226339864857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1751064272986161917116949 82081137796226339864857)
                  ·
                    rfl

theorem cell20_179834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_179834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179834 prefixEnd_179834 := by exact prefixLift 179834
  have htrace : WordTrace (prefixWord ++ tailWord_179834) baseStart_179834 baseEnd_179834 := by
    simpa [prefixWord, tailWord_179834, baseEnd_179834] using wordTrace_append hprefix tailTrace_179834
  have hstable : (prefixWord ++ tailWord_179834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179834).length < 2 ^ (prefixWord ++ tailWord_179834).sum := by decide
  have hdescent : baseEnd_179834 < baseStart_179834 := by decide
  rcases family_descends (prefixWord ++ tailWord_179834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179837 : List Nat := [1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_179837 : Nat := 118140960795 + 179837 * 2 ^ 59
def prefixEnd_179837 : Nat := 4983230072969 + 3 ^ 40 * 179837 * 2
def baseEnd_179837 : Nat := 27360835692657220921615

theorem tailTrace_179837 : CollatzResearch.WordTrace tailWord_179837 prefixEnd_179837 27360835692657220921615 := by
  unfold tailWord_179837
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559194249488737559465765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4372796166325825039643843 6559194249488737559465765)
  ·
    refine ⟨1229848921779138292399831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6559194249488737559465765 1229848921779138292399831)
    ·
      refine ⟨1844773382668707438599747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229848921779138292399831 1844773382668707438599747)
      ·
        refine ⟨2767160074003061157899621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844773382668707438599747 2767160074003061157899621)
        ·
          refine ⟨518842513875573967106179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2767160074003061157899621 518842513875573967106179)
          ·
            refine ⟨778263770813360950659269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518842513875573967106179 778263770813360950659269)
            ·
              refine ⟨145924457027505178248613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 778263770813360950659269 145924457027505178248613)
              ·
                refine ⟨27360835692657220921615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145924457027505178248613 27360835692657220921615)
                ·
                  rfl

theorem cell20_179837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_179837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179837 prefixEnd_179837 := by exact prefixLift 179837
  have htrace : WordTrace (prefixWord ++ tailWord_179837) baseStart_179837 baseEnd_179837 := by
    simpa [prefixWord, tailWord_179837, baseEnd_179837] using wordTrace_append hprefix tailTrace_179837
  have hstable : (prefixWord ++ tailWord_179837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179837).length < 2 ^ (prefixWord ++ tailWord_179837).sum := by decide
  have hdescent : baseEnd_179837 < baseStart_179837 := by decide
  rcases family_descends (prefixWord ++ tailWord_179837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179847 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 2]
def baseStart_179847 : Nat := 118140960795 + 179847 * 2 ^ 59
def prefixEnd_179847 : Nat := 4983230072969 + 3 ^ 40 * 179847 * 2
def baseEnd_179847 : Nat := 82087071350456072431471

theorem tailTrace_179847 : CollatzResearch.WordTrace tailWord_179847 prefixEnd_179847 82087071350456072431471 := by
  unfold tailWord_179847
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559558979452509267329795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4373039319635006178219863 6559558979452509267329795)
  ·
    refine ⟨9839338469178763900994693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6559558979452509267329795 9839338469178763900994693)
    ·
      refine ⟨1844875962971018231436505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9839338469178763900994693 1844875962971018231436505)
      ·
        refine ⟨1383656972228263673577379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1844875962971018231436505 1383656972228263673577379)
        ·
          refine ⟨2075485458342395510366069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383656972228263673577379 2075485458342395510366069)
          ·
            refine ⟨194576761719599579096819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2075485458342395510366069 194576761719599579096819)
            ·
              refine ⟨291865142579399368645229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194576761719599579096819 291865142579399368645229)
              ·
                refine ⟨109449428467274763241961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291865142579399368645229 109449428467274763241961)
                ·
                  refine ⟨82087071350456072431471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109449428467274763241961 82087071350456072431471)
                  ·
                    rfl

theorem cell20_179847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2].length) (baseStart_179847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179847 prefixEnd_179847 := by exact prefixLift 179847
  have htrace : WordTrace (prefixWord ++ tailWord_179847) baseStart_179847 baseEnd_179847 := by
    simpa [prefixWord, tailWord_179847, baseEnd_179847] using wordTrace_append hprefix tailTrace_179847
  have hstable : (prefixWord ++ tailWord_179847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179847).length < 2 ^ (prefixWord ++ tailWord_179847).sum := by decide
  have hdescent : baseEnd_179847 < baseStart_179847 := by decide
  rcases family_descends (prefixWord ++ tailWord_179847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179874 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_179874 : Nat := 118140960795 + 179874 * 2 ^ 59
def prefixEnd_179874 : Nat := 4983230072969 + 3 ^ 40 * 179874 * 2
def baseEnd_179874 : Nat := 82099394886163978531361

theorem tailTrace_179874 : CollatzResearch.WordTrace tailWord_179874 prefixEnd_179874 82099394886163978531361 := by
  unfold tailWord_179874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640135937588673219640669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4373695833569795252375117 1640135937588673219640669)
  ·
    refine ⟨615050976595752457365251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1640135937588673219640669 615050976595752457365251)
    ·
      refine ⟨922576464893628686047877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615050976595752457365251 922576464893628686047877)
      ·
        refine ⟨172983087167555378633977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 922576464893628686047877 172983087167555378633977)
        ·
          refine ⟨129737315375666533975483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172983087167555378633977 129737315375666533975483)
          ·
            refine ⟨194605973063499800963225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129737315375666533975483 194605973063499800963225)
            ·
              refine ⟨145954479797624850722419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194605973063499800963225 145954479797624850722419)
              ·
                refine ⟨218931719696437276083629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145954479797624850722419 218931719696437276083629)
                ·
                  refine ⟨82099394886163978531361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218931719696437276083629 82099394886163978531361)
                  ·
                    rfl

theorem cell20_179874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_179874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179874 prefixEnd_179874 := by exact prefixLift 179874
  have htrace : WordTrace (prefixWord ++ tailWord_179874) baseStart_179874 baseEnd_179874 := by
    simpa [prefixWord, tailWord_179874, baseEnd_179874] using wordTrace_append hprefix tailTrace_179874
  have hstable : (prefixWord ++ tailWord_179874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179874).length < 2 ^ (prefixWord ++ tailWord_179874).sum := by decide
  have hdescent : baseEnd_179874 < baseStart_179874 := by decide
  rcases family_descends (prefixWord ++ tailWord_179874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179926 : List Nat := [5, 2, 1, 3, 2, 1, 1, 5]
def baseStart_179926 : Nat := 118140960795 + 179926 * 2 ^ 59
def prefixEnd_179926 : Nat := 4983230072969 + 3 ^ 40 * 179926 * 2
def baseEnd_179926 : Nat := 27374376367694302932605

theorem tailTrace_179926 : CollatzResearch.WordTrace tailWord_179926 prefixEnd_179926 27374376367694302932605 := by
  unfold tailWord_179926
  simp only [CollatzResearch.WordTrace]
  refine ⟨410152521635394109965977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4374960230777537172970421 410152521635394109965977)
  ·
    refine ⟨307614391226545582474483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 410152521635394109965977 307614391226545582474483)
    ·
      refine ⟨461421586839818373711725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307614391226545582474483 461421586839818373711725)
      ·
        refine ⟨173033095064931890141897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461421586839818373711725 173033095064931890141897)
        ·
          refine ⟨129774821298698917606423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173033095064931890141897 129774821298698917606423)
          ·
            refine ⟨194662231948048376409635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129774821298698917606423 194662231948048376409635)
            ·
              refine ⟨291993347922072564614453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194662231948048376409635 291993347922072564614453)
              ·
                refine ⟨27374376367694302932605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291993347922072564614453 27374376367694302932605)
                ·
                  rfl

theorem cell20_179926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_179926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179926 prefixEnd_179926 := by exact prefixLift 179926
  have htrace : WordTrace (prefixWord ++ tailWord_179926) baseStart_179926 baseEnd_179926 := by
    simpa [prefixWord, tailWord_179926, baseEnd_179926] using wordTrace_append hprefix tailTrace_179926
  have hstable : (prefixWord ++ tailWord_179926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179926).length < 2 ^ (prefixWord ++ tailWord_179926).sum := by decide
  have hdescent : baseEnd_179926 < baseStart_179926 := by decide
  rcases family_descends (prefixWord ++ tailWord_179926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179948 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_179948 : Nat := 118140960795 + 179948 * 2 ^ 59
def prefixEnd_179948 : Nat := 4983230072969 + 3 ^ 40 * 179948 * 2
def baseEnd_179948 : Nat := 82133170502548610064391

theorem tailTrace_179948 : CollatzResearch.WordTrace tailWord_179948 prefixEnd_179948 82133170502548610064391 := by
  unfold tailWord_179948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281621376043301758378249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4375495168057735677837665 3281621376043301758378249)
  ·
    refine ⟨2461216032032476318783687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3281621376043301758378249 2461216032032476318783687)
    ·
      refine ⟨3691824048048714478175531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461216032032476318783687 3691824048048714478175531)
      ·
        refine ⟨5537736072073071717263297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691824048048714478175531 5537736072073071717263297)
        ·
          refine ⟨4153302054054803787947473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5537736072073071717263297 4153302054054803787947473)
          ·
            refine ⟨3114976540541102840960605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4153302054054803787947473 3114976540541102840960605)
            ·
              refine ⟨1168116202702913565360227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3114976540541102840960605 1168116202702913565360227)
              ·
                refine ⟨1752174304054370348040341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168116202702913565360227 1752174304054370348040341)
                ·
                  refine ⟨82133170502548610064391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1752174304054370348040341 82133170502548610064391)
                  ·
                    rfl

theorem cell20_179948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_179948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179948 prefixEnd_179948 := by exact prefixLift 179948
  have htrace : WordTrace (prefixWord ++ tailWord_179948) baseStart_179948 baseEnd_179948 := by
    simpa [prefixWord, tailWord_179948, baseEnd_179948] using wordTrace_append hprefix tailTrace_179948
  have hstable : (prefixWord ++ tailWord_179948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179948).length < 2 ^ (prefixWord ++ tailWord_179948).sum := by decide
  have hdescent : baseEnd_179948 < baseStart_179948 := by decide
  rcases family_descends (prefixWord ++ tailWord_179948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179955 : List Nat := [1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_179955 : Nat := 118140960795 + 179955 * 2 ^ 59
def prefixEnd_179955 : Nat := 4983230072969 + 3 ^ 40 * 179955 * 2
def baseEnd_179955 : Nat := 27378788497762565610343

theorem tailTrace_179955 : CollatzResearch.WordTrace tailWord_179955 prefixEnd_179955 27378788497762565610343 := by
  unfold tailWord_179955
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563498063061243712261319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4375665375374162474840879 6563498063061243712261319)
  ·
    refine ⟨9845247094591865568391979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563498063061243712261319 9845247094591865568391979)
    ·
      refine ⟨14767870641887798352587969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845247094591865568391979 14767870641887798352587969)
      ·
        refine ⟨11075902981415848764440977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14767870641887798352587969 11075902981415848764440977)
        ·
          refine ⟨8306927236061886573330733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11075902981415848764440977 8306927236061886573330733)
          ·
            refine ⟨3115097713523207464999025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8306927236061886573330733 3115097713523207464999025)
            ·
              refine ⟨2336323285142405598749269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115097713523207464999025 2336323285142405598749269)
              ·
                refine ⟨27378788497762565610343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2336323285142405598749269 27378788497762565610343)
                ·
                  rfl

theorem cell20_179955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_179955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179955 prefixEnd_179955 := by exact prefixLift 179955
  have htrace : WordTrace (prefixWord ++ tailWord_179955) baseStart_179955 baseEnd_179955 := by
    simpa [prefixWord, tailWord_179955, baseEnd_179955] using wordTrace_append hprefix tailTrace_179955
  have hstable : (prefixWord ++ tailWord_179955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179955).length < 2 ^ (prefixWord ++ tailWord_179955).sum := by decide
  have hdescent : baseEnd_179955 < baseStart_179955 := by decide
  rcases family_descends (prefixWord ++ tailWord_179955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179972 : List Nat := [2, 3, 2, 2, 1, 3, 7]
def baseStart_179972 : Nat := 118140960795 + 179972 * 2 ^ 59
def prefixEnd_179972 : Nat := 4983230072969 + 3 ^ 40 * 179972 * 2
def baseEnd_179972 : Nat := 9127124972945688140477

theorem tailTrace_179972 : CollatzResearch.WordTrace tailWord_179972 prefixEnd_179972 9127124972945688140477 := by
  unfold tailWord_179972
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282059051999827807815085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4376078735999770410420113 3282059051999827807815085)
  ·
    refine ⟨1230772144499935427930657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3282059051999827807815085 1230772144499935427930657)
    ·
      refine ⟨923079108374951570947993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230772144499935427930657 923079108374951570947993)
      ·
        refine ⟨692309331281213678210995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923079108374951570947993 692309331281213678210995)
        ·
          refine ⟨1038463996921820517316493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692309331281213678210995 1038463996921820517316493)
          ·
            refine ⟨389423998845682693993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038463996921820517316493 389423998845682693993685)
            ·
              refine ⟨9127124972945688140477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 389423998845682693993685 9127124972945688140477)
              ·
                rfl

theorem cell20_179972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_179972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179972 prefixEnd_179972 := by exact prefixLift 179972
  have htrace : WordTrace (prefixWord ++ tailWord_179972) baseStart_179972 baseEnd_179972 := by
    simpa [prefixWord, tailWord_179972, baseEnd_179972] using wordTrace_append hprefix tailTrace_179972
  have hstable : (prefixWord ++ tailWord_179972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179972).length < 2 ^ (prefixWord ++ tailWord_179972).sum := by decide
  have hdescent : baseEnd_179972 < baseStart_179972 := by decide
  rcases family_descends (prefixWord ++ tailWord_179972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179974 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_179974 : Nat := 118140960795 + 179974 * 2 ^ 59
def prefixEnd_179974 : Nat := 4983230072969 + 3 ^ 40 * 179974 * 2
def baseEnd_179974 : Nat := 82145037611008075197619

theorem tailTrace_179974 : CollatzResearch.WordTrace tailWord_179974 prefixEnd_179974 82145037611008075197619 := by
  unfold tailWord_179974
  simp only [CollatzResearch.WordTrace]
  refine ⟨205130970312262811162593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4376127366661606638135317 205130970312262811162593)
  ·
    refine ⟨153848227734197108371945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205130970312262811162593 153848227734197108371945)
    ·
      refine ⟨115386170800647831278959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153848227734197108371945 115386170800647831278959)
      ·
        refine ⟨173079256200971746918439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115386170800647831278959 173079256200971746918439)
        ·
          refine ⟨259618884301457620377659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173079256200971746918439 259618884301457620377659)
          ·
            refine ⟨389428326452186430566489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259618884301457620377659 389428326452186430566489)
            ·
              refine ⟨292071244839139822924867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389428326452186430566489 292071244839139822924867)
              ·
                refine ⟨438106867258709734387301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292071244839139822924867 438106867258709734387301)
                ·
                  refine ⟨82145037611008075197619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438106867258709734387301 82145037611008075197619)
                  ·
                    rfl

theorem cell20_179974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_179974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179974 prefixEnd_179974 := by exact prefixLift 179974
  have htrace : WordTrace (prefixWord ++ tailWord_179974) baseStart_179974 baseEnd_179974 := by
    simpa [prefixWord, tailWord_179974, baseEnd_179974] using wordTrace_append hprefix tailTrace_179974
  have hstable : (prefixWord ++ tailWord_179974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179974).length < 2 ^ (prefixWord ++ tailWord_179974).sum := by decide
  have hdescent : baseEnd_179974 < baseStart_179974 := by decide
  rcases family_descends (prefixWord ++ tailWord_179974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179982 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_179982 : Nat := 118140960795 + 179982 * 2 ^ 59
def prefixEnd_179982 : Nat := 4983230072969 + 3 ^ 40 * 179982 * 2
def baseEnd_179982 : Nat := 82148689028995602930919

theorem tailTrace_179982 : CollatzResearch.WordTrace tailWord_179982 prefixEnd_179982 82148689028995602930919 := by
  unfold tailWord_179982
  simp only [CollatzResearch.WordTrace]
  refine ⟨820560354245428415436775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4376321889308951548996133 820560354245428415436775)
  ·
    refine ⟨1230840531368142623155163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820560354245428415436775 1230840531368142623155163)
    ·
      refine ⟨1846260797052213934732745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230840531368142623155163 1846260797052213934732745)
      ·
        refine ⟨1384695597789160451049559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846260797052213934732745 1384695597789160451049559)
        ·
          refine ⟨2077043396683740676574339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384695597789160451049559 2077043396683740676574339)
          ·
            refine ⟨3115565095025611014861509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077043396683740676574339 3115565095025611014861509)
            ·
              refine ⟨584168455317302065286533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3115565095025611014861509 584168455317302065286533)
              ·
                refine ⟨109531585371994137241225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584168455317302065286533 109531585371994137241225)
                ·
                  refine ⟨82148689028995602930919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109531585371994137241225 82148689028995602930919)
                  ·
                    rfl

theorem cell20_179982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_179982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179982 prefixEnd_179982 := by exact prefixLift 179982
  have htrace : WordTrace (prefixWord ++ tailWord_179982) baseStart_179982 baseEnd_179982 := by
    simpa [prefixWord, tailWord_179982, baseEnd_179982] using wordTrace_append hprefix tailTrace_179982
  have hstable : (prefixWord ++ tailWord_179982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179982).length < 2 ^ (prefixWord ++ tailWord_179982).sum := by decide
  have hdescent : baseEnd_179982 < baseStart_179982 := by decide
  rcases family_descends (prefixWord ++ tailWord_179982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179988 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_179988 : Nat := 118140960795 + 179988 * 2 ^ 59
def prefixEnd_179988 : Nat := 4983230072969 + 3 ^ 40 * 179988 * 2
def baseEnd_179988 : Nat := 82151427592486248730895

theorem tailTrace_179988 : CollatzResearch.WordTrace tailWord_179988 prefixEnd_179988 82151427592486248730895 := by
  unfold tailWord_179988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282350835970845174106309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4376467781294460232141745 3282350835970845174106309)
  ·
    refine ⟨615440781744533470144933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3282350835970845174106309 615440781744533470144933)
    ·
      refine ⟨115395146577100025652175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 615440781744533470144933 115395146577100025652175)
      ·
        refine ⟨173092719865650038478263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115395146577100025652175 173092719865650038478263)
        ·
          refine ⟨259639079798475057717395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173092719865650038478263 259639079798475057717395)
          ·
            refine ⟨389458619697712586576093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259639079798475057717395 389458619697712586576093)
            ·
              refine ⟨146046982386642219966035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389458619697712586576093 146046982386642219966035)
              ·
                refine ⟨219070473579963329949053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146046982386642219966035 219070473579963329949053)
                ·
                  refine ⟨82151427592486248730895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219070473579963329949053 82151427592486248730895)
                  ·
                    rfl

theorem cell20_179988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_179988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_179988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_179988 prefixEnd_179988 := by exact prefixLift 179988
  have htrace : WordTrace (prefixWord ++ tailWord_179988) baseStart_179988 baseEnd_179988 := by
    simpa [prefixWord, tailWord_179988, baseEnd_179988] using wordTrace_append hprefix tailTrace_179988
  have hstable : (prefixWord ++ tailWord_179988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179988).length < 2 ^ (prefixWord ++ tailWord_179988).sum := by decide
  have hdescent : baseEnd_179988 < baseStart_179988 := by decide
  rcases family_descends (prefixWord ++ tailWord_179988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180017 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_180017 : Nat := 118140960795 + 180017 * 2 ^ 59
def prefixEnd_180017 : Nat := 4983230072969 + 3 ^ 40 * 180017 * 2
def baseEnd_180017 : Nat := 82164663982691036764109

theorem tailTrace_180017 : CollatzResearch.WordTrace tailWord_180017 prefixEnd_180017 82164663982691036764109 := by
  unfold tailWord_180017
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565759388836628301018305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377172925891085534012203 6565759388836628301018305)
  ·
    refine ⟨4924319541627471225763729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6565759388836628301018305 4924319541627471225763729)
    ·
      refine ⟨3693239656220603419322797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4924319541627471225763729 3693239656220603419322797)
      ·
        refine ⟨1384964871082726282246049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3693239656220603419322797 1384964871082726282246049)
        ·
          refine ⟨1038723653312044711684537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384964871082726282246049 1038723653312044711684537)
          ·
            refine ⟨779042739984033533763403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038723653312044711684537 779042739984033533763403)
            ·
              refine ⟨1168564109976050300645105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779042739984033533763403 1168564109976050300645105)
              ·
                refine ⟨876423082482037725483829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168564109976050300645105 876423082482037725483829)
                ·
                  refine ⟨82164663982691036764109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 876423082482037725483829 82164663982691036764109)
                  ·
                    rfl

theorem cell20_180017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_180017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180017 prefixEnd_180017 := by exact prefixLift 180017
  have htrace : WordTrace (prefixWord ++ tailWord_180017) baseStart_180017 baseEnd_180017 := by
    simpa [prefixWord, tailWord_180017, baseEnd_180017] using wordTrace_append hprefix tailTrace_180017
  have hstable : (prefixWord ++ tailWord_180017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180017).length < 2 ^ (prefixWord ++ tailWord_180017).sum := by decide
  have hdescent : baseEnd_180017 < baseStart_180017 := by decide
  rcases family_descends (prefixWord ++ tailWord_180017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180086 : List Nat := [5, 1, 1, 3, 10]
def baseStart_180086 : Nat := 118140960795 + 180086 * 2 ^ 59
def prefixEnd_180086 : Nat := 4983230072969 + 3 ^ 40 * 180086 * 2
def baseEnd_180086 : Nat := 1014767376084363746467

theorem tailTrace_180086 : CollatzResearch.WordTrace tailWord_180086 prefixEnd_180086 1014767376084363746467 := by
  unfold tailWord_180086
  simp only [CollatzResearch.WordTrace]
  refine ⟨410517251599165817830007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4378850683724435390186741 410517251599165817830007)
  ·
    refine ⟨615775877398748726745011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410517251599165817830007 615775877398748726745011)
    ·
      refine ⟨923663816098123090117517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615775877398748726745011 923663816098123090117517)
      ·
        refine ⟨346373931036796158794069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 923663816098123090117517 346373931036796158794069)
        ·
          refine ⟨1014767376084363746467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 346373931036796158794069 1014767376084363746467)
          ·
            rfl

theorem cell20_180086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 10].length) (baseStart_180086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180086 prefixEnd_180086 := by exact prefixLift 180086
  have htrace : WordTrace (prefixWord ++ tailWord_180086) baseStart_180086 baseEnd_180086 := by
    simpa [prefixWord, tailWord_180086, baseEnd_180086] using wordTrace_append hprefix tailTrace_180086
  have hstable : (prefixWord ++ tailWord_180086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180086).length < 2 ^ (prefixWord ++ tailWord_180086).sum := by decide
  have hdescent : baseEnd_180086 < baseStart_180086 := by decide
  rcases family_descends (prefixWord ++ tailWord_180086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180103 : List Nat := [1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_180103 : Nat := 118140960795 + 180103 * 2 ^ 59
def prefixEnd_180103 : Nat := 4983230072969 + 3 ^ 40 * 180103 * 2
def baseEnd_180103 : Nat := 27401305575352319965697

theorem tailTrace_180103 : CollatzResearch.WordTrace tailWord_180103 prefixEnd_180103 27401305575352319965697 := by
  unfold tailWord_180103
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568896066525064988648963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4379264044350043325765975 6568896066525064988648963)
  ·
    refine ⟨9853344099787597482973445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6568896066525064988648963 9853344099787597482973445)
    ·
      refine ⟨1847502018710174528057521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9853344099787597482973445 1847502018710174528057521)
      ·
        refine ⟨1385626514032630896043141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847502018710174528057521 1385626514032630896043141)
        ·
          refine ⟨259804971381118293008089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1385626514032630896043141 259804971381118293008089)
          ·
            refine ⟨194853728535838719756067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259804971381118293008089 194853728535838719756067)
            ·
              refine ⟨292280592803758079634101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194853728535838719756067 292280592803758079634101)
              ·
                refine ⟨27401305575352319965697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292280592803758079634101 27401305575352319965697)
                ·
                  rfl

theorem cell20_180103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_180103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180103 prefixEnd_180103 := by exact prefixLift 180103
  have htrace : WordTrace (prefixWord ++ tailWord_180103) baseStart_180103 baseEnd_180103 := by
    simpa [prefixWord, tailWord_180103, baseEnd_180103] using wordTrace_append hprefix tailTrace_180103
  have hstable : (prefixWord ++ tailWord_180103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180103).length < 2 ^ (prefixWord ++ tailWord_180103).sum := by decide
  have hdescent : baseEnd_180103 < baseStart_180103 := by decide
  rcases family_descends (prefixWord ++ tailWord_180103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180120 : List Nat := [2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_180120 : Nat := 118140960795 + 180120 * 2 ^ 59
def prefixEnd_180120 : Nat := 4983230072969 + 3 ^ 40 * 180120 * 2
def baseEnd_180120 : Nat := 27403891996426818776785

theorem tailTrace_180120 : CollatzResearch.WordTrace tailWord_180120 prefixEnd_180120 27403891996426818776785 := by
  unfold tailWord_180120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284758053731738446008907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4379677404975651261345209 3284758053731738446008907)
  ·
    refine ⟨4927137080597607669013361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284758053731738446008907 4927137080597607669013361)
    ·
      refine ⟨3695352810448205751760021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4927137080597607669013361 3695352810448205751760021)
      ·
        refine ⟨173219662989759644613751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3695352810448205751760021 173219662989759644613751)
        ·
          refine ⟨259829494484639466920627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173219662989759644613751 259829494484639466920627)
          ·
            refine ⟨389744241726959200380941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259829494484639466920627 389744241726959200380941)
            ·
              refine ⟨146154090647609700142853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389744241726959200380941 146154090647609700142853)
              ·
                refine ⟨27403891996426818776785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146154090647609700142853 27403891996426818776785)
                ·
                  rfl

theorem cell20_180120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_180120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180120 prefixEnd_180120 := by exact prefixLift 180120
  have htrace : WordTrace (prefixWord ++ tailWord_180120) baseStart_180120 baseEnd_180120 := by
    simpa [prefixWord, tailWord_180120, baseEnd_180120] using wordTrace_append hprefix tailTrace_180120
  have hstable : (prefixWord ++ tailWord_180120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180120).length < 2 ^ (prefixWord ++ tailWord_180120).sum := by decide
  have hdescent : baseEnd_180120 < baseStart_180120 := by decide
  rcases family_descends (prefixWord ++ tailWord_180120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180176 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_180176 : Nat := 118140960795 + 180176 * 2 ^ 59
def prefixEnd_180176 : Nat := 4983230072969 + 3 ^ 40 * 180176 * 2
def baseEnd_180176 : Nat := 82237235915193150463459

theorem tailTrace_180176 : CollatzResearch.WordTrace tailWord_180176 prefixEnd_180176 82237235915193150463459 := by
  unfold tailWord_180176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3285779297630299228028191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4381039063507065637370921 3285779297630299228028191)
  ·
    refine ⟨4928668946445448842042287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3285779297630299228028191 4928668946445448842042287)
    ·
      refine ⟨7393003419668173263063431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928668946445448842042287 7393003419668173263063431)
      ·
        refine ⟨11089505129502259894595147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393003419668173263063431 11089505129502259894595147)
        ·
          refine ⟨16634257694253389841892721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089505129502259894595147 16634257694253389841892721)
          ·
            refine ⟨12475693270690042381419541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16634257694253389841892721 12475693270690042381419541)
            ·
              refine ⟨584798122063595736629041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12475693270690042381419541 584798122063595736629041)
              ·
                refine ⟨438598591547696802471781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584798122063595736629041 438598591547696802471781)
                ·
                  refine ⟨82237235915193150463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438598591547696802471781 82237235915193150463459)
                  ·
                    rfl

theorem cell20_180176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_180176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180176 prefixEnd_180176 := by exact prefixLift 180176
  have htrace : WordTrace (prefixWord ++ tailWord_180176) baseStart_180176 baseEnd_180176 := by
    simpa [prefixWord, tailWord_180176, baseEnd_180176] using wordTrace_append hprefix tailTrace_180176
  have hstable : (prefixWord ++ tailWord_180176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180176).length < 2 ^ (prefixWord ++ tailWord_180176).sum := by decide
  have hdescent : baseEnd_180176 < baseStart_180176 := by decide
  rcases family_descends (prefixWord ++ tailWord_180176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180183 : List Nat := [1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_180183 : Nat := 118140960795 + 180183 * 2 ^ 59
def prefixEnd_180183 : Nat := 4983230072969 + 3 ^ 40 * 180183 * 2
def baseEnd_180183 : Nat := 27413476968644079076699

theorem tailTrace_180183 : CollatzResearch.WordTrace tailWord_180183 prefixEnd_180183 27413476968644079076699 := by
  unfold tailWord_180183
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571813906235238651561203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381209270823492434374135 6571813906235238651561203)
  ·
    refine ⟨9857720859352857977341805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571813906235238651561203 9857720859352857977341805)
    ·
      refine ⟨3696645322257321741503177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9857720859352857977341805 3696645322257321741503177)
      ·
        refine ⟨2772483991692991306127383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3696645322257321741503177 2772483991692991306127383)
        ·
          refine ⟨4158725987539486959191075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772483991692991306127383 4158725987539486959191075)
          ·
            refine ⟨6238088981309230438786613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158725987539486959191075 6238088981309230438786613)
            ·
              refine ⟨584820841997740353636245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6238088981309230438786613 584820841997740353636245)
              ·
                refine ⟨27413476968644079076699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 584820841997740353636245 27413476968644079076699)
                ·
                  rfl

theorem cell20_180183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_180183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180183 prefixEnd_180183 := by exact prefixLift 180183
  have htrace : WordTrace (prefixWord ++ tailWord_180183) baseStart_180183 baseEnd_180183 := by
    simpa [prefixWord, tailWord_180183, baseEnd_180183] using wordTrace_append hprefix tailTrace_180183
  have hstable : (prefixWord ++ tailWord_180183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180183).length < 2 ^ (prefixWord ++ tailWord_180183).sum := by decide
  have hdescent : baseEnd_180183 < baseStart_180183 := by decide
  rcases family_descends (prefixWord ++ tailWord_180183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180207 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_180207 : Nat := 118140960795 + 180207 * 2 ^ 59
def prefixEnd_180207 : Nat := 4983230072969 + 3 ^ 40 * 180207 * 2
def baseEnd_180207 : Nat := 82251385159894820429999

theorem tailTrace_180207 : CollatzResearch.WordTrace tailWord_180207 prefixEnd_180207 82251385159894820429999 := by
  unfold tailWord_180207
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572689258148290750434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381792838765527166956583 6572689258148290750434875)
  ·
    refine ⟨9859033887222436125652313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572689258148290750434875 9859033887222436125652313)
    ·
      refine ⟨7394275415416827094239235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9859033887222436125652313 7394275415416827094239235)
      ·
        refine ⟨11091413123125240641358853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394275415416827094239235 11091413123125240641358853)
        ·
          refine ⟨2079639960585982620254785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11091413123125240641358853 2079639960585982620254785)
          ·
            refine ⟨1559729970439486965191089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079639960585982620254785 1559729970439486965191089)
            ·
              refine ⟨1169797477829615223893317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559729970439486965191089 1169797477829615223893317)
              ·
                refine ⟨219337027093052854479997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1169797477829615223893317 219337027093052854479997)
                ·
                  refine ⟨82251385159894820429999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219337027093052854479997 82251385159894820429999)
                  ·
                    rfl

theorem cell20_180207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_180207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180207 prefixEnd_180207 := by exact prefixLift 180207
  have htrace : WordTrace (prefixWord ++ tailWord_180207) baseStart_180207 baseEnd_180207 := by
    simpa [prefixWord, tailWord_180207, baseEnd_180207] using wordTrace_append hprefix tailTrace_180207
  have hstable : (prefixWord ++ tailWord_180207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180207).length < 2 ^ (prefixWord ++ tailWord_180207).sum := by decide
  have hdescent : baseEnd_180207 < baseStart_180207 := by decide
  rcases family_descends (prefixWord ++ tailWord_180207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180221 : List Nat := [1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_180221 : Nat := 118140960795 + 180221 * 2 ^ 59
def prefixEnd_180221 : Nat := 4983230072969 + 3 ^ 40 * 180221 * 2
def baseEnd_180221 : Nat := 27419258380457664654425

theorem tailTrace_180221 : CollatzResearch.WordTrace tailWord_180221 prefixEnd_180221 27419258380457664654425 := by
  unfold tailWord_180221
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573199880097571141444517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4382133253398380760963011 6573199880097571141444517)
  ·
    refine ⟨1232474977518294589020847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6573199880097571141444517 1232474977518294589020847)
    ·
      refine ⟨1848712466277441883531271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232474977518294589020847 1848712466277441883531271)
      ·
        refine ⟨2773068699416162825296907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848712466277441883531271 2773068699416162825296907)
        ·
          refine ⟨4159603049124244237945361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773068699416162825296907 4159603049124244237945361)
          ·
            refine ⟨3119702286843183178459021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159603049124244237945361 3119702286843183178459021)
            ·
              refine ⟨1169888357566193691922133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3119702286843183178459021 1169888357566193691922133)
              ·
                refine ⟨27419258380457664654425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1169888357566193691922133 27419258380457664654425)
                ·
                  rfl

theorem cell20_180221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_180221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180221 prefixEnd_180221 := by exact prefixLift 180221
  have htrace : WordTrace (prefixWord ++ tailWord_180221) baseStart_180221 baseEnd_180221 := by
    simpa [prefixWord, tailWord_180221, baseEnd_180221] using wordTrace_append hprefix tailTrace_180221
  have hstable : (prefixWord ++ tailWord_180221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180221).length < 2 ^ (prefixWord ++ tailWord_180221).sum := by decide
  have hdescent : baseEnd_180221 < baseStart_180221 := by decide
  rcases family_descends (prefixWord ++ tailWord_180221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180286 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_180286 : Nat := 118140960795 + 180286 * 2 ^ 59
def prefixEnd_180286 : Nat := 4983230072969 + 3 ^ 40 * 180286 * 2
def baseEnd_180286 : Nat := 82287442912521656796343

theorem tailTrace_180286 : CollatzResearch.WordTrace tailWord_180286 prefixEnd_180286 82287442912521656796343 := by
  unfold tailWord_180286
  simp only [CollatzResearch.WordTrace]
  refine ⟨821946328107760905320089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4383713749908058161707141 821946328107760905320089)
  ·
    refine ⟨616459746080820678990067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 821946328107760905320089 616459746080820678990067)
    ·
      refine ⟨924689619121231018485101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616459746080820678990067 924689619121231018485101)
      ·
        refine ⟨346758607170461631931913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 924689619121231018485101 346758607170461631931913)
        ·
          refine ⟨260068955377846223948935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346758607170461631931913 260068955377846223948935)
          ·
            refine ⟨390103433066769335923403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260068955377846223948935 390103433066769335923403)
            ·
              refine ⟨585155149600154003885105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390103433066769335923403 585155149600154003885105)
              ·
                refine ⟨438866362200115502913829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585155149600154003885105 438866362200115502913829)
                ·
                  refine ⟨82287442912521656796343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438866362200115502913829 82287442912521656796343)
                  ·
                    rfl

theorem cell20_180286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_180286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180286 prefixEnd_180286 := by exact prefixLift 180286
  have htrace : WordTrace (prefixWord ++ tailWord_180286) baseStart_180286 baseEnd_180286 := by
    simpa [prefixWord, tailWord_180286, baseEnd_180286] using wordTrace_append hprefix tailTrace_180286
  have hstable : (prefixWord ++ tailWord_180286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180286).length < 2 ^ (prefixWord ++ tailWord_180286).sum := by decide
  have hdescent : baseEnd_180286 < baseStart_180286 := by decide
  rcases family_descends (prefixWord ++ tailWord_180286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180317 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_180317 : Nat := 118140960795 + 180317 * 2 ^ 59
def prefixEnd_180317 : Nat := 4983230072969 + 3 ^ 40 * 180317 * 2
def baseEnd_180317 : Nat := 82301592157223326762883

theorem tailTrace_180317 : CollatzResearch.WordTrace tailWord_180317 prefixEnd_180317 82301592157223326762883 := by
  unfold tailWord_180317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6576701287749779536939205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4384467525166519691292803 6576701287749779536939205)
  ·
    refine ⟨1233131491453083663176101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6576701287749779536939205 1233131491453083663176101)
    ·
      refine ⟨231212154647453186845519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1233131491453083663176101 231212154647453186845519)
      ·
        refine ⟨346818231971179780268279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231212154647453186845519 346818231971179780268279)
        ·
          refine ⟨520227347956769670402419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346818231971179780268279 520227347956769670402419)
          ·
            refine ⟨780341021935154505603629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520227347956769670402419 780341021935154505603629)
            ·
              refine ⟨292627883225682939601361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780341021935154505603629 292627883225682939601361)
              ·
                refine ⟨219470912419262204701021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292627883225682939601361 219470912419262204701021)
                ·
                  refine ⟨82301592157223326762883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219470912419262204701021 82301592157223326762883)
                  ·
                    rfl

theorem cell20_180317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_180317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180317 prefixEnd_180317 := by exact prefixLift 180317
  have htrace : WordTrace (prefixWord ++ tailWord_180317) baseStart_180317 baseEnd_180317 := by
    simpa [prefixWord, tailWord_180317, baseEnd_180317] using wordTrace_append hprefix tailTrace_180317
  have hstable : (prefixWord ++ tailWord_180317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180317).length < 2 ^ (prefixWord ++ tailWord_180317).sum := by decide
  have hdescent : baseEnd_180317 < baseStart_180317 := by decide
  rcases family_descends (prefixWord ++ tailWord_180317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180362 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_180362 : Nat := 118140960795 + 180362 * 2 ^ 59
def prefixEnd_180362 : Nat := 4983230072969 + 3 ^ 40 * 180362 * 2
def baseEnd_180362 : Nat := 82322131383403170262699

theorem tailTrace_180362 : CollatzResearch.WordTrace tailWord_180362 prefixEnd_180362 82322131383403170262699 := by
  unfold tailWord_180362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644585643146688055581835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4385561715057834814884893 1644585643146688055581835)
  ·
    refine ⟨2466878464720032083372753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644585643146688055581835 2466878464720032083372753)
    ·
      refine ⟨1850158848540024062529565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2466878464720032083372753 1850158848540024062529565)
      ·
        refine ⟨693809568202509023448587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1850158848540024062529565 693809568202509023448587)
        ·
          refine ⟨1040714352303763535172881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693809568202509023448587 1040714352303763535172881)
          ·
            refine ⟨780535764227822651379661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1040714352303763535172881 780535764227822651379661)
            ·
              refine ⟨292700911585433494267373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780535764227822651379661 292700911585433494267373)
              ·
                refine ⟨109762841844537560350265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292700911585433494267373 109762841844537560350265)
                ·
                  refine ⟨82322131383403170262699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109762841844537560350265 82322131383403170262699)
                  ·
                    rfl

theorem cell20_180362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_180362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180362 prefixEnd_180362 := by exact prefixLift 180362
  have htrace : WordTrace (prefixWord ++ tailWord_180362) baseStart_180362 baseEnd_180362 := by
    simpa [prefixWord, tailWord_180362, baseEnd_180362] using wordTrace_append hprefix tailTrace_180362
  have hstable : (prefixWord ++ tailWord_180362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180362).length < 2 ^ (prefixWord ++ tailWord_180362).sum := by decide
  have hdescent : baseEnd_180362 < baseStart_180362 := by decide
  rcases family_descends (prefixWord ++ tailWord_180362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180383 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_180383 : Nat := 118140960795 + 180383 * 2 ^ 59
def prefixEnd_180383 : Nat := 4983230072969 + 3 ^ 40 * 180383 * 2
def baseEnd_180383 : Nat := 82331716355620430562613

theorem tailTrace_180383 : CollatzResearch.WordTrace tailWord_180383 prefixEnd_180383 82331716355620430562613 := by
  unfold tailWord_180383
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579108505510672808841803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4386072337007115205894535 6579108505510672808841803)
  ·
    refine ⟨9868662758266009213262705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6579108505510672808841803 9868662758266009213262705)
    ·
      refine ⟨7401497068699506909947029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9868662758266009213262705 7401497068699506909947029)
      ·
        refine ⟨346945175095289386403767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7401497068699506909947029 346945175095289386403767)
        ·
          refine ⟨520417762642934079605651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346945175095289386403767 520417762642934079605651)
          ·
            refine ⟨780626643964401119408477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520417762642934079605651 780626643964401119408477)
            ·
              refine ⟨292734991486650419778179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780626643964401119408477 292734991486650419778179)
              ·
                refine ⟨439102487229975629667269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292734991486650419778179 439102487229975629667269)
                ·
                  refine ⟨82331716355620430562613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439102487229975629667269 82331716355620430562613)
                  ·
                    rfl

theorem cell20_180383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_180383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180383 prefixEnd_180383 := by exact prefixLift 180383
  have htrace : WordTrace (prefixWord ++ tailWord_180383) baseStart_180383 baseEnd_180383 := by
    simpa [prefixWord, tailWord_180383, baseEnd_180383] using wordTrace_append hprefix tailTrace_180383
  have hstable : (prefixWord ++ tailWord_180383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180383).length < 2 ^ (prefixWord ++ tailWord_180383).sum := by decide
  have hdescent : baseEnd_180383 < baseStart_180383 := by decide
  rcases family_descends (prefixWord ++ tailWord_180383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180425 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_180425 : Nat := 118140960795 + 180425 * 2 ^ 59
def prefixEnd_180425 : Nat := 4983230072969 + 3 ^ 40 * 180425 * 2
def baseEnd_180425 : Nat := 82350886300054951162441

theorem tailTrace_180425 : CollatzResearch.WordTrace tailWord_180425 prefixEnd_180425 82350886300054951162441 := by
  unfold tailWord_180425
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580640371358513981870729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4387093580905675987913819 6580640371358513981870729)
  ·
    refine ⟨4935480278518885486403047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6580640371358513981870729 4935480278518885486403047)
    ·
      refine ⟨7403220417778328229604571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935480278518885486403047 7403220417778328229604571)
      ·
        refine ⟨11104830626667492344406857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403220417778328229604571 11104830626667492344406857)
        ·
          refine ⟨8328622970000619258305143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11104830626667492344406857 8328622970000619258305143)
          ·
            refine ⟨12492934455000928887457715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328622970000619258305143 12492934455000928887457715)
            ·
              refine ⟨18739401682501393331186573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492934455000928887457715 18739401682501393331186573)
              ·
                refine ⟨7027275630938022499194965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18739401682501393331186573 7027275630938022499194965)
                ·
                  refine ⟨82350886300054951162441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7027275630938022499194965 82350886300054951162441)
                  ·
                    rfl

theorem cell20_180425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_180425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180425 prefixEnd_180425 := by exact prefixLift 180425
  have htrace : WordTrace (prefixWord ++ tailWord_180425) baseStart_180425 baseEnd_180425 := by
    simpa [prefixWord, tailWord_180425, baseEnd_180425] using wordTrace_append hprefix tailTrace_180425
  have hstable : (prefixWord ++ tailWord_180425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180425).length < 2 ^ (prefixWord ++ tailWord_180425).sum := by decide
  have hdescent : baseEnd_180425 < baseStart_180425 := by decide
  rcases family_descends (prefixWord ++ tailWord_180425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180428 : List Nat := [2, 2, 1, 6, 1, 8]
def baseStart_180428 : Nat := 118140960795 + 180428 * 2 ^ 59
def prefixEnd_180428 : Nat := 4983230072969 + 3 ^ 40 * 180428 * 2
def baseEnd_180428 : Nat := 3050083540066676817127

theorem tailTrace_180428 : CollatzResearch.WordTrace tailWord_180428 prefixEnd_180428 3050083540066676817127 := by
  unfold tailWord_180428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290374895173822747114969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4387166526898430329486625 3290374895173822747114969)
  ·
    refine ⟨2467781171380367060336227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3290374895173822747114969 2467781171380367060336227)
    ·
      refine ⟨3701671757070550590504341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467781171380367060336227 3701671757070550590504341)
      ·
        refine ⟨173515863612682058929891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3701671757070550590504341 173515863612682058929891)
        ·
          refine ⟨260273795419023088394837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173515863612682058929891 260273795419023088394837)
          ·
            refine ⟨3050083540066676817127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 260273795419023088394837 3050083540066676817127)
            ·
              rfl

theorem cell20_180428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 8].length) (baseStart_180428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180428 prefixEnd_180428 := by exact prefixLift 180428
  have htrace : WordTrace (prefixWord ++ tailWord_180428) baseStart_180428 baseEnd_180428 := by
    simpa [prefixWord, tailWord_180428, baseEnd_180428] using wordTrace_append hprefix tailTrace_180428
  have hstable : (prefixWord ++ tailWord_180428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180428).length < 2 ^ (prefixWord ++ tailWord_180428).sum := by decide
  have hdescent : baseEnd_180428 < baseStart_180428 := by decide
  rcases family_descends (prefixWord ++ tailWord_180428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180445 : List Nat := [1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_180445 : Nat := 118140960795 + 180445 * 2 ^ 59
def prefixEnd_180445 : Nat := 4983230072969 + 3 ^ 40 * 180445 * 2
def baseEnd_180445 : Nat := 27453338281674590165231

theorem tailTrace_180445 : CollatzResearch.WordTrace tailWord_180445 prefixEnd_180445 27453338281674590165231 := by
  unfold tailWord_180445
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581369831286057397598789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4387579887524038265065859 6581369831286057397598789)
  ·
    refine ⟨1234006843366135762049773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6581369831286057397598789 1234006843366135762049773)
    ·
      refine ⟨462752566262300910768665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1234006843366135762049773 462752566262300910768665)
      ·
        refine ⟨347064424696725683076499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462752566262300910768665 347064424696725683076499)
        ·
          refine ⟨520596637045088524614749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347064424696725683076499 520596637045088524614749)
          ·
            refine ⟨195223738891908196730531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 520596637045088524614749 195223738891908196730531)
            ·
              refine ⟨292835608337862295095797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195223738891908196730531 292835608337862295095797)
              ·
                refine ⟨27453338281674590165231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292835608337862295095797 27453338281674590165231)
                ·
                  rfl

theorem cell20_180445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_180445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180445 prefixEnd_180445 := by exact prefixLift 180445
  have htrace : WordTrace (prefixWord ++ tailWord_180445) baseStart_180445 baseEnd_180445 := by
    simpa [prefixWord, tailWord_180445, baseEnd_180445] using wordTrace_append hprefix tailTrace_180445
  have hstable : (prefixWord ++ tailWord_180445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180445).length < 2 ^ (prefixWord ++ tailWord_180445).sum := by decide
  have hdescent : baseEnd_180445 < baseStart_180445 := by decide
  rcases family_descends (prefixWord ++ tailWord_180445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180476 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_180476 : Nat := 118140960795 + 180476 * 2 ^ 59
def prefixEnd_180476 : Nat := 4983230072969 + 3 ^ 40 * 180476 * 2
def baseEnd_180476 : Nat := 82374164089725440462233

theorem tailTrace_180476 : CollatzResearch.WordTrace tailWord_180476 prefixEnd_180476 82374164089725440462233 := by
  unfold tailWord_180476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291250247086874845988641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4388333662782499794651521 3291250247086874845988641)
  ·
    refine ⟨2468437685315156134491481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3291250247086874845988641 2468437685315156134491481)
    ·
      refine ⟨1851328263986367100868611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2468437685315156134491481 1851328263986367100868611)
      ·
        refine ⟨2776992395979550651302917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851328263986367100868611 2776992395979550651302917)
        ·
          refine ⟨520686074246165747119297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2776992395979550651302917 520686074246165747119297)
          ·
            refine ⟨390514555684624310339473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520686074246165747119297 390514555684624310339473)
            ·
              refine ⟨292885916763468232754605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390514555684624310339473 292885916763468232754605)
              ·
                refine ⟨109832218786300587282977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292885916763468232754605 109832218786300587282977)
                ·
                  refine ⟨82374164089725440462233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109832218786300587282977 82374164089725440462233)
                  ·
                    rfl

theorem cell20_180476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_180476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180476 prefixEnd_180476 := by exact prefixLift 180476
  have htrace : WordTrace (prefixWord ++ tailWord_180476) baseStart_180476 baseEnd_180476 := by
    simpa [prefixWord, tailWord_180476, baseEnd_180476] using wordTrace_append hprefix tailTrace_180476
  have hstable : (prefixWord ++ tailWord_180476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180476).length < 2 ^ (prefixWord ++ tailWord_180476).sum := by decide
  have hdescent : baseEnd_180476 < baseStart_180476 := by decide
  rcases family_descends (prefixWord ++ tailWord_180476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180497 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 2]
def baseStart_180497 : Nat := 118140960795 + 180497 * 2 ^ 59
def prefixEnd_180497 : Nat := 4983230072969 + 3 ^ 40 * 180497 * 2
def baseEnd_180497 : Nat := 82383749061942700762147

theorem tailTrace_180497 : CollatzResearch.WordTrace tailWord_180497 prefixEnd_180497 82383749061942700762147 := by
  unfold tailWord_180497
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583266427097670278491745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4388844284731780185661163 6583266427097670278491745)
  ·
    refine ⟨4937449820323252708868809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6583266427097670278491745 4937449820323252708868809)
    ·
      refine ⟨3703087365242439531651607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4937449820323252708868809 3703087365242439531651607)
      ·
        refine ⟨5554631047863659297477411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703087365242439531651607 5554631047863659297477411)
        ·
          refine ⟨8331946571795488946216117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5554631047863659297477411 8331946571795488946216117)
          ·
            refine ⟨781119991105827088707761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8331946571795488946216117 781119991105827088707761)
            ·
              refine ⟨585839993329370316530821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781119991105827088707761 585839993329370316530821)
              ·
                refine ⟨109844998749256934349529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585839993329370316530821 109844998749256934349529)
                ·
                  refine ⟨82383749061942700762147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109844998749256934349529 82383749061942700762147)
                  ·
                    rfl

theorem cell20_180497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_180497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180497 prefixEnd_180497 := by exact prefixLift 180497
  have htrace : WordTrace (prefixWord ++ tailWord_180497) baseStart_180497 baseEnd_180497 := by
    simpa [prefixWord, tailWord_180497, baseEnd_180497] using wordTrace_append hprefix tailTrace_180497
  have hstable : (prefixWord ++ tailWord_180497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180497).length < 2 ^ (prefixWord ++ tailWord_180497).sum := by decide
  have hdescent : baseEnd_180497 < baseStart_180497 := by decide
  rcases family_descends (prefixWord ++ tailWord_180497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180542 : List Nat := [4, 2, 1, 2, 1, 4, 6]
def baseStart_180542 : Nat := 118140960795 + 180542 * 2 ^ 59
def prefixEnd_180542 : Nat := 4983230072969 + 3 ^ 40 * 180542 * 2
def baseEnd_180542 : Nat := 9156032032013616029107

theorem tailTrace_180542 : CollatzResearch.WordTrace tailWord_180542 prefixEnd_180542 9156032032013616029107 := by
  unfold tailWord_180542
  simp only [CollatzResearch.WordTrace]
  refine ⟨823113463991830370484985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4389938474623095309253253 823113463991830370484985)
  ·
    refine ⟨617335097993872777863739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 823113463991830370484985 617335097993872777863739)
    ·
      refine ⟨926002646990809166795609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617335097993872777863739 926002646990809166795609)
      ·
        refine ⟨694501985243106875096707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926002646990809166795609 694501985243106875096707)
        ·
          refine ⟨1041752977864660312645061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694501985243106875096707 1041752977864660312645061)
          ·
            refine ⟨195328683349623808620949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1041752977864660312645061 195328683349623808620949)
            ·
              refine ⟨9156032032013616029107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195328683349623808620949 9156032032013616029107)
              ·
                rfl

theorem cell20_180542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_180542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180542 prefixEnd_180542 := by exact prefixLift 180542
  have htrace : WordTrace (prefixWord ++ tailWord_180542) baseStart_180542 baseEnd_180542 := by
    simpa [prefixWord, tailWord_180542, baseEnd_180542] using wordTrace_append hprefix tailTrace_180542
  have hstable : (prefixWord ++ tailWord_180542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180542).length < 2 ^ (prefixWord ++ tailWord_180542).sum := by decide
  have hdescent : baseEnd_180542 < baseStart_180542 := by decide
  rcases family_descends (prefixWord ++ tailWord_180542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180548 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_180548 : Nat := 118140960795 + 180548 * 2 ^ 59
def prefixEnd_180548 : Nat := 4983230072969 + 3 ^ 40 * 180548 * 2
def baseEnd_180548 : Nat := 82407026851613190061939

theorem tailTrace_180548 : CollatzResearch.WordTrace tailWord_180548 prefixEnd_180548 82407026851613190061939 := by
  unfold tailWord_180548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292563274956452994299149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4390084366608603992398865 3292563274956452994299149)
  ·
    refine ⟨1234711228108669872862181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3292563274956452994299149 1234711228108669872862181)
    ·
      refine ⟨231508355270375601161659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1234711228108669872862181 231508355270375601161659)
      ·
        refine ⟨347262532905563401742489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231508355270375601161659 347262532905563401742489)
        ·
          refine ⟨260446899679172551306867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347262532905563401742489 260446899679172551306867)
          ·
            refine ⟨390670349518758826960301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260446899679172551306867 390670349518758826960301)
            ·
              refine ⟨146501381069534560110113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390670349518758826960301 146501381069534560110113)
              ·
                refine ⟨109876035802150920082585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146501381069534560110113 109876035802150920082585)
                ·
                  refine ⟨82407026851613190061939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109876035802150920082585 82407026851613190061939)
                  ·
                    rfl

theorem cell20_180548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_180548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180548 prefixEnd_180548 := by exact prefixLift 180548
  have htrace : WordTrace (prefixWord ++ tailWord_180548) baseStart_180548 baseEnd_180548 := by
    simpa [prefixWord, tailWord_180548, baseEnd_180548] using wordTrace_append hprefix tailTrace_180548
  have hstable : (prefixWord ++ tailWord_180548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180548).length < 2 ^ (prefixWord ++ tailWord_180548).sum := by decide
  have hdescent : baseEnd_180548 < baseStart_180548 := by decide
  rcases family_descends (prefixWord ++ tailWord_180548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180632 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_180632 : Nat := 118140960795 + 180632 * 2 ^ 59
def prefixEnd_180632 : Nat := 4983230072969 + 3 ^ 40 * 180632 * 2
def baseEnd_180632 : Nat := 82445366740482231261595

theorem tailTrace_180632 : CollatzResearch.WordTrace tailWord_180632 prefixEnd_180632 82445366740482231261595 := by
  unfold tailWord_180632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294095140804294167328075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4392126854405725556437433 3294095140804294167328075)
  ·
    refine ⟨4941142711206441250992113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3294095140804294167328075 4941142711206441250992113)
    ·
      refine ⟨3705857033404830938244085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4941142711206441250992113 3705857033404830938244085)
      ·
        refine ⟨347424096881702900460383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3705857033404830938244085 347424096881702900460383)
        ·
          refine ⟨521136145322554350690575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347424096881702900460383 521136145322554350690575)
          ·
            refine ⟨781704217983831526035863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521136145322554350690575 781704217983831526035863)
            ·
              refine ⟨1172556326975747289053795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781704217983831526035863 1172556326975747289053795)
              ·
                refine ⟨1758834490463620933580693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172556326975747289053795 1758834490463620933580693)
                ·
                  refine ⟨82445366740482231261595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1758834490463620933580693 82445366740482231261595)
                  ·
                    rfl

theorem cell20_180632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_180632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180632 prefixEnd_180632 := by exact prefixLift 180632
  have htrace : WordTrace (prefixWord ++ tailWord_180632) baseStart_180632 baseEnd_180632 := by
    simpa [prefixWord, tailWord_180632, baseEnd_180632] using wordTrace_append hprefix tailTrace_180632
  have hstable : (prefixWord ++ tailWord_180632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180632).length < 2 ^ (prefixWord ++ tailWord_180632).sum := by decide
  have hdescent : baseEnd_180632 < baseStart_180632 := by decide
  rcases family_descends (prefixWord ++ tailWord_180632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180663 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_180663 : Nat := 118140960795 + 180663 * 2 ^ 59
def prefixEnd_180663 : Nat := 4983230072969 + 3 ^ 40 * 180663 * 2
def baseEnd_180663 : Nat := 82459515985183901228135

theorem tailTrace_180663 : CollatzResearch.WordTrace tailWord_180663 prefixEnd_180663 82459515985183901228135 := by
  unfold tailWord_180663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589320944496280629034643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4392880629664187086023095 6589320944496280629034643)
  ·
    refine ⟨9883981416744420943551965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6589320944496280629034643 9883981416744420943551965)
    ·
      refine ⟨3706493031279157853831987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9883981416744420943551965 3706493031279157853831987)
      ·
        refine ⟨5559739546918736780747981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706493031279157853831987 5559739546918736780747981)
        ·
          refine ⟨2084902330094526292780493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5559739546918736780747981 2084902330094526292780493)
          ·
            refine ⟨781838373785447359792685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2084902330094526292780493 781838373785447359792685)
            ·
              refine ⟨293189390169542759922257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 781838373785447359792685 293189390169542759922257)
              ·
                refine ⟨219892042627157069941693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293189390169542759922257 219892042627157069941693)
                ·
                  refine ⟨82459515985183901228135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219892042627157069941693 82459515985183901228135)
                  ·
                    rfl

theorem cell20_180663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_180663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180663 prefixEnd_180663 := by exact prefixLift 180663
  have htrace : WordTrace (prefixWord ++ tailWord_180663) baseStart_180663 baseEnd_180663 := by
    simpa [prefixWord, tailWord_180663, baseEnd_180663] using wordTrace_append hprefix tailTrace_180663
  have hstable : (prefixWord ++ tailWord_180663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180663).length < 2 ^ (prefixWord ++ tailWord_180663).sum := by decide
  have hdescent : baseEnd_180663 < baseStart_180663 := by decide
  rcases family_descends (prefixWord ++ tailWord_180663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180670 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_180670 : Nat := 118140960795 + 180670 * 2 ^ 59
def prefixEnd_180670 : Nat := 4983230072969 + 3 ^ 40 * 180670 * 2
def baseEnd_180670 : Nat := 82462710975922987994773

theorem tailTrace_180670 : CollatzResearch.WordTrace tailWord_180670 prefixEnd_180670 82462710975922987994773 := by
  unfold tailWord_180670
  simp only [CollatzResearch.WordTrace]
  refine ⟨823697031933865103067433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4393050836980613883026309 823697031933865103067433)
  ·
    refine ⟨617772773950398827300575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 823697031933865103067433 617772773950398827300575)
    ·
      refine ⟨926659160925598240950863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617772773950398827300575 926659160925598240950863)
      ·
        refine ⟨1389988741388397361426295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926659160925598240950863 1389988741388397361426295)
        ·
          refine ⟨2084983112082596042139443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389988741388397361426295 2084983112082596042139443)
          ·
            refine ⟨3127474668123894063209165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084983112082596042139443 3127474668123894063209165)
            ·
              refine ⟨1172803000546460273703437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3127474668123894063209165 1172803000546460273703437)
              ·
                refine ⟨439801125204922602638789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172803000546460273703437 439801125204922602638789)
                ·
                  refine ⟨82462710975922987994773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439801125204922602638789 82462710975922987994773)
                  ·
                    rfl

theorem cell20_180670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_180670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180670 prefixEnd_180670 := by exact prefixLift 180670
  have htrace : WordTrace (prefixWord ++ tailWord_180670) baseStart_180670 baseEnd_180670 := by
    simpa [prefixWord, tailWord_180670, baseEnd_180670] using wordTrace_append hprefix tailTrace_180670
  have hstable : (prefixWord ++ tailWord_180670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180670).length < 2 ^ (prefixWord ++ tailWord_180670).sum := by decide
  have hdescent : baseEnd_180670 < baseStart_180670 := by decide
  rcases family_descends (prefixWord ++ tailWord_180670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180680 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_180680 : Nat := 118140960795 + 180680 * 2 ^ 59
def prefixEnd_180680 : Nat := 4983230072969 + 3 ^ 40 * 180680 * 2
def baseEnd_180680 : Nat := 82467275248407397661399

theorem tailTrace_180680 : CollatzResearch.WordTrace tailWord_180680 prefixEnd_180680 82467275248407397661399 := by
  unfold tailWord_180680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294970492717346266201747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4393293990289795021602329 3294970492717346266201747)
  ·
    refine ⟨4942455739076019399302621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3294970492717346266201747 4942455739076019399302621)
    ·
      refine ⟨1853420902153507274738483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4942455739076019399302621 1853420902153507274738483)
      ·
        refine ⟨2780131353230260912107725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853420902153507274738483 2780131353230260912107725)
        ·
          refine ⟨1042549257461347842040397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2780131353230260912107725 1042549257461347842040397)
          ·
            refine ⟨390955971548005440765149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1042549257461347842040397 390955971548005440765149)
            ·
              refine ⟨146608489330502040286931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390955971548005440765149 146608489330502040286931)
              ·
                refine ⟨219912733995753060430397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146608489330502040286931 219912733995753060430397)
                ·
                  refine ⟨82467275248407397661399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219912733995753060430397 82467275248407397661399)
                  ·
                    rfl

theorem cell20_180680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_180680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180680 prefixEnd_180680 := by exact prefixLift 180680
  have htrace : WordTrace (prefixWord ++ tailWord_180680) baseStart_180680 baseEnd_180680 := by
    simpa [prefixWord, tailWord_180680, baseEnd_180680] using wordTrace_append hprefix tailTrace_180680
  have hstable : (prefixWord ++ tailWord_180680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180680).length < 2 ^ (prefixWord ++ tailWord_180680).sum := by decide
  have hdescent : baseEnd_180680 < baseStart_180680 := by decide
  rcases family_descends (prefixWord ++ tailWord_180680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180690 : List Nat := [3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_180690 : Nat := 118140960795 + 180690 * 2 ^ 59
def prefixEnd_180690 : Nat := 4983230072969 + 3 ^ 40 * 180690 * 2
def baseEnd_180690 : Nat := 27490613173630602442675

theorem tailTrace_180690 : CollatzResearch.WordTrace tailWord_180690 prefixEnd_180690 27490613173630602442675 := by
  unfold tailWord_180690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647576428849616060066881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4393537143598976160178349 1647576428849616060066881)
  ·
    refine ⟨1235682321637212045050161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1647576428849616060066881 1235682321637212045050161)
    ·
      refine ⟨926761741227909033787621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235682321637212045050161 926761741227909033787621)
      ·
        refine ⟨173767826480232943835179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 926761741227909033787621 173767826480232943835179)
        ·
          refine ⟨260651739720349415752769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173767826480232943835179 260651739720349415752769)
          ·
            refine ⟨195488804790262061814577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260651739720349415752769 195488804790262061814577)
            ·
              refine ⟨146616603592696546360933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195488804790262061814577 146616603592696546360933)
              ·
                refine ⟨27490613173630602442675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146616603592696546360933 27490613173630602442675)
                ·
                  rfl

theorem cell20_180690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_180690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180690 prefixEnd_180690 := by exact prefixLift 180690
  have htrace : WordTrace (prefixWord ++ tailWord_180690) baseStart_180690 baseEnd_180690 := by
    simpa [prefixWord, tailWord_180690, baseEnd_180690] using wordTrace_append hprefix tailTrace_180690
  have hstable : (prefixWord ++ tailWord_180690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180690).length < 2 ^ (prefixWord ++ tailWord_180690).sum := by decide
  have hdescent : baseEnd_180690 < baseStart_180690 := by decide
  rcases family_descends (prefixWord ++ tailWord_180690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180694 : List Nat := [5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_180694 : Nat := 118140960795 + 180694 * 2 ^ 59
def prefixEnd_180694 : Nat := 4983230072969 + 3 ^ 40 * 180694 * 2
def baseEnd_180694 : Nat := 27491221743295190398225

theorem tailTrace_180694 : CollatzResearch.WordTrace tailWord_180694 prefixEnd_180694 27491221743295190398225 := by
  unfold tailWord_180694
  simp only [CollatzResearch.WordTrace]
  refine ⟨411903225461498307713321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4393634404922648615608757 411903225461498307713321)
  ·
    refine ⟨308927419096123730784991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 411903225461498307713321 308927419096123730784991)
    ·
      refine ⟨463391128644185596177487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308927419096123730784991 463391128644185596177487)
      ·
        refine ⟨695086692966278394266231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463391128644185596177487 695086692966278394266231)
        ·
          refine ⟨1042630039449417591399347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695086692966278394266231 1042630039449417591399347)
          ·
            refine ⟨1563945059174126387099021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042630039449417591399347 1563945059174126387099021)
            ·
              refine ⟨586479397190297395162133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1563945059174126387099021 586479397190297395162133)
              ·
                refine ⟨27491221743295190398225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 586479397190297395162133 27491221743295190398225)
                ·
                  rfl

theorem cell20_180694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_180694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180694 prefixEnd_180694 := by exact prefixLift 180694
  have htrace : WordTrace (prefixWord ++ tailWord_180694) baseStart_180694 baseEnd_180694 := by
    simpa [prefixWord, tailWord_180694, baseEnd_180694] using wordTrace_append hprefix tailTrace_180694
  have hstable : (prefixWord ++ tailWord_180694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180694).length < 2 ^ (prefixWord ++ tailWord_180694).sum := by decide
  have hdescent : baseEnd_180694 < baseStart_180694 := by decide
  rcases family_descends (prefixWord ++ tailWord_180694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180749 : List Nat := [1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_180749 : Nat := 118140960795 + 180749 * 2 ^ 59
def prefixEnd_180749 : Nat := 4983230072969 + 3 ^ 40 * 180749 * 2
def baseEnd_180749 : Nat := 27499589576183274787039

theorem tailTrace_180749 : CollatzResearch.WordTrace tailWord_180749 prefixEnd_180749 27499589576183274787039 := by
  unfold tailWord_180749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592457622184717316665301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4394971748123144877776867 6592457622184717316665301)
  ·
    refine ⟨154510725519954312109343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6592457622184717316665301 154510725519954312109343)
    ·
      refine ⟨231766088279931468164015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154510725519954312109343 231766088279931468164015)
      ·
        refine ⟨347649132419897202246023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231766088279931468164015 347649132419897202246023)
        ·
          refine ⟨521473698629845803369035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347649132419897202246023 521473698629845803369035)
          ·
            refine ⟨782210547944768705053553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521473698629845803369035 782210547944768705053553)
            ·
              refine ⟨586657910958576528790165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782210547944768705053553 586657910958576528790165)
              ·
                refine ⟨27499589576183274787039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 586657910958576528790165 27499589576183274787039)
                ·
                  rfl

theorem cell20_180749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_180749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180749 prefixEnd_180749 := by exact prefixLift 180749
  have htrace : WordTrace (prefixWord ++ tailWord_180749) baseStart_180749 baseEnd_180749 := by
    simpa [prefixWord, tailWord_180749, baseEnd_180749] using wordTrace_append hprefix tailTrace_180749
  have hstable : (prefixWord ++ tailWord_180749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180749).length < 2 ^ (prefixWord ++ tailWord_180749).sum := by decide
  have hdescent : baseEnd_180749 < baseStart_180749 := by decide
  rcases family_descends (prefixWord ++ tailWord_180749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180805 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_180805 : Nat := 118140960795 + 180805 * 2 ^ 59
def prefixEnd_180805 : Nat := 4983230072969 + 3 ^ 40 * 180805 * 2
def baseEnd_180805 : Nat := 82524328654462518494221

theorem tailTrace_180805 : CollatzResearch.WordTrace tailWord_180805 prefixEnd_180805 82524328654462518494221 := by
  unfold tailWord_180805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594500109981838880703869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4396333406654559253802579 6594500109981838880703869)
  ·
    refine ⟨2472937541243189580263951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6594500109981838880703869 2472937541243189580263951)
    ·
      refine ⟨3709406311864784370395927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2472937541243189580263951 3709406311864784370395927)
      ·
        refine ⟨5564109467797176555593891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709406311864784370395927 5564109467797176555593891)
        ·
          refine ⟨8346164201695764833390837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564109467797176555593891 8346164201695764833390837)
          ·
            refine ⟨782452893908977953130391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8346164201695764833390837 782452893908977953130391)
            ·
              refine ⟨1173679340863466929695587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782452893908977953130391 1173679340863466929695587)
              ·
                refine ⟨1760519011295200394543381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173679340863466929695587 1760519011295200394543381)
                ·
                  refine ⟨82524328654462518494221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1760519011295200394543381 82524328654462518494221)
                  ·
                    rfl

theorem cell20_180805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_180805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180805 prefixEnd_180805 := by exact prefixLift 180805
  have htrace : WordTrace (prefixWord ++ tailWord_180805) baseStart_180805 baseEnd_180805 := by
    simpa [prefixWord, tailWord_180805, baseEnd_180805] using wordTrace_append hprefix tailTrace_180805
  have hstable : (prefixWord ++ tailWord_180805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180805).length < 2 ^ (prefixWord ++ tailWord_180805).sum := by decide
  have hdescent : baseEnd_180805 < baseStart_180805 := by decide
  rcases family_descends (prefixWord ++ tailWord_180805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180836 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_180836 : Nat := 118140960795 + 180836 * 2 ^ 59
def prefixEnd_180836 : Nat := 4983230072969 + 3 ^ 40 * 180836 * 2
def baseEnd_180836 : Nat := 82538477899164188460761

theorem tailTrace_180836 : CollatzResearch.WordTrace tailWord_180836 prefixEnd_180836 82538477899164188460761 := by
  unfold tailWord_180836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297815386434765587541181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4397087181913020783388241 3297815386434765587541181)
  ·
    refine ⟨1236680769913037095327943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3297815386434765587541181 1236680769913037095327943)
    ·
      refine ⟨1855021154869555642991915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236680769913037095327943 1855021154869555642991915)
      ·
        refine ⟨2782531732304333464487873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855021154869555642991915 2782531732304333464487873)
        ·
          refine ⟨2086898799228250098365905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2782531732304333464487873 2086898799228250098365905)
          ·
            refine ⟨1565174099421187573774429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086898799228250098365905 1565174099421187573774429)
            ·
              refine ⟨586940287282945340165411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565174099421187573774429 586940287282945340165411)
              ·
                refine ⟨880410430924418010248117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586940287282945340165411 880410430924418010248117)
                ·
                  refine ⟨82538477899164188460761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 880410430924418010248117 82538477899164188460761)
                  ·
                    rfl

theorem cell20_180836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_180836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180836 prefixEnd_180836 := by exact prefixLift 180836
  have htrace : WordTrace (prefixWord ++ tailWord_180836) baseStart_180836 baseEnd_180836 := by
    simpa [prefixWord, tailWord_180836, baseEnd_180836] using wordTrace_append hprefix tailTrace_180836
  have hstable : (prefixWord ++ tailWord_180836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180836).length < 2 ^ (prefixWord ++ tailWord_180836).sum := by decide
  have hdescent : baseEnd_180836 < baseStart_180836 := by decide
  rcases family_descends (prefixWord ++ tailWord_180836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180867 : List Nat := [1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_180867 : Nat := 118140960795 + 180867 * 2 ^ 59
def prefixEnd_180867 : Nat := 4983230072969 + 3 ^ 40 * 180867 * 2
def baseEnd_180867 : Nat := 27517542381288619475767

theorem tailTrace_180867 : CollatzResearch.WordTrace tailWord_180867 prefixEnd_180867 27517542381288619475767 := by
  unfold tailWord_180867
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596761435757223469460855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4397840957171482312973903 6596761435757223469460855)
  ·
    refine ⟨9895142153635835204191283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6596761435757223469460855 9895142153635835204191283)
    ·
      refine ⟨14842713230453752806286925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9895142153635835204191283 14842713230453752806286925)
      ·
        refine ⟨5566017461420157302357597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14842713230453752806286925 5566017461420157302357597)
        ·
          refine ⟨2087256548032558988384099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5566017461420157302357597 2087256548032558988384099)
          ·
            refine ⟨3130884822048838482576149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087256548032558988384099 3130884822048838482576149)
            ·
              refine ⟨146760226033539303870757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3130884822048838482576149 146760226033539303870757)
              ·
                refine ⟨27517542381288619475767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146760226033539303870757 27517542381288619475767)
                ·
                  rfl

theorem cell20_180867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_180867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180867 prefixEnd_180867 := by exact prefixLift 180867
  have htrace : WordTrace (prefixWord ++ tailWord_180867) baseStart_180867 baseEnd_180867 := by
    simpa [prefixWord, tailWord_180867, baseEnd_180867] using wordTrace_append hprefix tailTrace_180867
  have hstable : (prefixWord ++ tailWord_180867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180867).length < 2 ^ (prefixWord ++ tailWord_180867).sum := by decide
  have hdescent : baseEnd_180867 < baseStart_180867 := by decide
  rcases family_descends (prefixWord ++ tailWord_180867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180884 : List Nat := [2, 4, 2, 2, 1, 3, 6]
def baseStart_180884 : Nat := 118140960795 + 180884 * 2 ^ 59
def prefixEnd_180884 : Nat := 4983230072969 + 3 ^ 40 * 180884 * 2
def baseEnd_180884 : Nat := 9173376267454372762285

theorem tailTrace_180884 : CollatzResearch.WordTrace tailWord_180884 prefixEnd_180884 9173376267454372762285 := by
  unfold tailWord_180884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298690738347817686414853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4398254317797090248553137 3298690738347817686414853)
  ·
    refine ⟨618504513440215816202785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3298690738347817686414853 618504513440215816202785)
    ·
      refine ⟨463878385080161862152089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 618504513440215816202785 463878385080161862152089)
      ·
        refine ⟨347908788810121396614067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463878385080161862152089 347908788810121396614067)
        ·
          refine ⟨521863183215182094921101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347908788810121396614067 521863183215182094921101)
          ·
            refine ⟨195698693705693285595413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521863183215182094921101 195698693705693285595413)
            ·
              refine ⟨9173376267454372762285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195698693705693285595413 9173376267454372762285)
              ·
                rfl

theorem cell20_180884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_180884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180884 prefixEnd_180884 := by exact prefixLift 180884
  have htrace : WordTrace (prefixWord ++ tailWord_180884) baseStart_180884 baseEnd_180884 := by
    simpa [prefixWord, tailWord_180884, baseEnd_180884] using wordTrace_append hprefix tailTrace_180884
  have hstable : (prefixWord ++ tailWord_180884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180884).length < 2 ^ (prefixWord ++ tailWord_180884).sum := by decide
  have hdescent : baseEnd_180884 < baseStart_180884 := by decide
  rcases family_descends (prefixWord ++ tailWord_180884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180946 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_180946 : Nat := 118140960795 + 180946 * 2 ^ 59
def prefixEnd_180946 : Nat := 4983230072969 + 3 ^ 40 * 180946 * 2
def baseEnd_180946 : Nat := 82588684896492694793645

theorem tailTrace_180946 : CollatzResearch.WordTrace tailWord_180946 prefixEnd_180946 82588684896492694793645 := by
  unfold tailWord_180946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649910700617754990396673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4399761868314013307724461 1649910700617754990396673)
  ·
    refine ⟨1237433025463316242797505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1649910700617754990396673 1237433025463316242797505)
    ·
      refine ⟨928074769097487182098129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1237433025463316242797505 928074769097487182098129)
      ·
        refine ⟨696056076823115386573597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928074769097487182098129 696056076823115386573597)
        ·
          refine ⟨261021028808668269965099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696056076823115386573597 261021028808668269965099)
          ·
            refine ⟨391531543213002404947649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261021028808668269965099 391531543213002404947649)
            ·
              refine ⟨293648657409751803710737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391531543213002404947649 293648657409751803710737)
              ·
                refine ⟨220236493057313852783053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293648657409751803710737 220236493057313852783053)
                ·
                  refine ⟨82588684896492694793645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220236493057313852783053 82588684896492694793645)
                  ·
                    rfl

theorem cell20_180946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_180946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180946 prefixEnd_180946 := by exact prefixLift 180946
  have htrace : WordTrace (prefixWord ++ tailWord_180946) baseStart_180946 baseEnd_180946 := by
    simpa [prefixWord, tailWord_180946, baseEnd_180946] using wordTrace_append hprefix tailTrace_180946
  have hstable : (prefixWord ++ tailWord_180946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180946).length < 2 ^ (prefixWord ++ tailWord_180946).sum := by decide
  have hdescent : baseEnd_180946 < baseStart_180946 := by decide
  rcases family_descends (prefixWord ++ tailWord_180946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180971 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_180971 : Nat := 118140960795 + 180971 * 2 ^ 59
def prefixEnd_180971 : Nat := 4983230072969 + 3 ^ 40 * 180971 * 2
def baseEnd_180971 : Nat := 82600095577703718960209

theorem tailTrace_180971 : CollatzResearch.WordTrace tailWord_180971 prefixEnd_180971 82600095577703718960209 := by
  unfold tailWord_180971
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600554627380449231246767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4400369751586966154164511 6600554627380449231246767)
  ·
    refine ⟨9900831941070673846870151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6600554627380449231246767 9900831941070673846870151)
    ·
      refine ⟨14851247911606010770305227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900831941070673846870151 14851247911606010770305227)
      ·
        refine ⟨22276871867409016155457841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14851247911606010770305227 22276871867409016155457841)
        ·
          refine ⟨16707653900556762116593381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22276871867409016155457841 16707653900556762116593381)
          ·
            refine ⟨3132685106354392896861259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16707653900556762116593381 3132685106354392896861259)
            ·
              refine ⟨4699027659531589345291889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132685106354392896861259 4699027659531589345291889)
              ·
                refine ⟨3524270744648692008968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699027659531589345291889 3524270744648692008968917)
                ·
                  refine ⟨82600095577703718960209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3524270744648692008968917 82600095577703718960209)
                  ·
                    rfl

theorem cell20_180971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_180971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180971 prefixEnd_180971 := by exact prefixLift 180971
  have htrace : WordTrace (prefixWord ++ tailWord_180971) baseStart_180971 baseEnd_180971 := by
    simpa [prefixWord, tailWord_180971, baseEnd_180971] using wordTrace_append hprefix tailTrace_180971
  have hstable : (prefixWord ++ tailWord_180971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180971).length < 2 ^ (prefixWord ++ tailWord_180971).sum := by decide
  have hdescent : baseEnd_180971 < baseStart_180971 := by decide
  rcases family_descends (prefixWord ++ tailWord_180971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180974 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_180974 : Nat := 118140960795 + 180974 * 2 ^ 59
def prefixEnd_180974 : Nat := 4983230072969 + 3 ^ 40 * 180974 * 2
def baseEnd_180974 : Nat := 82601464859449041860197

theorem tailTrace_180974 : CollatzResearch.WordTrace tailWord_180974 prefixEnd_180974 82601464859449041860197 := by
  unfold tailWord_180974
  simp only [CollatzResearch.WordTrace]
  refine ⟨825083005796197592950747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4400442697579720495737317 825083005796197592950747)
  ·
    refine ⟨1237624508694296389426121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 825083005796197592950747 1237624508694296389426121)
    ·
      refine ⟨928218381520722292069591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1237624508694296389426121 928218381520722292069591)
      ·
        refine ⟨1392327572281083438104387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928218381520722292069591 1392327572281083438104387)
        ·
          refine ⟨2088491358421625157156581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392327572281083438104387 2088491358421625157156581)
          ·
            refine ⟨391592129704054716966859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2088491358421625157156581 391592129704054716966859)
            ·
              refine ⟨587388194556082075450289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391592129704054716966859 587388194556082075450289)
              ·
                refine ⟨440541145917061556587717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587388194556082075450289 440541145917061556587717)
                ·
                  refine ⟨82601464859449041860197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440541145917061556587717 82601464859449041860197)
                  ·
                    rfl

theorem cell20_180974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_180974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_180974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_180974 prefixEnd_180974 := by exact prefixLift 180974
  have htrace : WordTrace (prefixWord ++ tailWord_180974) baseStart_180974 baseEnd_180974 := by
    simpa [prefixWord, tailWord_180974, baseEnd_180974] using wordTrace_append hprefix tailTrace_180974
  have hstable : (prefixWord ++ tailWord_180974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180974).length < 2 ^ (prefixWord ++ tailWord_180974).sum := by decide
  have hdescent : baseEnd_180974 < baseStart_180974 := by decide
  rcases family_descends (prefixWord ++ tailWord_180974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181002 : List Nat := [3, 1, 2, 2, 1, 2, 9]
def baseStart_181002 : Nat := 118140960795 + 181002 * 2 ^ 59
def prefixEnd_181002 : Nat := 4983230072969 + 3 ^ 40 * 181002 * 2
def baseEnd_181002 : Nat := 9179360535822820991861

theorem tailTrace_181002 : CollatzResearch.WordTrace tailWord_181002 prefixEnd_181002 9179360535822820991861 := by
  unfold tailWord_181002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650421322567035381406315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4401123526845427683750173 1650421322567035381406315)
  ·
    refine ⟨2475631983850553072109473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1650421322567035381406315 2475631983850553072109473)
    ·
      refine ⟨1856723987887914804082105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2475631983850553072109473 1856723987887914804082105)
      ·
        refine ⟨1392542990915936103061579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856723987887914804082105 1392542990915936103061579)
        ·
          refine ⟨2088814486373904154592369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392542990915936103061579 2088814486373904154592369)
          ·
            refine ⟨1566610864780428115944277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088814486373904154592369 1566610864780428115944277)
            ·
              refine ⟨9179360535822820991861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1566610864780428115944277 9179360535822820991861)
              ·
                rfl

theorem cell20_181002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_181002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181002 prefixEnd_181002 := by exact prefixLift 181002
  have htrace : WordTrace (prefixWord ++ tailWord_181002) baseStart_181002 baseEnd_181002 := by
    simpa [prefixWord, tailWord_181002, baseEnd_181002] using wordTrace_append hprefix tailTrace_181002
  have hstable : (prefixWord ++ tailWord_181002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181002).length < 2 ^ (prefixWord ++ tailWord_181002).sum := by decide
  have hdescent : baseEnd_181002 < baseStart_181002 := by decide
  rcases family_descends (prefixWord ++ tailWord_181002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181047 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_181047 : Nat := 118140960795 + 181047 * 2 ^ 59
def prefixEnd_181047 : Nat := 4983230072969 + 3 ^ 40 * 181047 * 2
def baseEnd_181047 : Nat := 82634784048585232426565

theorem tailTrace_181047 : CollatzResearch.WordTrace tailWord_181047 prefixEnd_181047 82634784048585232426565 := by
  unfold tailWord_181047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603326575105114211013395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4402217716736742807342263 6603326575105114211013395)
  ·
    refine ⟨9904989862657671316520093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6603326575105114211013395 9904989862657671316520093)
    ·
      refine ⟨3714371198496626743695035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9904989862657671316520093 3714371198496626743695035)
      ·
        refine ⟨5571556797744940115542553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3714371198496626743695035 5571556797744940115542553)
        ·
          refine ⟨4178667598308705086656915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5571556797744940115542553 4178667598308705086656915)
          ·
            refine ⟨6268001397463057629985373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178667598308705086656915 6268001397463057629985373)
            ·
              refine ⟨2350500524048646611244515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6268001397463057629985373 2350500524048646611244515)
              ·
                refine ⟨3525750786072969916866773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350500524048646611244515 3525750786072969916866773)
                ·
                  refine ⟨82634784048585232426565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3525750786072969916866773 82634784048585232426565)
                  ·
                    rfl

theorem cell20_181047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_181047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181047 prefixEnd_181047 := by exact prefixLift 181047
  have htrace : WordTrace (prefixWord ++ tailWord_181047) baseStart_181047 baseEnd_181047 := by
    simpa [prefixWord, tailWord_181047, baseEnd_181047] using wordTrace_append hprefix tailTrace_181047
  have hstable : (prefixWord ++ tailWord_181047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181047).length < 2 ^ (prefixWord ++ tailWord_181047).sum := by decide
  have hdescent : baseEnd_181047 < baseStart_181047 := by decide
  rcases family_descends (prefixWord ++ tailWord_181047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181064 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_181064 : Nat := 118140960795 + 181064 * 2 ^ 59
def prefixEnd_181064 : Nat := 4983230072969 + 3 ^ 40 * 181064 * 2
def baseEnd_181064 : Nat := 82642543311808728859829

theorem tailTrace_181064 : CollatzResearch.WordTrace tailWord_181064 prefixEnd_181064 82642543311808728859829 := by
  unfold tailWord_181064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301973308021763057191123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4402631077362350742921497 3301973308021763057191123)
  ·
    refine ⟨4952959962032644585786685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3301973308021763057191123 4952959962032644585786685)
    ·
      refine ⟨1857359985762241719670007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4952959962032644585786685 1857359985762241719670007)
      ·
        refine ⟨2786039978643362579505011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857359985762241719670007 2786039978643362579505011)
        ·
          refine ⟨4179059967965043869257517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786039978643362579505011 4179059967965043869257517)
          ·
            refine ⟨1567147487986891450971569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4179059967965043869257517 1567147487986891450971569)
            ·
              refine ⟨1175360615990168588228677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567147487986891450971569 1175360615990168588228677)
              ·
                refine ⟨220380115498156610292877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1175360615990168588228677 220380115498156610292877)
                ·
                  refine ⟨82642543311808728859829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220380115498156610292877 82642543311808728859829)
                  ·
                    rfl

theorem cell20_181064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_181064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181064 prefixEnd_181064 := by exact prefixLift 181064
  have htrace : WordTrace (prefixWord ++ tailWord_181064) baseStart_181064 baseEnd_181064 := by
    simpa [prefixWord, tailWord_181064, baseEnd_181064] using wordTrace_append hprefix tailTrace_181064
  have hstable : (prefixWord ++ tailWord_181064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181064).length < 2 ^ (prefixWord ++ tailWord_181064).sum := by decide
  have hdescent : baseEnd_181064 < baseStart_181064 := by decide
  rcases family_descends (prefixWord ++ tailWord_181064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181081 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 3]
def baseStart_181081 : Nat := 118140960795 + 181081 * 2 ^ 59
def prefixEnd_181081 : Nat := 4983230072969 + 3 ^ 40 * 181081 * 2
def baseEnd_181081 : Nat := 82650302575032225293093

theorem tailTrace_181081 : CollatzResearch.WordTrace tailWord_181081 prefixEnd_181081 82650302575032225293093 := by
  unfold tailWord_181081
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604566656981938017751097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4403044437987958678500731 6604566656981938017751097)
  ·
    refine ⟨4953424992736453513313323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6604566656981938017751097 4953424992736453513313323)
    ·
      refine ⟨7430137489104680269969985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953424992736453513313323 7430137489104680269969985)
      ·
        refine ⟨5572603116828510202477489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7430137489104680269969985 5572603116828510202477489)
        ·
          refine ⟨4179452337621382651858117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5572603116828510202477489 4179452337621382651858117)
          ·
            refine ⟨783647313304009247223397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4179452337621382651858117 783647313304009247223397)
            ·
              refine ⟨146933871244501733854387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 783647313304009247223397 146933871244501733854387)
              ·
                refine ⟨220400806866752600781581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146933871244501733854387 220400806866752600781581)
                ·
                  refine ⟨82650302575032225293093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220400806866752600781581 82650302575032225293093)
                  ·
                    rfl

theorem cell20_181081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_181081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181081 prefixEnd_181081 := by exact prefixLift 181081
  have htrace : WordTrace (prefixWord ++ tailWord_181081) baseStart_181081 baseEnd_181081 := by
    simpa [prefixWord, tailWord_181081, baseEnd_181081] using wordTrace_append hprefix tailTrace_181081
  have hstable : (prefixWord ++ tailWord_181081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181081).length < 2 ^ (prefixWord ++ tailWord_181081).sum := by decide
  have hdescent : baseEnd_181081 < baseStart_181081 := by decide
  rcases family_descends (prefixWord ++ tailWord_181081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181118 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_181118 : Nat := 118140960795 + 181118 * 2 ^ 59
def prefixEnd_181118 : Nat := 4983230072969 + 3 ^ 40 * 181118 * 2
def baseEnd_181118 : Nat := 82667190383224541059609

theorem tailTrace_181118 : CollatzResearch.WordTrace tailWord_181118 prefixEnd_181118 82667190383224541059609 := by
  unfold tailWord_181118
  simp only [CollatzResearch.WordTrace]
  refine ⟨825739519730986667106001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4403944105231928891232005 825739519730986667106001)
  ·
    refine ⟨619304639798240000329501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 825739519730986667106001 619304639798240000329501)
    ·
      refine ⟨232239239924340000123563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 619304639798240000329501 232239239924340000123563)
      ·
        refine ⟨348358859886510000185345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232239239924340000123563 348358859886510000185345)
        ·
          refine ⟨261269144914882500139009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348358859886510000185345 261269144914882500139009)
          ·
            refine ⟨195951858686161875104257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261269144914882500139009 195951858686161875104257)
            ·
              refine ⟨146963894014621406328193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195951858686161875104257 146963894014621406328193)
              ·
                refine ⟨110222920510966054746145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146963894014621406328193 110222920510966054746145)
                ·
                  refine ⟨82667190383224541059609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110222920510966054746145 82667190383224541059609)
                  ·
                    rfl

theorem cell20_181118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_181118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181118 prefixEnd_181118 := by exact prefixLift 181118
  have htrace : WordTrace (prefixWord ++ tailWord_181118) baseStart_181118 baseEnd_181118 := by
    simpa [prefixWord, tailWord_181118, baseEnd_181118] using wordTrace_append hprefix tailTrace_181118
  have hstable : (prefixWord ++ tailWord_181118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181118).length < 2 ^ (prefixWord ++ tailWord_181118).sum := by decide
  have hdescent : baseEnd_181118 < baseStart_181118 := by decide
  rcases family_descends (prefixWord ++ tailWord_181118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181161 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_181161 : Nat := 118140960795 + 181161 * 2 ^ 59
def prefixEnd_181161 : Nat := 4983230072969 + 3 ^ 40 * 181161 * 2
def baseEnd_181161 : Nat := 82686816754907502626099

theorem tailTrace_181161 : CollatzResearch.WordTrace tailWord_181161 prefixEnd_181161 82686816754907502626099 := by
  unfold tailWord_181161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607484496692111680663337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4404989664461407787108891 6607484496692111680663337)
  ·
    refine ⟨4955613372519083760497503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6607484496692111680663337 4955613372519083760497503)
    ·
      refine ⟨7433420058778625640746255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955613372519083760497503 7433420058778625640746255)
      ·
        refine ⟨11150130088167938461119383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7433420058778625640746255 11150130088167938461119383)
        ·
          refine ⟨16725195132251907691679075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150130088167938461119383 16725195132251907691679075)
          ·
            refine ⟨25087792698377861537518613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16725195132251907691679075 25087792698377861537518613)
            ·
              refine ⟨1175990282736462259571185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25087792698377861537518613 1175990282736462259571185)
              ·
                refine ⟨881992712052346694678389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175990282736462259571185 881992712052346694678389)
                ·
                  refine ⟨82686816754907502626099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 881992712052346694678389 82686816754907502626099)
                  ·
                    rfl

theorem cell20_181161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_181161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181161 prefixEnd_181161 := by exact prefixLift 181161
  have htrace : WordTrace (prefixWord ++ tailWord_181161) baseStart_181161 baseEnd_181161 := by
    simpa [prefixWord, tailWord_181161, baseEnd_181161] using wordTrace_append hprefix tailTrace_181161
  have hstable : (prefixWord ++ tailWord_181161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181161).length < 2 ^ (prefixWord ++ tailWord_181161).sum := by decide
  have hdescent : baseEnd_181161 < baseStart_181161 := by decide
  rcases family_descends (prefixWord ++ tailWord_181161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181195 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 3]
def baseStart_181195 : Nat := 118140960795 + 181195 * 2 ^ 59
def prefixEnd_181195 : Nat := 4983230072969 + 3 ^ 40 * 181195 * 2
def baseEnd_181195 : Nat := 82702335281354495492627

theorem tailTrace_181195 : CollatzResearch.WordTrace tailWord_181195 prefixEnd_181195 82702335281354495492627 := by
  unfold tailWord_181195
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608724578568935487401039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4405816385712623658267359 6608724578568935487401039)
  ·
    refine ⟨9913086867853403231101559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608724578568935487401039 9913086867853403231101559)
    ·
      refine ⟨14869630301780104846652339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9913086867853403231101559 14869630301780104846652339)
      ·
        refine ⟨22304445452670157269978509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14869630301780104846652339 22304445452670157269978509)
        ·
          refine ⟨8364167044751308976241941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22304445452670157269978509 8364167044751308976241941)
          ·
            refine ⟨392070330222717608261341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8364167044751308976241941 392070330222717608261341)
            ·
              refine ⟨147026373833519103098003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392070330222717608261341 147026373833519103098003)
              ·
                refine ⟨220539560750278654647005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147026373833519103098003 220539560750278654647005)
                ·
                  refine ⟨82702335281354495492627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220539560750278654647005 82702335281354495492627)
                  ·
                    rfl

theorem cell20_181195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_181195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181195 prefixEnd_181195 := by exact prefixLift 181195
  have htrace : WordTrace (prefixWord ++ tailWord_181195) baseStart_181195 baseEnd_181195 := by
    simpa [prefixWord, tailWord_181195, baseEnd_181195] using wordTrace_append hprefix tailTrace_181195
  have hstable : (prefixWord ++ tailWord_181195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181195).length < 2 ^ (prefixWord ++ tailWord_181195).sum := by decide
  have hdescent : baseEnd_181195 < baseStart_181195 := by decide
  rcases family_descends (prefixWord ++ tailWord_181195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181202 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_181202 : Nat := 118140960795 + 181202 * 2 ^ 59
def prefixEnd_181202 : Nat := 4983230072969 + 3 ^ 40 * 181202 * 2
def baseEnd_181202 : Nat := 82705530272093582259265

theorem tailTrace_181202 : CollatzResearch.WordTrace tailWord_181202 prefixEnd_181202 82705530272093582259265 := by
  unfold tailWord_181202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652244972385893920726465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4405986593029050455270573 1652244972385893920726465)
  ·
    refine ⟨1239183729289420440544849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1652244972385893920726465 1239183729289420440544849)
    ·
      refine ⟨929387796967065330408637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1239183729289420440544849 929387796967065330408637)
      ·
        refine ⟨348520423862649498903239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 929387796967065330408637 348520423862649498903239)
        ·
          refine ⟨522780635793974248354859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348520423862649498903239 522780635793974248354859)
          ·
            refine ⟨784170953690961372532289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522780635793974248354859 784170953690961372532289)
            ·
              refine ⟨588128215268221029399217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784170953690961372532289 588128215268221029399217)
              ·
                refine ⟨441096161451165772049413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588128215268221029399217 441096161451165772049413)
                ·
                  refine ⟨82705530272093582259265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441096161451165772049413 82705530272093582259265)
                  ·
                    rfl

theorem cell20_181202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_181202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181202 prefixEnd_181202 := by exact prefixLift 181202
  have htrace : WordTrace (prefixWord ++ tailWord_181202) baseStart_181202 baseEnd_181202 := by
    simpa [prefixWord, tailWord_181202, baseEnd_181202] using wordTrace_append hprefix tailTrace_181202
  have hstable : (prefixWord ++ tailWord_181202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181202).length < 2 ^ (prefixWord ++ tailWord_181202).sum := by decide
  have hdescent : baseEnd_181202 < baseStart_181202 := by decide
  rcases family_descends (prefixWord ++ tailWord_181202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181205 : List Nat := [1, 3, 2, 3, 4, 1, 2, 4]
def baseStart_181205 : Nat := 118140960795 + 181205 * 2 ^ 59
def prefixEnd_181205 : Nat := 4983230072969 + 3 ^ 40 * 181205 * 2
def baseEnd_181205 : Nat := 27568966517946301719751

theorem tailTrace_181205 : CollatzResearch.WordTrace tailWord_181205 prefixEnd_181205 27568966517946301719751 := by
  unfold tailWord_181205
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609089308532707195265069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4406059539021804796843379 6609089308532707195265069)
  ·
    refine ⟨2478408490699765198224401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6609089308532707195265069 2478408490699765198224401)
    ·
      refine ⟨1858806368024823898668301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478408490699765198224401 1858806368024823898668301)
      ·
        refine ⟨697052388009308962000613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1858806368024823898668301 697052388009308962000613)
        ·
          refine ⟨130697322751745430375115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 697052388009308962000613 130697322751745430375115)
          ·
            refine ⟨196045984127618145562673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130697322751745430375115 196045984127618145562673)
            ·
              refine ⟨147034488095713609172005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196045984127618145562673 147034488095713609172005)
              ·
                refine ⟨27568966517946301719751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147034488095713609172005 27568966517946301719751)
                ·
                  rfl

theorem cell20_181205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_181205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181205 prefixEnd_181205 := by exact prefixLift 181205
  have htrace : WordTrace (prefixWord ++ tailWord_181205) baseStart_181205 baseEnd_181205 := by
    simpa [prefixWord, tailWord_181205, baseEnd_181205] using wordTrace_append hprefix tailTrace_181205
  have hstable : (prefixWord ++ tailWord_181205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181205).length < 2 ^ (prefixWord ++ tailWord_181205).sum := by decide
  have hdescent : baseEnd_181205 < baseStart_181205 := by decide
  rcases family_descends (prefixWord ++ tailWord_181205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181209 : List Nat := [1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_181209 : Nat := 118140960795 + 181209 * 2 ^ 59
def prefixEnd_181209 : Nat := 4983230072969 + 3 ^ 40 * 181209 * 2
def baseEnd_181209 : Nat := 27569575087610889675301

theorem tailTrace_181209 : CollatzResearch.WordTrace tailWord_181209 prefixEnd_181209 27569575087610889675301 := by
  unfold tailWord_181209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609235200518215878410681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4406156800345477252273787 6609235200518215878410681)
  ·
    refine ⟨4956926400388661908808011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6609235200518215878410681 4956926400388661908808011)
    ·
      refine ⟨7435389600582992863212017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956926400388661908808011 7435389600582992863212017)
      ·
        refine ⟨5576542200437244647409013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7435389600582992863212017 5576542200437244647409013)
        ·
          refine ⟨522800831290991685694595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5576542200437244647409013 522800831290991685694595)
          ·
            refine ⟨784201246936487528541893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522800831290991685694595 784201246936487528541893)
            ·
              refine ⟨147037733800591411601605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 784201246936487528541893 147037733800591411601605)
              ·
                refine ⟨27569575087610889675301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147037733800591411601605 27569575087610889675301)
                ·
                  rfl

theorem cell20_181209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_181209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181209 prefixEnd_181209 := by exact prefixLift 181209
  have htrace : WordTrace (prefixWord ++ tailWord_181209) baseStart_181209 baseEnd_181209 := by
    simpa [prefixWord, tailWord_181209, baseEnd_181209] using wordTrace_append hprefix tailTrace_181209
  have hstable : (prefixWord ++ tailWord_181209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181209).length < 2 ^ (prefixWord ++ tailWord_181209).sum := by decide
  have hdescent : baseEnd_181209 < baseStart_181209 := by decide
  rcases family_descends (prefixWord ++ tailWord_181209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181246 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_181246 : Nat := 118140960795 + 181246 * 2 ^ 59
def prefixEnd_181246 : Nat := 4983230072969 + 3 ^ 40 * 181246 * 2
def baseEnd_181246 : Nat := 82725613071024984792419

theorem tailTrace_181246 : CollatzResearch.WordTrace tailWord_181246 prefixEnd_181246 82725613071024984792419 := by
  unfold tailWord_181246
  simp only [CollatzResearch.WordTrace]
  refine ⟨826323087673021399688449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4407056467589447465005061 826323087673021399688449)
  ·
    refine ⟨619742315754766049766337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 826323087673021399688449 619742315754766049766337)
    ·
      refine ⟨464806736816074537324753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 619742315754766049766337 464806736816074537324753)
      ·
        refine ⟨348605052612055902993565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464806736816074537324753 348605052612055902993565)
        ·
          refine ⟨130726894729520963622587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348605052612055902993565 130726894729520963622587)
          ·
            refine ⟨196090342094281445433881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130726894729520963622587 196090342094281445433881)
            ·
              refine ⟨147067756570711084075411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196090342094281445433881 147067756570711084075411)
              ·
                refine ⟨220601634856066626113117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147067756570711084075411 220601634856066626113117)
                ·
                  refine ⟨82725613071024984792419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220601634856066626113117 82725613071024984792419)
                  ·
                    rfl

theorem cell20_181246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_181246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181246 prefixEnd_181246 := by exact prefixLift 181246
  have htrace : WordTrace (prefixWord ++ tailWord_181246) baseStart_181246 baseEnd_181246 := by
    simpa [prefixWord, tailWord_181246, baseEnd_181246] using wordTrace_append hprefix tailTrace_181246
  have hstable : (prefixWord ++ tailWord_181246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181246).length < 2 ^ (prefixWord ++ tailWord_181246).sum := by decide
  have hdescent : baseEnd_181246 < baseStart_181246 := by decide
  rcases family_descends (prefixWord ++ tailWord_181246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181292 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_181292 : Nat := 118140960795 + 181292 * 2 ^ 59
def prefixEnd_181292 : Nat := 4983230072969 + 3 ^ 40 * 181292 * 2
def baseEnd_181292 : Nat := 82746608724453269258897

theorem tailTrace_181292 : CollatzResearch.WordTrace tailWord_181292 prefixEnd_181292 82746608724453269258897 := by
  unfold tailWord_181292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306131229608760526841065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4408174972811680702454753 3306131229608760526841065)
  ·
    refine ⟨2479598422206570395130799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3306131229608760526841065 2479598422206570395130799)
    ·
      refine ⟨3719397633309855592696199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479598422206570395130799 3719397633309855592696199)
      ·
        refine ⟨5579096449964783389044299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719397633309855592696199 5579096449964783389044299)
        ·
          refine ⟨8368644674947175083566449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579096449964783389044299 8368644674947175083566449)
          ·
            refine ⟨6276483506210381312674837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8368644674947175083566449 6276483506210381312674837)
            ·
              refine ⟨294210164353611624031633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6276483506210381312674837 294210164353611624031633)
              ·
                refine ⟨220657623265208718023725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294210164353611624031633 220657623265208718023725)
                ·
                  refine ⟨82746608724453269258897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220657623265208718023725 82746608724453269258897)
                  ·
                    rfl

theorem cell20_181292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_181292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181292 prefixEnd_181292 := by exact prefixLift 181292
  have htrace : WordTrace (prefixWord ++ tailWord_181292) baseStart_181292 baseEnd_181292 := by
    simpa [prefixWord, tailWord_181292, baseEnd_181292] using wordTrace_append hprefix tailTrace_181292
  have hstable : (prefixWord ++ tailWord_181292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181292).length < 2 ^ (prefixWord ++ tailWord_181292).sum := by decide
  have hdescent : baseEnd_181292 < baseStart_181292 := by decide
  rcases family_descends (prefixWord ++ tailWord_181292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181302 : List Nat := [5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_181302 : Nat := 118140960795 + 181302 * 2 ^ 59
def prefixEnd_181302 : Nat := 4983230072969 + 3 ^ 40 * 181302 * 2
def baseEnd_181302 : Nat := 27583724332312559641841

theorem tailTrace_181302 : CollatzResearch.WordTrace tailWord_181302 prefixEnd_181302 27583724332312559641841 := by
  unfold tailWord_181302
  simp only [CollatzResearch.WordTrace]
  refine ⟨413289199323830797596635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4408418126120861841030773 413289199323830797596635)
  ·
    refine ⟨619933798985746196394953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413289199323830797596635 619933798985746196394953)
    ·
      refine ⟨464950349239309647296215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 619933798985746196394953 464950349239309647296215)
      ·
        refine ⟨697425523858964470944323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464950349239309647296215 697425523858964470944323)
        ·
          refine ⟨1046138285788446706416485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697425523858964470944323 1046138285788446706416485)
          ·
            refine ⟨196150928585333757453091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1046138285788446706416485 196150928585333757453091)
            ·
              refine ⟨294226392878000636179637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196150928585333757453091 294226392878000636179637)
              ·
                refine ⟨27583724332312559641841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294226392878000636179637 27583724332312559641841)
                ·
                  rfl

theorem cell20_181302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_181302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181302 prefixEnd_181302 := by exact prefixLift 181302
  have htrace : WordTrace (prefixWord ++ tailWord_181302) baseStart_181302 baseEnd_181302 := by
    simpa [prefixWord, tailWord_181302, baseEnd_181302] using wordTrace_append hprefix tailTrace_181302
  have hstable : (prefixWord ++ tailWord_181302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181302).length < 2 ^ (prefixWord ++ tailWord_181302).sum := by decide
  have hdescent : baseEnd_181302 < baseStart_181302 := by decide
  rcases family_descends (prefixWord ++ tailWord_181302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181306 : List Nat := [3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_181306 : Nat := 118140960795 + 181306 * 2 ^ 59
def prefixEnd_181306 : Nat := 4983230072969 + 3 ^ 40 * 181306 * 2
def baseEnd_181306 : Nat := 27584332901977147597391

theorem tailTrace_181306 : CollatzResearch.WordTrace tailWord_181306 prefixEnd_181306 27584332901977147597391 := by
  unfold tailWord_181306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653193270291700361172943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4408515387444534296461181 1653193270291700361172943)
  ·
    refine ⟨2479789905437550541759415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653193270291700361172943 2479789905437550541759415)
    ·
      refine ⟨3719684858156325812639123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479789905437550541759415 3719684858156325812639123)
      ·
        refine ⟨5579527287234488718958685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719684858156325812639123 5579527287234488718958685)
        ·
          refine ⟨2092322732712933269609507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5579527287234488718958685 2092322732712933269609507)
          ·
            refine ⟨3138484099069399904414261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092322732712933269609507 3138484099069399904414261)
            ·
              refine ⟨294232884287756241038837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3138484099069399904414261 294232884287756241038837)
              ·
                refine ⟨27584332901977147597391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294232884287756241038837 27584332901977147597391)
                ·
                  rfl

theorem cell20_181306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_181306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181306 prefixEnd_181306 := by exact prefixLift 181306
  have htrace : WordTrace (prefixWord ++ tailWord_181306) baseStart_181306 baseEnd_181306 := by
    simpa [prefixWord, tailWord_181306, baseEnd_181306] using wordTrace_append hprefix tailTrace_181306
  have hstable : (prefixWord ++ tailWord_181306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181306).length < 2 ^ (prefixWord ++ tailWord_181306).sum := by decide
  have hdescent : baseEnd_181306 < baseStart_181306 := by decide
  rcases family_descends (prefixWord ++ tailWord_181306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181354 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_181354 : Nat := 118140960795 + 181354 * 2 ^ 59
def prefixEnd_181354 : Nat := 4983230072969 + 3 ^ 40 * 181354 * 2
def baseEnd_181354 : Nat := 82774907213856609191977

theorem tailTrace_181354 : CollatzResearch.WordTrace tailWord_181354 prefixEnd_181354 82774907213856609191977 := by
  unfold tailWord_181354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653630946248226410609779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4409682523328603761626077 1653630946248226410609779)
  ·
    refine ⟨2480446419372339615914669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653630946248226410609779 2480446419372339615914669)
    ·
      refine ⟨930167407264627355968001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2480446419372339615914669 930167407264627355968001)
      ·
        refine ⟨697625555448470516976001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 930167407264627355968001 697625555448470516976001)
        ·
          refine ⟨523219166586352887732001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697625555448470516976001 523219166586352887732001)
          ·
            refine ⟨392414374939764665799001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523219166586352887732001 392414374939764665799001)
            ·
              refine ⟨294310781204823499349251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392414374939764665799001 294310781204823499349251)
              ·
                refine ⟨441466171807235249023877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294310781204823499349251 441466171807235249023877)
                ·
                  refine ⟨82774907213856609191977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441466171807235249023877 82774907213856609191977)
                  ·
                    rfl

theorem cell20_181354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_181354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181354 prefixEnd_181354 := by exact prefixLift 181354
  have htrace : WordTrace (prefixWord ++ tailWord_181354) baseStart_181354 baseEnd_181354 := by
    simpa [prefixWord, tailWord_181354, baseEnd_181354] using wordTrace_append hprefix tailTrace_181354
  have hstable : (prefixWord ++ tailWord_181354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181354).length < 2 ^ (prefixWord ++ tailWord_181354).sum := by decide
  have hdescent : baseEnd_181354 < baseStart_181354 := by decide
  rcases family_descends (prefixWord ++ tailWord_181354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181409 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 2]
def baseStart_181409 : Nat := 118140960795 + 181409 * 2 ^ 59
def prefixEnd_181409 : Nat := 4983230072969 + 3 ^ 40 * 181409 * 2
def baseEnd_181409 : Nat := 82800010712520862358419

theorem tailTrace_181409 : CollatzResearch.WordTrace tailWord_181409 prefixEnd_181409 82800010712520862358419 := by
  unfold tailWord_181409
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616529799793650035691281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4411019866529100023794187 6616529799793650035691281)
  ·
    refine ⟨4962397349845237526768461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6616529799793650035691281 4962397349845237526768461)
    ·
      refine ⟨1860899006191964072538173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4962397349845237526768461 1860899006191964072538173)
      ·
        refine ⟨697837127321986527201815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1860899006191964072538173 697837127321986527201815)
        ·
          refine ⟨1046755690982979790802723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697837127321986527201815 1046755690982979790802723)
          ·
            refine ⟨1570133536474469686204085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046755690982979790802723 1570133536474469686204085)
            ·
              refine ⟨147200019044481533081633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1570133536474469686204085 147200019044481533081633)
              ·
                refine ⟨110400014283361149811225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147200019044481533081633 110400014283361149811225)
                ·
                  refine ⟨82800010712520862358419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110400014283361149811225 82800010712520862358419)
                  ·
                    rfl

theorem cell20_181409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_181409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181409 prefixEnd_181409 := by exact prefixLift 181409
  have htrace : WordTrace (prefixWord ++ tailWord_181409) baseStart_181409 baseEnd_181409 := by
    simpa [prefixWord, tailWord_181409, baseEnd_181409] using wordTrace_append hprefix tailTrace_181409
  have hstable : (prefixWord ++ tailWord_181409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181409).length < 2 ^ (prefixWord ++ tailWord_181409).sum := by decide
  have hdescent : baseEnd_181409 < baseStart_181409 := by decide
  rcases family_descends (prefixWord ++ tailWord_181409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181413 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_181413 : Nat := 118140960795 + 181413 * 2 ^ 59
def prefixEnd_181413 : Nat := 4983230072969 + 3 ^ 40 * 181413 * 2
def baseEnd_181413 : Nat := 82801836421514626225069

theorem tailTrace_181413 : CollatzResearch.WordTrace tailWord_181413 prefixEnd_181413 82801836421514626225069 := by
  unfold tailWord_181413
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616675691779158718836893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4411117127852772479224595 6616675691779158718836893)
  ·
    refine ⟨2481253384417184519563835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6616675691779158718836893 2481253384417184519563835)
    ·
      refine ⟨3721880076625776779345753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481253384417184519563835 3721880076625776779345753)
      ·
        refine ⟨2791410057469332584509315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3721880076625776779345753 2791410057469332584509315)
        ·
          refine ⟨4187115086203998876763973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791410057469332584509315 4187115086203998876763973)
          ·
            refine ⟨785084078663249789393245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4187115086203998876763973 785084078663249789393245)
            ·
              refine ⟨294406529498718671022467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 785084078663249789393245 294406529498718671022467)
              ·
                refine ⟨441609794248078006533701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294406529498718671022467 441609794248078006533701)
                ·
                  refine ⟨82801836421514626225069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441609794248078006533701 82801836421514626225069)
                  ·
                    rfl

theorem cell20_181413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_181413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181413 prefixEnd_181413 := by exact prefixLift 181413
  have htrace : WordTrace (prefixWord ++ tailWord_181413) baseStart_181413 baseEnd_181413 := by
    simpa [prefixWord, tailWord_181413, baseEnd_181413] using wordTrace_append hprefix tailTrace_181413
  have hstable : (prefixWord ++ tailWord_181413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181413).length < 2 ^ (prefixWord ++ tailWord_181413).sum := by decide
  have hdescent : baseEnd_181413 < baseStart_181413 := by decide
  rcases family_descends (prefixWord ++ tailWord_181413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181434 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_181434 : Nat := 118140960795 + 181434 * 2 ^ 59
def prefixEnd_181434 : Nat := 4983230072969 + 3 ^ 40 * 181434 * 2
def baseEnd_181434 : Nat := 82811421393731886524983

theorem tailTrace_181434 : CollatzResearch.WordTrace tailWord_181434 prefixEnd_181434 82811421393731886524983 := by
  unfold tailWord_181434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654360406175769826337839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4411627749802052870234237 1654360406175769826337839)
  ·
    refine ⟨2481540609263654739506759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654360406175769826337839 2481540609263654739506759)
    ·
      refine ⟨3722310913895482109260139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481540609263654739506759 3722310913895482109260139)
      ·
        refine ⟨5583466370843223163890209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722310913895482109260139 5583466370843223163890209)
        ·
          refine ⟨4187599778132417372917657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5583466370843223163890209 4187599778132417372917657)
          ·
            refine ⟨3140699833599313029688243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187599778132417372917657 3140699833599313029688243)
            ·
              refine ⟨4711049750398969544532365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140699833599313029688243 4711049750398969544532365)
              ·
                refine ⟨1766643656399613579199637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4711049750398969544532365 1766643656399613579199637)
                ·
                  refine ⟨82811421393731886524983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1766643656399613579199637 82811421393731886524983)
                  ·
                    rfl

theorem cell20_181434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_181434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181434 prefixEnd_181434 := by exact prefixLift 181434
  have htrace : WordTrace (prefixWord ++ tailWord_181434) baseStart_181434 baseEnd_181434 := by
    simpa [prefixWord, tailWord_181434, baseEnd_181434] using wordTrace_append hprefix tailTrace_181434
  have hstable : (prefixWord ++ tailWord_181434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181434).length < 2 ^ (prefixWord ++ tailWord_181434).sum := by decide
  have hdescent : baseEnd_181434 < baseStart_181434 := by decide
  rcases family_descends (prefixWord ++ tailWord_181434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181460 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_181460 : Nat := 118140960795 + 181460 * 2 ^ 59
def prefixEnd_181460 : Nat := 4983230072969 + 3 ^ 40 * 181460 * 2
def baseEnd_181460 : Nat := 82823288502191351658211

theorem tailTrace_181460 : CollatzResearch.WordTrace tailWord_181460 prefixEnd_181460 82823288502191351658211 := by
  unfold tailWord_181460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309194961304442872898917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4412259948405923830531889 3309194961304442872898917)
  ·
    refine ⟨620474055244583038668547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3309194961304442872898917 620474055244583038668547)
    ·
      refine ⟨930711082866874558002821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620474055244583038668547 930711082866874558002821)
      ·
        refine ⟨174508328037538979625529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 930711082866874558002821 174508328037538979625529)
        ·
          refine ⟨130881246028154234719147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174508328037538979625529 130881246028154234719147)
          ·
            refine ⟨196321869042231352078721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130881246028154234719147 196321869042231352078721)
            ·
              refine ⟨147241401781673514059041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196321869042231352078721 147241401781673514059041)
              ·
                refine ⟨110431051336255135544281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147241401781673514059041 110431051336255135544281)
                ·
                  refine ⟨82823288502191351658211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110431051336255135544281 82823288502191351658211)
                  ·
                    rfl

theorem cell20_181460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_181460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181460 prefixEnd_181460 := by exact prefixLift 181460
  have htrace : WordTrace (prefixWord ++ tailWord_181460) baseStart_181460 baseEnd_181460 := by
    simpa [prefixWord, tailWord_181460, baseEnd_181460] using wordTrace_append hprefix tailTrace_181460
  have hstable : (prefixWord ++ tailWord_181460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181460).length < 2 ^ (prefixWord ++ tailWord_181460).sum := by decide
  have hdescent : baseEnd_181460 < baseStart_181460 := by decide
  rcases family_descends (prefixWord ++ tailWord_181460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181461 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_181461 : Nat := 118140960795 + 181461 * 2 ^ 59
def prefixEnd_181461 : Nat := 4983230072969 + 3 ^ 40 * 181461 * 2
def baseEnd_181461 : Nat := 82823744929439792624873

theorem tailTrace_181461 : CollatzResearch.WordTrace tailWord_181461 prefixEnd_181461 82823744929439792624873 := by
  unfold tailWord_181461
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618426395605262916584237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4412284263736841944389491 6618426395605262916584237)
  ·
    refine ⟨2481909898351973593719089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6618426395605262916584237 2481909898351973593719089)
    ·
      refine ⟨1861432423763980195289317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2481909898351973593719089 1861432423763980195289317)
      ·
        refine ⟨349018579455746286616747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1861432423763980195289317 349018579455746286616747)
        ·
          refine ⟨523527869183619429925121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349018579455746286616747 523527869183619429925121)
          ·
            refine ⟨392645901887714572443841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523527869183619429925121 392645901887714572443841)
            ·
              refine ⟨294484426415785929332881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392645901887714572443841 294484426415785929332881)
              ·
                refine ⟨220863319811839446999661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294484426415785929332881 220863319811839446999661)
                ·
                  refine ⟨82823744929439792624873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220863319811839446999661 82823744929439792624873)
                  ·
                    rfl

theorem cell20_181461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_181461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181461 prefixEnd_181461 := by exact prefixLift 181461
  have htrace : WordTrace (prefixWord ++ tailWord_181461) baseStart_181461 baseEnd_181461 := by
    simpa [prefixWord, tailWord_181461, baseEnd_181461] using wordTrace_append hprefix tailTrace_181461
  have hstable : (prefixWord ++ tailWord_181461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181461).length < 2 ^ (prefixWord ++ tailWord_181461).sum := by decide
  have hdescent : baseEnd_181461 < baseStart_181461 := by decide
  rcases family_descends (prefixWord ++ tailWord_181461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181464 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_181464 : Nat := 118140960795 + 181464 * 2 ^ 59
def prefixEnd_181464 : Nat := 4983230072969 + 3 ^ 40 * 181464 * 2
def baseEnd_181464 : Nat := 82825114211185115524861

theorem tailTrace_181464 : CollatzResearch.WordTrace tailWord_181464 prefixEnd_181464 82825114211185115524861 := by
  unfold tailWord_181464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309267907297197214471723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4412357209729596285962297 3309267907297197214471723)
  ·
    refine ⟨4963901860945795821707585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3309267907297197214471723 4963901860945795821707585)
    ·
      refine ⟨3722926395709346866280689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4963901860945795821707585 3722926395709346866280689)
      ·
        refine ⟨2792194796782010149710517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3722926395709346866280689 2792194796782010149710517)
        ·
          refine ⟨261768262198313451535361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2792194796782010149710517 261768262198313451535361)
          ·
            refine ⟨196326196648735088651521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261768262198313451535361 196326196648735088651521)
            ·
              refine ⟨147244647486551316488641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196326196648735088651521 147244647486551316488641)
              ·
                refine ⟨110433485614913487366481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147244647486551316488641 110433485614913487366481)
                ·
                  refine ⟨82825114211185115524861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110433485614913487366481 82825114211185115524861)
                  ·
                    rfl

theorem cell20_181464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_181464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181464 prefixEnd_181464 := by exact prefixLift 181464
  have htrace : WordTrace (prefixWord ++ tailWord_181464) baseStart_181464 baseEnd_181464 := by
    simpa [prefixWord, tailWord_181464, baseEnd_181464] using wordTrace_append hprefix tailTrace_181464
  have hstable : (prefixWord ++ tailWord_181464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181464).length < 2 ^ (prefixWord ++ tailWord_181464).sum := by decide
  have hdescent : baseEnd_181464 < baseStart_181464 := by decide
  rcases family_descends (prefixWord ++ tailWord_181464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181482 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_181482 : Nat := 118140960795 + 181482 * 2 ^ 59
def prefixEnd_181482 : Nat := 4983230072969 + 3 ^ 40 * 181482 * 2
def baseEnd_181482 : Nat := 82833329901657052924787

theorem tailTrace_181482 : CollatzResearch.WordTrace tailWord_181482 prefixEnd_181482 82833329901657052924787 := by
  unfold tailWord_181482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654798082132295875774675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4412794885686122335399133 1654798082132295875774675)
  ·
    refine ⟨2482197123198443813662013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654798082132295875774675 2482197123198443813662013)
    ·
      refine ⟨930823921199416430123255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2482197123198443813662013 930823921199416430123255)
      ·
        refine ⟨1396235881799124645184883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930823921199416430123255 1396235881799124645184883)
        ·
          refine ⟨2094353822698686967777325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396235881799124645184883 2094353822698686967777325)
          ·
            refine ⟨785382683512007612916497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2094353822698686967777325 785382683512007612916497)
            ·
              refine ⟨589037012634005709687373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785382683512007612916497 589037012634005709687373)
              ·
                refine ⟨220888879737752141132765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589037012634005709687373 220888879737752141132765)
                ·
                  refine ⟨82833329901657052924787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220888879737752141132765 82833329901657052924787)
                  ·
                    rfl

theorem cell20_181482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_181482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181482 prefixEnd_181482 := by exact prefixLift 181482
  have htrace : WordTrace (prefixWord ++ tailWord_181482) baseStart_181482 baseEnd_181482 := by
    simpa [prefixWord, tailWord_181482, baseEnd_181482] using wordTrace_append hprefix tailTrace_181482
  have hstable : (prefixWord ++ tailWord_181482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181482).length < 2 ^ (prefixWord ++ tailWord_181482).sum := by decide
  have hdescent : baseEnd_181482 < baseStart_181482 := by decide
  rcases family_descends (prefixWord ++ tailWord_181482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181527 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_181527 : Nat := 118140960795 + 181527 * 2 ^ 59
def prefixEnd_181527 : Nat := 4983230072969 + 3 ^ 40 * 181527 * 2
def baseEnd_181527 : Nat := 82853869127836896424603

theorem tailTrace_181527 : CollatzResearch.WordTrace tailWord_181527 prefixEnd_181527 82853869127836896424603 := by
  unfold tailWord_181527
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620833613366156188486835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4413889075577437458991223 6620833613366156188486835)
  ·
    refine ⟨9931250420049234282730253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6620833613366156188486835 9931250420049234282730253)
    ·
      refine ⟨3724218907518462856023845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9931250420049234282730253 3724218907518462856023845)
      ·
        refine ⟨698291045159711785504471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3724218907518462856023845 698291045159711785504471)
        ·
          refine ⟨1047436567739567678256707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698291045159711785504471 1047436567739567678256707)
          ·
            refine ⟨1571154851609351517385061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047436567739567678256707 1571154851609351517385061)
            ·
              refine ⟨294591534676753409509699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1571154851609351517385061 294591534676753409509699)
              ·
                refine ⟨441887302015130114264549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294591534676753409509699 441887302015130114264549)
                ·
                  refine ⟨82853869127836896424603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441887302015130114264549 82853869127836896424603)
                  ·
                    rfl

theorem cell20_181527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_181527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181527 prefixEnd_181527 := by exact prefixLift 181527
  have htrace : WordTrace (prefixWord ++ tailWord_181527) baseStart_181527 baseEnd_181527 := by
    simpa [prefixWord, tailWord_181527, baseEnd_181527] using wordTrace_append hprefix tailTrace_181527
  have hstable : (prefixWord ++ tailWord_181527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181527).length < 2 ^ (prefixWord ++ tailWord_181527).sum := by decide
  have hdescent : baseEnd_181527 < baseStart_181527 := by decide
  rcases family_descends (prefixWord ++ tailWord_181527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181574 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_181574 : Nat := 118140960795 + 181574 * 2 ^ 59
def prefixEnd_181574 : Nat := 4983230072969 + 3 ^ 40 * 181574 * 2
def baseEnd_181574 : Nat := 82875321208513621857745

theorem tailTrace_181574 : CollatzResearch.WordTrace tailWord_181574 prefixEnd_181574 82875321208513621857745 := by
  unfold tailWord_181574
  simp only [CollatzResearch.WordTrace]
  refine ⟨206954620131121350482743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4415031896130588810298517 206954620131121350482743)
  ·
    refine ⟨310431930196682025724115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206954620131121350482743 310431930196682025724115)
    ·
      refine ⟨465647895295023038586173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310431930196682025724115 465647895295023038586173)
      ·
        refine ⟨174617960735633639469815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465647895295023038586173 174617960735633639469815)
        ·
          refine ⟨261926941103450459204723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174617960735633639469815 261926941103450459204723)
          ·
            refine ⟨392890411655175688807085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261926941103450459204723 392890411655175688807085)
            ·
              refine ⟨147333904370690883302657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392890411655175688807085 147333904370690883302657)
              ·
                refine ⟨110500428278018162476993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147333904370690883302657 110500428278018162476993)
                ·
                  refine ⟨82875321208513621857745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110500428278018162476993 82875321208513621857745)
                  ·
                    rfl

theorem cell20_181574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_181574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181574 prefixEnd_181574 := by exact prefixLift 181574
  have htrace : WordTrace (prefixWord ++ tailWord_181574) baseStart_181574 baseEnd_181574 := by
    simpa [prefixWord, tailWord_181574, baseEnd_181574] using wordTrace_append hprefix tailTrace_181574
  have hstable : (prefixWord ++ tailWord_181574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181574).length < 2 ^ (prefixWord ++ tailWord_181574).sum := by decide
  have hdescent : baseEnd_181574 < baseStart_181574 := by decide
  rcases family_descends (prefixWord ++ tailWord_181574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181593 : List Nat := [1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_181593 : Nat := 118140960795 + 181593 * 2 ^ 59
def prefixEnd_181593 : Nat := 4983230072969 + 3 ^ 40 * 181593 * 2
def baseEnd_181593 : Nat := 27627997775411333408111

theorem tailTrace_181593 : CollatzResearch.WordTrace tailWord_181593 prefixEnd_181593 27627997775411333408111 := by
  unfold tailWord_181593
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623240831127049460389433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4415493887418032973592955 6623240831127049460389433)
  ·
    refine ⟨4967430623345287095292075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6623240831127049460389433 4967430623345287095292075)
    ·
      refine ⟨7451145935017930642938113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4967430623345287095292075 7451145935017930642938113)
      ·
        refine ⟨5588359451263447982203585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7451145935017930642938113 5588359451263447982203585)
        ·
          refine ⟨4191269588447585986652689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5588359451263447982203585 4191269588447585986652689)
          ·
            refine ⟨3143452191335689489989517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191269588447585986652689 3143452191335689489989517)
            ·
              refine ⟨1178794571750883558746069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143452191335689489989517 1178794571750883558746069)
              ·
                refine ⟨27627997775411333408111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1178794571750883558746069 27627997775411333408111)
                ·
                  rfl

theorem cell20_181593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_181593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181593 prefixEnd_181593 := by exact prefixLift 181593
  have htrace : WordTrace (prefixWord ++ tailWord_181593) baseStart_181593 baseEnd_181593 := by
    simpa [prefixWord, tailWord_181593, baseEnd_181593] using wordTrace_append hprefix tailTrace_181593
  have hstable : (prefixWord ++ tailWord_181593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181593).length < 2 ^ (prefixWord ++ tailWord_181593).sum := by decide
  have hdescent : baseEnd_181593 < baseStart_181593 := by decide
  rcases family_descends (prefixWord ++ tailWord_181593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181633 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 2]
def baseStart_181633 : Nat := 118140960795 + 181633 * 2 ^ 59
def prefixEnd_181633 : Nat := 4983230072969 + 3 ^ 40 * 181633 * 2
def baseEnd_181633 : Nat := 82902250416171638890837

theorem tailTrace_181633 : CollatzResearch.WordTrace tailWord_181633 prefixEnd_181633 82902250416171638890837 := by
  unfold tailWord_181633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624699750982136291845553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4416466500654757527897035 6624699750982136291845553)
  ·
    refine ⟨4968524813236602218884165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6624699750982136291845553 4968524813236602218884165)
    ·
      refine ⟨931598402481862916040781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4968524813236602218884165 931598402481862916040781)
      ·
        refine ⟨349349400930698593515293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 931598402481862916040781 349349400930698593515293)
        ·
          refine ⟨131006025349011972568235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349349400930698593515293 131006025349011972568235)
          ·
            refine ⟨196509038023517958852353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131006025349011972568235 196509038023517958852353)
            ·
              refine ⟨147381778517638469139265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196509038023517958852353 147381778517638469139265)
              ·
                refine ⟨110536333888228851854449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147381778517638469139265 110536333888228851854449)
                ·
                  refine ⟨82902250416171638890837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110536333888228851854449 82902250416171638890837)
                  ·
                    rfl

theorem cell20_181633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_181633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181633 prefixEnd_181633 := by exact prefixLift 181633
  have htrace : WordTrace (prefixWord ++ tailWord_181633) baseStart_181633 baseEnd_181633 := by
    simpa [prefixWord, tailWord_181633, baseEnd_181633] using wordTrace_append hprefix tailTrace_181633
  have hstable : (prefixWord ++ tailWord_181633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181633).length < 2 ^ (prefixWord ++ tailWord_181633).sum := by decide
  have hdescent : baseEnd_181633 < baseStart_181633 := by decide
  rcases family_descends (prefixWord ++ tailWord_181633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181689 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_181689 : Nat := 118140960795 + 181689 * 2 ^ 59
def prefixEnd_181689 : Nat := 4983230072969 + 3 ^ 40 * 181689 * 2
def baseEnd_181689 : Nat := 82927810342084333023941

theorem tailTrace_181689 : CollatzResearch.WordTrace tailWord_181689 prefixEnd_181689 82927810342084333023941 := by
  unfold tailWord_181689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626742238779257855884121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4417828159186171903922747 6626742238779257855884121)
  ·
    refine ⟨4970056679084443391913091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6626742238779257855884121 4970056679084443391913091)
    ·
      refine ⟨7455085018626665087869637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4970056679084443391913091 7455085018626665087869637)
      ·
        refine ⟨1397828440992499703975557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7455085018626665087869637 1397828440992499703975557)
        ·
          refine ⟨262092832686093694495417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1397828440992499703975557 262092832686093694495417)
          ·
            refine ⟨196569624514570270871563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262092832686093694495417 196569624514570270871563)
            ·
              refine ⟨294854436771855406307345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196569624514570270871563 294854436771855406307345)
              ·
                refine ⟨221140827578891554730509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294854436771855406307345 221140827578891554730509)
                ·
                  refine ⟨82927810342084333023941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221140827578891554730509 82927810342084333023941)
                  ·
                    rfl

theorem cell20_181689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_181689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181689 prefixEnd_181689 := by exact prefixLift 181689
  have htrace : WordTrace (prefixWord ++ tailWord_181689) baseStart_181689 baseEnd_181689 := by
    simpa [prefixWord, tailWord_181689, baseEnd_181689] using wordTrace_append hprefix tailTrace_181689
  have hstable : (prefixWord ++ tailWord_181689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181689).length < 2 ^ (prefixWord ++ tailWord_181689).sum := by decide
  have hdescent : baseEnd_181689 < baseStart_181689 := by decide
  rcases family_descends (prefixWord ++ tailWord_181689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181693 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_181693 : Nat := 118140960795 + 181693 * 2 ^ 59
def prefixEnd_181693 : Nat := 4983230072969 + 3 ^ 40 * 181693 * 2
def baseEnd_181693 : Nat := 82929636051078096890591

theorem tailTrace_181693 : CollatzResearch.WordTrace tailWord_181693 prefixEnd_181693 82929636051078096890591 := by
  unfold tailWord_181693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626888130764766539029733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4417925420509844359353155 6626888130764766539029733)
  ·
    refine ⟨1242541524518393726068075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6626888130764766539029733 1242541524518393726068075)
    ·
      refine ⟨1863812286777590589102113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242541524518393726068075 1863812286777590589102113)
      ·
        refine ⟨1397859215083192941826585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863812286777590589102113 1397859215083192941826585)
        ·
          refine ⟨1048394411312394706369939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397859215083192941826585 1048394411312394706369939)
          ·
            refine ⟨1572591616968592059554909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048394411312394706369939 1572591616968592059554909)
            ·
              refine ⟨589721856363222022333091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572591616968592059554909 589721856363222022333091)
              ·
                refine ⟨884582784544833033499637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589721856363222022333091 884582784544833033499637)
                ·
                  refine ⟨82929636051078096890591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884582784544833033499637 82929636051078096890591)
                  ·
                    rfl

theorem cell20_181693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_181693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181693 prefixEnd_181693 := by exact prefixLift 181693
  have htrace : WordTrace (prefixWord ++ tailWord_181693) baseStart_181693 baseEnd_181693 := by
    simpa [prefixWord, tailWord_181693, baseEnd_181693] using wordTrace_append hprefix tailTrace_181693
  have hstable : (prefixWord ++ tailWord_181693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181693).length < 2 ^ (prefixWord ++ tailWord_181693).sum := by decide
  have hdescent : baseEnd_181693 < baseStart_181693 := by decide
  rcases family_descends (prefixWord ++ tailWord_181693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181731 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_181731 : Nat := 118140960795 + 181731 * 2 ^ 59
def prefixEnd_181731 : Nat := 4983230072969 + 3 ^ 40 * 181731 * 2
def baseEnd_181731 : Nat := 82946980286518853623769

theorem tailTrace_181731 : CollatzResearch.WordTrace tailWord_181731 prefixEnd_181731 82946980286518853623769 := by
  unfold tailWord_181731
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628274104627099028913047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4418849403084732685942031 6628274104627099028913047)
  ·
    refine ⟨9942411156940648543369571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6628274104627099028913047 9942411156940648543369571)
    ·
      refine ⟨14913616735410972815054357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9942411156940648543369571 14913616735410972815054357)
      ·
        refine ⟨699075784472389350705673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14913616735410972815054357 699075784472389350705673)
        ·
          refine ⟨524306838354292013029255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699075784472389350705673 524306838354292013029255)
          ·
            refine ⟨786460257531438019543883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524306838354292013029255 786460257531438019543883)
            ·
              refine ⟨1179690386297157029315825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786460257531438019543883 1179690386297157029315825)
              ·
                refine ⟨884767789722867771986869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179690386297157029315825 884767789722867771986869)
                ·
                  refine ⟨82946980286518853623769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884767789722867771986869 82946980286518853623769)
                  ·
                    rfl

theorem cell20_181731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_181731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181731 prefixEnd_181731 := by exact prefixLift 181731
  have htrace : WordTrace (prefixWord ++ tailWord_181731) baseStart_181731 baseEnd_181731 := by
    simpa [prefixWord, tailWord_181731, baseEnd_181731] using wordTrace_append hprefix tailTrace_181731
  have hstable : (prefixWord ++ tailWord_181731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181731).length < 2 ^ (prefixWord ++ tailWord_181731).sum := by decide
  have hdescent : baseEnd_181731 < baseStart_181731 := by decide
  rcases family_descends (prefixWord ++ tailWord_181731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181741 : List Nat := [1, 5, 1, 3, 2, 2, 6]
def baseStart_181741 : Nat := 118140960795 + 181741 * 2 ^ 59
def prefixEnd_181741 : Nat := 4983230072969 + 3 ^ 40 * 181741 * 2
def baseEnd_181741 : Nat := 9216838284333695921155

theorem tailTrace_181741 : CollatzResearch.WordTrace tailWord_181741 prefixEnd_181741 9216838284333695921155 := by
  unfold tailWord_181741
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628638834590870736777077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4419092556393913824518051 6628638834590870736777077)
  ·
    refine ⟨621434890742894131572851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6628638834590870736777077 621434890742894131572851)
    ·
      refine ⟨932152336114341197359277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621434890742894131572851 932152336114341197359277)
      ·
        refine ⟨349557126042877949009729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 932152336114341197359277 349557126042877949009729)
        ·
          refine ⟨262167844532158461757297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349557126042877949009729 262167844532158461757297)
          ·
            refine ⟨196625883399118846317973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262167844532158461757297 196625883399118846317973)
            ·
              refine ⟨9216838284333695921155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196625883399118846317973 9216838284333695921155)
              ·
                rfl

theorem cell20_181741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_181741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181741 prefixEnd_181741 := by exact prefixLift 181741
  have htrace : WordTrace (prefixWord ++ tailWord_181741) baseStart_181741 baseEnd_181741 := by
    simpa [prefixWord, tailWord_181741, baseEnd_181741] using wordTrace_append hprefix tailTrace_181741
  have hstable : (prefixWord ++ tailWord_181741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181741).length < 2 ^ (prefixWord ++ tailWord_181741).sum := by decide
  have hdescent : baseEnd_181741 < baseStart_181741 := by decide
  rcases family_descends (prefixWord ++ tailWord_181741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181745 : List Nat := [1, 2, 2, 2, 3, 2, 8]
def baseStart_181745 : Nat := 118140960795 + 181745 * 2 ^ 59
def prefixEnd_181745 : Nat := 4983230072969 + 3 ^ 40 * 181745 * 2
def baseEnd_181745 : Nat := 9217041140888558573005

theorem tailTrace_181745 : CollatzResearch.WordTrace tailWord_181745 prefixEnd_181745 9217041140888558573005 := by
  unfold tailWord_181745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628784726576379419922689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4419189817717586279948459 6628784726576379419922689)
  ·
    refine ⟨4971588544932284564942017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6628784726576379419922689 4971588544932284564942017)
    ·
      refine ⟨3728691408699213423706513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4971588544932284564942017 3728691408699213423706513)
      ·
        refine ⟨2796518556524410067779885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3728691408699213423706513 2796518556524410067779885)
        ·
          refine ⟨1048694458696653775417457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2796518556524410067779885 1048694458696653775417457)
          ·
            refine ⟨786520844022490331563093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048694458696653775417457 786520844022490331563093)
            ·
              refine ⟨9217041140888558573005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 786520844022490331563093 9217041140888558573005)
              ·
                rfl

theorem cell20_181745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_181745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181745 prefixEnd_181745 := by exact prefixLift 181745
  have htrace : WordTrace (prefixWord ++ tailWord_181745) baseStart_181745 baseEnd_181745 := by
    simpa [prefixWord, tailWord_181745, baseEnd_181745] using wordTrace_append hprefix tailTrace_181745
  have hstable : (prefixWord ++ tailWord_181745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181745).length < 2 ^ (prefixWord ++ tailWord_181745).sum := by decide
  have hdescent : baseEnd_181745 < baseStart_181745 := by decide
  rcases family_descends (prefixWord ++ tailWord_181745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181758 : List Nat := [4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_181758 : Nat := 118140960795 + 181758 * 2 ^ 59
def prefixEnd_181758 : Nat := 4983230072969 + 3 ^ 40 * 181758 * 2
def baseEnd_181758 : Nat := 27653101274075586574553

theorem tailTrace_181758 : CollatzResearch.WordTrace tailWord_181758 prefixEnd_181758 27653101274075586574553 := by
  unfold tailWord_181758
  simp only [CollatzResearch.WordTrace]
  refine ⟨828657359441160330018241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4419505917019521760097285 828657359441160330018241)
  ·
    refine ⟨621493019580870247513681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 828657359441160330018241 621493019580870247513681)
    ·
      refine ⟨466119764685652685635261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621493019580870247513681 466119764685652685635261)
      ·
        refine ⟨174794911757119757113223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466119764685652685635261 174794911757119757113223)
        ·
          refine ⟨262192367635679635669835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174794911757119757113223 262192367635679635669835)
          ·
            refine ⟨393288551453519453504753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262192367635679635669835 393288551453519453504753)
            ·
              refine ⟨294966413590139590128565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393288551453519453504753 294966413590139590128565)
              ·
                refine ⟨27653101274075586574553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294966413590139590128565 27653101274075586574553)
                ·
                  rfl

theorem cell20_181758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_181758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181758 prefixEnd_181758 := by exact prefixLift 181758
  have htrace : WordTrace (prefixWord ++ tailWord_181758) baseStart_181758 baseEnd_181758 := by
    simpa [prefixWord, tailWord_181758, baseEnd_181758] using wordTrace_append hprefix tailTrace_181758
  have hstable : (prefixWord ++ tailWord_181758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181758).length < 2 ^ (prefixWord ++ tailWord_181758).sum := by decide
  have hdescent : baseEnd_181758 < baseStart_181758 := by decide
  rcases family_descends (prefixWord ++ tailWord_181758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181769 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_181769 : Nat := 118140960795 + 181769 * 2 ^ 59
def prefixEnd_181769 : Nat := 4983230072969 + 3 ^ 40 * 181769 * 2
def baseEnd_181769 : Nat := 82964324521959610356947

theorem tailTrace_181769 : CollatzResearch.WordTrace tailWord_181769 prefixEnd_181769 82964324521959610356947 := by
  unfold tailWord_181769
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629660078489431518796361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4419773385659621012530907 6629660078489431518796361)
  ·
    refine ⟨4972245058867073639097271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6629660078489431518796361 4972245058867073639097271)
    ·
      refine ⟨7458367588300610458645907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972245058867073639097271 7458367588300610458645907)
      ·
        refine ⟨11187551382450915687968861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7458367588300610458645907 11187551382450915687968861)
        ·
          refine ⟨4195331768419093382988323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11187551382450915687968861 4195331768419093382988323)
          ·
            refine ⟨6292997652628640074482485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195331768419093382988323 6292997652628640074482485)
            ·
              refine ⟨589968529933935006982733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6292997652628640074482485 589968529933935006982733)
              ·
                refine ⟨221238198725225627618525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589968529933935006982733 221238198725225627618525)
                ·
                  refine ⟨82964324521959610356947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221238198725225627618525 82964324521959610356947)
                  ·
                    rfl

theorem cell20_181769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_181769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181769 prefixEnd_181769 := by exact prefixLift 181769
  have htrace : WordTrace (prefixWord ++ tailWord_181769) baseStart_181769 baseEnd_181769 := by
    simpa [prefixWord, tailWord_181769, baseEnd_181769] using wordTrace_append hprefix tailTrace_181769
  have hstable : (prefixWord ++ tailWord_181769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181769).length < 2 ^ (prefixWord ++ tailWord_181769).sum := by decide
  have hdescent : baseEnd_181769 < baseStart_181769 := by decide
  rcases family_descends (prefixWord ++ tailWord_181769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181800 : List Nat := [2, 1, 5, 2, 2, 8]
def baseStart_181800 : Nat := 118140960795 + 181800 * 2 ^ 59
def prefixEnd_181800 : Nat := 4983230072969 + 3 ^ 40 * 181800 * 2
def baseEnd_181800 : Nat := 3073276806172640011981

theorem tailTrace_181800 : CollatzResearch.WordTrace tailWord_181800 prefixEnd_181800 3073276806172640011981 := by
  unfold tailWord_181800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315395370688561906587427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4420527160918082542116569 3315395370688561906587427)
  ·
    refine ⟨4973093056032842859881141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315395370688561906587427 4973093056032842859881141)
    ·
      refine ⟨466227474003079018113857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4973093056032842859881141 466227474003079018113857)
      ·
        refine ⟨349670605502309263585393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466227474003079018113857 349670605502309263585393)
        ·
          refine ⟨262252954126731947689045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349670605502309263585393 262252954126731947689045)
          ·
            refine ⟨3073276806172640011981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 262252954126731947689045 3073276806172640011981)
            ·
              rfl

theorem cell20_181800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 8].length) (baseStart_181800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181800 prefixEnd_181800 := by exact prefixLift 181800
  have htrace : WordTrace (prefixWord ++ tailWord_181800) baseStart_181800 baseEnd_181800 := by
    simpa [prefixWord, tailWord_181800, baseEnd_181800] using wordTrace_append hprefix tailTrace_181800
  have hstable : (prefixWord ++ tailWord_181800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181800).length < 2 ^ (prefixWord ++ tailWord_181800).sum := by decide
  have hdescent : baseEnd_181800 < baseStart_181800 := by decide
  rcases family_descends (prefixWord ++ tailWord_181800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181806 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_181806 : Nat := 118140960795 + 181806 * 2 ^ 59
def prefixEnd_181806 : Nat := 4983230072969 + 3 ^ 40 * 181806 * 2
def baseEnd_181806 : Nat := 82981212330151926123463

theorem tailTrace_181806 : CollatzResearch.WordTrace tailWord_181806 prefixEnd_181806 82981212330151926123463 := by
  unfold tailWord_181806
  simp only [CollatzResearch.WordTrace]
  refine ⟨828876197419423354736659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4420673052903591225262181 828876197419423354736659)
  ·
    refine ⟨1243314296129135032104989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828876197419423354736659 1243314296129135032104989)
    ·
      refine ⟨466242861048425637039371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1243314296129135032104989 466242861048425637039371)
      ·
        refine ⟨699364291572638455559057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466242861048425637039371 699364291572638455559057)
        ·
          refine ⟨524523218679478841669293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699364291572638455559057 524523218679478841669293)
          ·
            refine ⟨196696207004804565625985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524523218679478841669293 196696207004804565625985)
            ·
              refine ⟨147522155253603424219489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196696207004804565625985 147522155253603424219489)
              ·
                refine ⟨110641616440202568164617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147522155253603424219489 110641616440202568164617)
                ·
                  refine ⟨82981212330151926123463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110641616440202568164617 82981212330151926123463)
                  ·
                    rfl

theorem cell20_181806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_181806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181806 prefixEnd_181806 := by exact prefixLift 181806
  have htrace : WordTrace (prefixWord ++ tailWord_181806) baseStart_181806 baseEnd_181806 := by
    simpa [prefixWord, tailWord_181806, baseEnd_181806] using wordTrace_append hprefix tailTrace_181806
  have hstable : (prefixWord ++ tailWord_181806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181806).length < 2 ^ (prefixWord ++ tailWord_181806).sum := by decide
  have hdescent : baseEnd_181806 < baseStart_181806 := by decide
  rcases family_descends (prefixWord ++ tailWord_181806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181831 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_181831 : Nat := 118140960795 + 181831 * 2 ^ 59
def prefixEnd_181831 : Nat := 4983230072969 + 3 ^ 40 * 181831 * 2
def baseEnd_181831 : Nat := 82992623011362950290027

theorem tailTrace_181831 : CollatzResearch.WordTrace tailWord_181831 prefixEnd_181831 82992623011362950290027 := by
  unfold tailWord_181831
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631921404264816107553347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4421280936176544071702231 6631921404264816107553347)
  ·
    refine ⟨9947882106397224161330021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631921404264816107553347 9947882106397224161330021)
    ·
      refine ⟨1865227894949479530249379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9947882106397224161330021 1865227894949479530249379)
      ·
        refine ⟨2797841842424219295374069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865227894949479530249379 2797841842424219295374069)
        ·
          refine ⟨262297672727270558941319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2797841842424219295374069 262297672727270558941319)
          ·
            refine ⟨393446509090905838411979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262297672727270558941319 393446509090905838411979)
            ·
              refine ⟨590169763636358757617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393446509090905838411979 590169763636358757617969)
              ·
                refine ⟨442627322727269068213477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590169763636358757617969 442627322727269068213477)
                ·
                  refine ⟨82992623011362950290027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442627322727269068213477 82992623011362950290027)
                  ·
                    rfl

theorem cell20_181831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_181831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181831 prefixEnd_181831 := by exact prefixLift 181831
  have htrace : WordTrace (prefixWord ++ tailWord_181831) baseStart_181831 baseEnd_181831 := by
    simpa [prefixWord, tailWord_181831, baseEnd_181831] using wordTrace_append hprefix tailTrace_181831
  have hstable : (prefixWord ++ tailWord_181831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181831).length < 2 ^ (prefixWord ++ tailWord_181831).sum := by decide
  have hdescent : baseEnd_181831 < baseStart_181831 := by decide
  rcases family_descends (prefixWord ++ tailWord_181831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181859 : List Nat := [1, 1, 1, 5, 1, 4, 7]
def baseStart_181859 : Nat := 118140960795 + 181859 * 2 ^ 59
def prefixEnd_181859 : Nat := 4983230072969 + 3 ^ 40 * 181859 * 2
def baseEnd_181859 : Nat := 9222822552702144150731

theorem tailTrace_181859 : CollatzResearch.WordTrace tailWord_181859 prefixEnd_181859 9222822552702144150731 := by
  unfold tailWord_181859
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632942648163376889572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4421961765442251259715087 6632942648163376889572631)
  ·
    refine ⟨9949413972245065334358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6632942648163376889572631 9949413972245065334358947)
    ·
      refine ⟨14924120958367598001538421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9949413972245065334358947 14924120958367598001538421)
      ·
        refine ⟨1399136339846962312644227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14924120958367598001538421 1399136339846962312644227)
        ·
          refine ⟨2098704509770443468966341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399136339846962312644227 2098704509770443468966341)
          ·
            refine ⟨393507095581958150431189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2098704509770443468966341 393507095581958150431189)
            ·
              refine ⟨9222822552702144150731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 393507095581958150431189 9222822552702144150731)
              ·
                rfl

theorem cell20_181859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_181859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181859 prefixEnd_181859 := by exact prefixLift 181859
  have htrace : WordTrace (prefixWord ++ tailWord_181859) baseStart_181859 baseEnd_181859 := by
    simpa [prefixWord, tailWord_181859, baseEnd_181859] using wordTrace_append hprefix tailTrace_181859
  have hstable : (prefixWord ++ tailWord_181859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181859).length < 2 ^ (prefixWord ++ tailWord_181859).sum := by decide
  have hdescent : baseEnd_181859 < baseStart_181859 := by decide
  rcases family_descends (prefixWord ++ tailWord_181859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181921 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_181921 : Nat := 118140960795 + 181921 * 2 ^ 59
def prefixEnd_181921 : Nat := 4983230072969 + 3 ^ 40 * 181921 * 2
def baseEnd_181921 : Nat := 83033701463722637289659

theorem tailTrace_181921 : CollatzResearch.WordTrace tailWord_181921 prefixEnd_181921 83033701463722637289659 := by
  unfold tailWord_181921
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635203973938761478329617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423469315959174318886411 6635203973938761478329617)
  ·
    refine ⟨4976402980454071108747213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6635203973938761478329617 4976402980454071108747213)
    ·
      refine ⟨1866151117670276665780205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4976402980454071108747213 1866151117670276665780205)
      ·
        refine ⟨699806669126353749667577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1866151117670276665780205 699806669126353749667577)
        ·
          refine ⟨524855001844765312250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699806669126353749667577 524855001844765312250683)
          ·
            refine ⟨787282502767147968376025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524855001844765312250683 787282502767147968376025)
            ·
              refine ⟨590461877075360976282019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787282502767147968376025 590461877075360976282019)
              ·
                refine ⟨885692815613041464423029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590461877075360976282019 885692815613041464423029)
                ·
                  refine ⟨83033701463722637289659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 885692815613041464423029 83033701463722637289659)
                  ·
                    rfl

theorem cell20_181921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_181921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181921 prefixEnd_181921 := by exact prefixLift 181921
  have htrace : WordTrace (prefixWord ++ tailWord_181921) baseStart_181921 baseEnd_181921 := by
    simpa [prefixWord, tailWord_181921, baseEnd_181921] using wordTrace_append hprefix tailTrace_181921
  have hstable : (prefixWord ++ tailWord_181921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181921).length < 2 ^ (prefixWord ++ tailWord_181921).sum := by decide
  have hdescent : baseEnd_181921 < baseStart_181921 := by decide
  rcases family_descends (prefixWord ++ tailWord_181921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181935 : List Nat := [1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_181935 : Nat := 118140960795 + 181935 * 2 ^ 59
def prefixEnd_181935 : Nat := 4983230072969 + 3 ^ 40 * 181935 * 2
def baseEnd_181935 : Nat := 27680030481733603607645

theorem tailTrace_181935 : CollatzResearch.WordTrace tailWord_181935 prefixEnd_181935 27680030481733603607645 := by
  unfold tailWord_181935
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635714595888041869339259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423809730592027912892839 6635714595888041869339259)
  ·
    refine ⟨9953571893832062804008889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6635714595888041869339259 9953571893832062804008889)
    ·
      refine ⟨7465178920374047103006667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9953571893832062804008889 7465178920374047103006667)
      ·
        refine ⟨11197768380561070654510001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465178920374047103006667 11197768380561070654510001)
        ·
          refine ⟨8398326285420802990882501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11197768380561070654510001 8398326285420802990882501)
          ·
            refine ⟨1574686178516400560790469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8398326285420802990882501 1574686178516400560790469)
            ·
              refine ⟨295253658471825105148213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1574686178516400560790469 295253658471825105148213)
              ·
                refine ⟨27680030481733603607645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295253658471825105148213 27680030481733603607645)
                ·
                  rfl

theorem cell20_181935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_181935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181935 prefixEnd_181935 := by exact prefixLift 181935
  have htrace : WordTrace (prefixWord ++ tailWord_181935) baseStart_181935 baseEnd_181935 := by
    simpa [prefixWord, tailWord_181935, baseEnd_181935] using wordTrace_append hprefix tailTrace_181935
  have hstable : (prefixWord ++ tailWord_181935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181935).length < 2 ^ (prefixWord ++ tailWord_181935).sum := by decide
  have hdescent : baseEnd_181935 < baseStart_181935 := by decide
  rcases family_descends (prefixWord ++ tailWord_181935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181938 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_181938 : Nat := 118140960795 + 181938 * 2 ^ 59
def prefixEnd_181938 : Nat := 4983230072969 + 3 ^ 40 * 181938 * 2
def baseEnd_181938 : Nat := 83041460726946133722923

theorem tailTrace_181938 : CollatzResearch.WordTrace tailWord_181938 prefixEnd_181938 83041460726946133722923 := by
  unfold tailWord_181938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658956003719293345424617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4423882676584782254465645 1658956003719293345424617)
  ·
    refine ⟨1244217002789470009068463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1658956003719293345424617 1244217002789470009068463)
    ·
      refine ⟨1866325504184205013602695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244217002789470009068463 1866325504184205013602695)
      ·
        refine ⟨2799488256276307520404043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866325504184205013602695 2799488256276307520404043)
        ·
          refine ⟨4199232384414461280606065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799488256276307520404043 4199232384414461280606065)
          ·
            refine ⟨3149424288310845960454549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4199232384414461280606065 3149424288310845960454549)
            ·
              refine ⟨147629263514570904396307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3149424288310845960454549 147629263514570904396307)
              ·
                refine ⟨221443895271856356594461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147629263514570904396307 221443895271856356594461)
                ·
                  refine ⟨83041460726946133722923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221443895271856356594461 83041460726946133722923)
                  ·
                    rfl

theorem cell20_181938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_181938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181938 prefixEnd_181938 := by exact prefixLift 181938
  have htrace : WordTrace (prefixWord ++ tailWord_181938) baseStart_181938 baseEnd_181938 := by
    simpa [prefixWord, tailWord_181938, baseEnd_181938] using wordTrace_append hprefix tailTrace_181938
  have hstable : (prefixWord ++ tailWord_181938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181938).length < 2 ^ (prefixWord ++ tailWord_181938).sum := by decide
  have hdescent : baseEnd_181938 < baseStart_181938 := by decide
  rcases family_descends (prefixWord ++ tailWord_181938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181983 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 2]
def baseStart_181983 : Nat := 118140960795 + 181983 * 2 ^ 59
def prefixEnd_181983 : Nat := 4983230072969 + 3 ^ 40 * 181983 * 2
def baseEnd_181983 : Nat := 83061999953125977222739

theorem tailTrace_181983 : CollatzResearch.WordTrace tailWord_181983 prefixEnd_181983 83061999953125977222739 := by
  unfold tailWord_181983
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637465299714146067086603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4424976866476097378057735 6637465299714146067086603)
  ·
    refine ⟨9956197949571219100629905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6637465299714146067086603 9956197949571219100629905)
    ·
      refine ⟨7467148462178414325472429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9956197949571219100629905 7467148462178414325472429)
      ·
        refine ⟨2800180673316905372052161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7467148462178414325472429 2800180673316905372052161)
        ·
          refine ⟨2100135504987679029039121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800180673316905372052161 2100135504987679029039121)
          ·
            refine ⟨1575101628740759271779341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100135504987679029039121 1575101628740759271779341)
            ·
              refine ⟨590663110777784726917253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1575101628740759271779341 590663110777784726917253)
              ·
                refine ⟨110749333270834636296985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590663110777784726917253 110749333270834636296985)
                ·
                  refine ⟨83061999953125977222739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110749333270834636296985 83061999953125977222739)
                  ·
                    rfl

theorem cell20_181983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2].length) (baseStart_181983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_181983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_181983 prefixEnd_181983 := by exact prefixLift 181983
  have htrace : WordTrace (prefixWord ++ tailWord_181983) baseStart_181983 baseEnd_181983 := by
    simpa [prefixWord, tailWord_181983, baseEnd_181983] using wordTrace_append hprefix tailTrace_181983
  have hstable : (prefixWord ++ tailWord_181983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181983).length < 2 ^ (prefixWord ++ tailWord_181983).sum := by decide
  have hdescent : baseEnd_181983 < baseStart_181983 := by decide
  rcases family_descends (prefixWord ++ tailWord_181983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182025 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_182025 : Nat := 118140960795 + 182025 * 2 ^ 59
def prefixEnd_182025 : Nat := 4983230072969 + 3 ^ 40 * 182025 * 2
def baseEnd_182025 : Nat := 83081169897560497822567

theorem tailTrace_182025 : CollatzResearch.WordTrace tailWord_182025 prefixEnd_182025 83081169897560497822567 := by
  unfold tailWord_182025
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638997165561987240115529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4425998110374658160077019 6638997165561987240115529)
  ·
    refine ⟨4979247874171490430086647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6638997165561987240115529 4979247874171490430086647)
    ·
      refine ⟨7468871811257235645129971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979247874171490430086647 7468871811257235645129971)
      ·
        refine ⟨11203307716885853467694957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468871811257235645129971 11203307716885853467694957)
        ·
          refine ⟨4201240393832195050385609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11203307716885853467694957 4201240393832195050385609)
          ·
            refine ⟨3150930295374146287789207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4201240393832195050385609 3150930295374146287789207)
            ·
              refine ⟨4726395443061219431683811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150930295374146287789207 4726395443061219431683811)
              ·
                refine ⟨7089593164591829147525717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726395443061219431683811 7089593164591829147525717)
                ·
                  refine ⟨83081169897560497822567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7089593164591829147525717 83081169897560497822567)
                  ·
                    rfl

theorem cell20_182025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_182025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182025 prefixEnd_182025 := by exact prefixLift 182025
  have htrace : WordTrace (prefixWord ++ tailWord_182025) baseStart_182025 baseEnd_182025 := by
    simpa [prefixWord, tailWord_182025, baseEnd_182025] using wordTrace_append hprefix tailTrace_182025
  have hstable : (prefixWord ++ tailWord_182025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182025).length < 2 ^ (prefixWord ++ tailWord_182025).sum := by decide
  have hdescent : baseEnd_182025 < baseStart_182025 := by decide
  rcases family_descends (prefixWord ++ tailWord_182025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182042 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_182042 : Nat := 118140960795 + 182042 * 2 ^ 59
def prefixEnd_182042 : Nat := 4983230072969 + 3 ^ 40 * 182042 * 2
def baseEnd_182042 : Nat := 83088929160783994255831

theorem tailTrace_182042 : CollatzResearch.WordTrace tailWord_182042 prefixEnd_182042 83088929160783994255831 := by
  unfold tailWord_182042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659904301625099785871095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4426411471000266095656253 1659904301625099785871095)
  ·
    refine ⟨2489856452437649678806643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1659904301625099785871095 2489856452437649678806643)
    ·
      refine ⟨3734784678656474518209965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2489856452437649678806643 3734784678656474518209965)
      ·
        refine ⟨1400544254496177944328737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3734784678656474518209965 1400544254496177944328737)
        ·
          refine ⟨1050408190872133458246553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400544254496177944328737 1050408190872133458246553)
          ·
            refine ⟨787806143154100093684915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050408190872133458246553 787806143154100093684915)
            ·
              refine ⟨1181709214731150140527373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787806143154100093684915 1181709214731150140527373)
              ·
                refine ⟨443140955524181302697765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181709214731150140527373 443140955524181302697765)
                ·
                  refine ⟨83088929160783994255831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443140955524181302697765 83088929160783994255831)
                  ·
                    rfl

theorem cell20_182042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_182042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182042 prefixEnd_182042 := by exact prefixLift 182042
  have htrace : WordTrace (prefixWord ++ tailWord_182042) baseStart_182042 baseEnd_182042 := by
    simpa [prefixWord, tailWord_182042, baseEnd_182042] using wordTrace_append hprefix tailTrace_182042
  have hstable : (prefixWord ++ tailWord_182042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182042).length < 2 ^ (prefixWord ++ tailWord_182042).sum := by decide
  have hdescent : baseEnd_182042 < baseStart_182042 := by decide
  rcases family_descends (prefixWord ++ tailWord_182042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182062 : List Nat := [4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_182062 : Nat := 118140960795 + 182062 * 2 ^ 59
def prefixEnd_182062 : Nat := 4983230072969 + 3 ^ 40 * 182062 * 2
def baseEnd_182062 : Nat := 27699352568584271196361

theorem tailTrace_182062 : CollatzResearch.WordTrace tailWord_182062 prefixEnd_182062 27699352568584271196361 := by
  unfold tailWord_182062
  simp only [CollatzResearch.WordTrace]
  refine ⟨830043333303492819901555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4426897777618628372808293 830043333303492819901555)
  ·
    refine ⟨1245064999955239229852333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830043333303492819901555 1245064999955239229852333)
    ·
      refine ⟨466899374983214711194625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1245064999955239229852333 466899374983214711194625)
      ·
        refine ⟨350174531237411033395969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466899374983214711194625 350174531237411033395969)
        ·
          refine ⟨262630898428058275046977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350174531237411033395969 262630898428058275046977)
          ·
            refine ⟨196973173821043706285233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262630898428058275046977 196973173821043706285233)
            ·
              refine ⟨147729880365782779713925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196973173821043706285233 147729880365782779713925)
              ·
                refine ⟨27699352568584271196361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147729880365782779713925 27699352568584271196361)
                ·
                  rfl

theorem cell20_182062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_182062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182062 prefixEnd_182062 := by exact prefixLift 182062
  have htrace : WordTrace (prefixWord ++ tailWord_182062) baseStart_182062 baseEnd_182062 := by
    simpa [prefixWord, tailWord_182062, baseEnd_182062] using wordTrace_append hprefix tailTrace_182062
  have hstable : (prefixWord ++ tailWord_182062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182062).length < 2 ^ (prefixWord ++ tailWord_182062).sum := by decide
  have hdescent : baseEnd_182062 < baseStart_182062 := by decide
  rcases family_descends (prefixWord ++ tailWord_182062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182066 : List Nat := [3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_182066 : Nat := 118140960795 + 182066 * 2 ^ 59
def prefixEnd_182066 : Nat := 4983230072969 + 3 ^ 40 * 182066 * 2
def baseEnd_182066 : Nat := 27699961138248859151911

theorem tailTrace_182066 : CollatzResearch.WordTrace tailWord_182066 prefixEnd_182066 27699961138248859151911 := by
  unfold tailWord_182066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660123139603362810589513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4426995038942300828238701 1660123139603362810589513)
  ·
    refine ⟨1245092354702522107942135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1660123139603362810589513 1245092354702522107942135)
    ·
      refine ⟨1867638532053783161913203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245092354702522107942135 1867638532053783161913203)
      ·
        refine ⟨2801457798080674742869805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867638532053783161913203 2801457798080674742869805)
        ·
          refine ⟨1050546674280253028576177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2801457798080674742869805 1050546674280253028576177)
          ·
            refine ⟨787910005710189771432133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050546674280253028576177 787910005710189771432133)
            ·
              refine ⟨147733126070660582143525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 787910005710189771432133 147733126070660582143525)
              ·
                refine ⟨27699961138248859151911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147733126070660582143525 27699961138248859151911)
                ·
                  rfl

theorem cell20_182066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_182066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182066 prefixEnd_182066 := by exact prefixLift 182066
  have htrace : WordTrace (prefixWord ++ tailWord_182066) baseStart_182066 baseEnd_182066 := by
    simpa [prefixWord, tailWord_182066, baseEnd_182066] using wordTrace_append hprefix tailTrace_182066
  have hstable : (prefixWord ++ tailWord_182066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182066).length < 2 ^ (prefixWord ++ tailWord_182066).sum := by decide
  have hdescent : baseEnd_182066 < baseStart_182066 := by decide
  rcases family_descends (prefixWord ++ tailWord_182066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182097 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_182097 : Nat := 118140960795 + 182097 * 2 ^ 59
def prefixEnd_182097 : Nat := 4983230072969 + 3 ^ 40 * 182097 * 2
def baseEnd_182097 : Nat := 83114032659448247422273

theorem tailTrace_182097 : CollatzResearch.WordTrace tailWord_182097 prefixEnd_182097 83114032659448247422273 := by
  unfold tailWord_182097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641623221301143536736545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4427748814200762357824363 6641623221301143536736545)
  ·
    refine ⟨4981217415975857652552409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6641623221301143536736545 4981217415975857652552409)
    ·
      refine ⟨3735913061981893239414307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4981217415975857652552409 3735913061981893239414307)
      ·
        refine ⟨5603869592972839859121461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735913061981893239414307 5603869592972839859121461)
        ·
          refine ⟨525362774341203736792637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5603869592972839859121461 525362774341203736792637)
          ·
            refine ⟨197011040377951401297239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525362774341203736792637 197011040377951401297239)
            ·
              refine ⟨295516560566927101945859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197011040377951401297239 295516560566927101945859)
              ·
                refine ⟨443274840850390652918789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295516560566927101945859 443274840850390652918789)
                ·
                  refine ⟨83114032659448247422273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443274840850390652918789 83114032659448247422273)
                  ·
                    rfl

theorem cell20_182097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_182097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182097 prefixEnd_182097 := by exact prefixLift 182097
  have htrace : WordTrace (prefixWord ++ tailWord_182097) baseStart_182097 baseEnd_182097 := by
    simpa [prefixWord, tailWord_182097, baseEnd_182097] using wordTrace_append hprefix tailTrace_182097
  have hstable : (prefixWord ++ tailWord_182097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182097).length < 2 ^ (prefixWord ++ tailWord_182097).sum := by decide
  have hdescent : baseEnd_182097 < baseStart_182097 := by decide
  rcases family_descends (prefixWord ++ tailWord_182097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182111 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_182111 : Nat := 118140960795 + 182111 * 2 ^ 59
def prefixEnd_182111 : Nat := 4983230072969 + 3 ^ 40 * 182111 * 2
def baseEnd_182111 : Nat := 83120422640926420955549

theorem tailTrace_182111 : CollatzResearch.WordTrace tailWord_182111 prefixEnd_182111 83120422640926420955549 := by
  unfold tailWord_182111
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642133843250423927746187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4428089228833615951830791 6642133843250423927746187)
  ·
    refine ⟨9963200764875635891619281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6642133843250423927746187 9963200764875635891619281)
    ·
      refine ⟨7472400573656726918714461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9963200764875635891619281 7472400573656726918714461)
      ·
        refine ⟨2802150215121272594517923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7472400573656726918714461 2802150215121272594517923)
        ·
          refine ⟨4203225322681908891776885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802150215121272594517923 4203225322681908891776885)
          ·
            refine ⟨394052374001428958604083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4203225322681908891776885 394052374001428958604083)
            ·
              refine ⟨591078561002143437906125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394052374001428958604083 591078561002143437906125)
              ·
                refine ⟨221654460375803789214797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591078561002143437906125 221654460375803789214797)
                ·
                  refine ⟨83120422640926420955549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221654460375803789214797 83120422640926420955549)
                  ·
                    rfl

theorem cell20_182111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_182111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182111 prefixEnd_182111 := by exact prefixLift 182111
  have htrace : WordTrace (prefixWord ++ tailWord_182111) baseStart_182111 baseEnd_182111 := by
    simpa [prefixWord, tailWord_182111, baseEnd_182111] using wordTrace_append hprefix tailTrace_182111
  have hstable : (prefixWord ++ tailWord_182111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182111).length < 2 ^ (prefixWord ++ tailWord_182111).sum := by decide
  have hdescent : baseEnd_182111 < baseStart_182111 := by decide
  rcases family_descends (prefixWord ++ tailWord_182111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182125 : List Nat := [1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_182125 : Nat := 118140960795 + 182125 * 2 ^ 59
def prefixEnd_182125 : Nat := 4983230072969 + 3 ^ 40 * 182125 * 2
def baseEnd_182125 : Nat := 27708937540801531496275

theorem tailTrace_182125 : CollatzResearch.WordTrace tailWord_182125 prefixEnd_182125 27708937540801531496275 := by
  unfold tailWord_182125
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642644465199704318755829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4428429643466469545837219 6642644465199704318755829)
  ·
    refine ⟨622747918612472279883359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6642644465199704318755829 622747918612472279883359)
    ·
      refine ⟨934121877918708419825039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622747918612472279883359 934121877918708419825039)
      ·
        refine ⟨1401182816878062629737559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934121877918708419825039 1401182816878062629737559)
        ·
          refine ⟨2101774225317093944606339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401182816878062629737559 2101774225317093944606339)
          ·
            refine ⟨3152661337975640916909509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101774225317093944606339 3152661337975640916909509)
            ·
              refine ⟨591124000870432671920533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3152661337975640916909509 591124000870432671920533)
              ·
                refine ⟨27708937540801531496275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591124000870432671920533 27708937540801531496275)
                ·
                  rfl

theorem cell20_182125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_182125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182125 prefixEnd_182125 := by exact prefixLift 182125
  have htrace : WordTrace (prefixWord ++ tailWord_182125) baseStart_182125 baseEnd_182125 := by
    simpa [prefixWord, tailWord_182125, baseEnd_182125] using wordTrace_append hprefix tailTrace_182125
  have hstable : (prefixWord ++ tailWord_182125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182125).length < 2 ^ (prefixWord ++ tailWord_182125).sum := by decide
  have hdescent : baseEnd_182125 < baseStart_182125 := by decide
  rcases family_descends (prefixWord ++ tailWord_182125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182142 : List Nat := [4, 2, 3, 1, 1, 9]
def baseStart_182142 : Nat := 118140960795 + 182142 * 2 ^ 59
def prefixEnd_182142 : Nat := 4983230072969 + 3 ^ 40 * 182142 * 2
def baseEnd_182142 : Nat := 3079058217986225589707

theorem tailTrace_182142 : CollatzResearch.WordTrace tailWord_182142 prefixEnd_182142 3079058217986225589707 := by
  unfold tailWord_182142
  simp only [CollatzResearch.WordTrace]
  refine ⟨830408063267264527765585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4428843004092077481416453 830408063267264527765585)
  ·
    refine ⟨622806047450448395824189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 830408063267264527765585 622806047450448395824189)
    ·
      refine ⟨233552267793918148434071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 622806047450448395824189 233552267793918148434071)
      ·
        refine ⟨350328401690877222651107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233552267793918148434071 350328401690877222651107)
        ·
          refine ⟨525492602536315833976661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350328401690877222651107 525492602536315833976661)
          ·
            refine ⟨3079058217986225589707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 525492602536315833976661 3079058217986225589707)
            ·
              rfl

theorem cell20_182142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 9].length) (baseStart_182142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182142 prefixEnd_182142 := by exact prefixLift 182142
  have htrace : WordTrace (prefixWord ++ tailWord_182142) baseStart_182142 baseEnd_182142 := by
    simpa [prefixWord, tailWord_182142, baseEnd_182142] using wordTrace_append hprefix tailTrace_182142
  have hstable : (prefixWord ++ tailWord_182142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182142).length < 2 ^ (prefixWord ++ tailWord_182142).sum := by decide
  have hdescent : baseEnd_182142 < baseStart_182142 := by decide
  rcases family_descends (prefixWord ++ tailWord_182142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182145 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_182145 : Nat := 118140960795 + 182145 * 2 ^ 59
def prefixEnd_182145 : Nat := 4983230072969 + 3 ^ 40 * 182145 * 2
def baseEnd_182145 : Nat := 83135941167373413822077

theorem tailTrace_182145 : CollatzResearch.WordTrace tailWord_182145 prefixEnd_182145 83135941167373413822077 := by
  unfold tailWord_182145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643373925127247734483889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4428915950084831822989259 6643373925127247734483889)
  ·
    refine ⟨4982530443845435800862917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6643373925127247734483889 4982530443845435800862917)
    ·
      refine ⟨934224458221019212661797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4982530443845435800862917 934224458221019212661797)
      ·
        refine ⟨175167085916441102374087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 934224458221019212661797 175167085916441102374087)
        ·
          refine ⟨262750628874661653561131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175167085916441102374087 262750628874661653561131)
          ·
            refine ⟨394125943311992480341697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262750628874661653561131 394125943311992480341697)
            ·
              refine ⟨295594457483994360256273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394125943311992480341697 295594457483994360256273)
              ·
                refine ⟨221695843112995770192205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295594457483994360256273 221695843112995770192205)
                ·
                  refine ⟨83135941167373413822077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221695843112995770192205 83135941167373413822077)
                  ·
                    rfl

theorem cell20_182145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_182145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182145 prefixEnd_182145 := by exact prefixLift 182145
  have htrace : WordTrace (prefixWord ++ tailWord_182145) baseStart_182145 baseEnd_182145 := by
    simpa [prefixWord, tailWord_182145, baseEnd_182145] using wordTrace_append hprefix tailTrace_182145
  have hstable : (prefixWord ++ tailWord_182145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182145).length < 2 ^ (prefixWord ++ tailWord_182145).sum := by decide
  have hdescent : baseEnd_182145 < baseStart_182145 := by decide
  rcases family_descends (prefixWord ++ tailWord_182145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182149 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_182149 : Nat := 118140960795 + 182149 * 2 ^ 59
def prefixEnd_182149 : Nat := 4983230072969 + 3 ^ 40 * 182149 * 2
def baseEnd_182149 : Nat := 83137766876367177688727

theorem tailTrace_182149 : CollatzResearch.WordTrace tailWord_182149 prefixEnd_182149 83137766876367177688727 := by
  unfold tailWord_182149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643519817112756417629501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4429013211408504278419667 6643519817112756417629501)
  ·
    refine ⟨2491319931417283656611063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6643519817112756417629501 2491319931417283656611063)
    ·
      refine ⟨3736979897125925484916595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491319931417283656611063 3736979897125925484916595)
      ·
        refine ⟨5605469845688888227374893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736979897125925484916595 5605469845688888227374893)
        ·
          refine ⟨2102051192133333085265585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5605469845688888227374893 2102051192133333085265585)
          ·
            refine ⟨1576538394099999813949189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102051192133333085265585 1576538394099999813949189)
            ·
              refine ⟨295600948893749965115473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1576538394099999813949189 295600948893749965115473)
              ·
                refine ⟨221700711670312473836605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295600948893749965115473 221700711670312473836605)
                ·
                  refine ⟨83137766876367177688727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221700711670312473836605 83137766876367177688727)
                  ·
                    rfl

theorem cell20_182149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_182149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182149 prefixEnd_182149 := by exact prefixLift 182149
  have htrace : WordTrace (prefixWord ++ tailWord_182149) baseStart_182149 baseEnd_182149 := by
    simpa [prefixWord, tailWord_182149, baseEnd_182149] using wordTrace_append hprefix tailTrace_182149
  have hstable : (prefixWord ++ tailWord_182149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182149).length < 2 ^ (prefixWord ++ tailWord_182149).sum := by decide
  have hdescent : baseEnd_182149 < baseStart_182149 := by decide
  rcases family_descends (prefixWord ++ tailWord_182149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182152 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_182152 : Nat := 118140960795 + 182152 * 2 ^ 59
def prefixEnd_182152 : Nat := 4983230072969 + 3 ^ 40 * 182152 * 2
def baseEnd_182152 : Nat := 83139136158112500588715

theorem tailTrace_182152 : CollatzResearch.WordTrace tailWord_182152 prefixEnd_182152 83139136158112500588715 := by
  unfold tailWord_182152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321814618050943964994355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4429086157401258619992473 3321814618050943964994355)
  ·
    refine ⟨4982721927076415947491533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3321814618050943964994355 4982721927076415947491533)
    ·
      refine ⟨1868520722653655980309325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4982721927076415947491533 1868520722653655980309325)
      ·
        refine ⟨700695270995120992615997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1868520722653655980309325 700695270995120992615997)
        ·
          refine ⟨262760726623170372230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700695270995120992615997 262760726623170372230999)
          ·
            refine ⟨394141089934755558346499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262760726623170372230999 394141089934755558346499)
            ·
              refine ⟨591211634902133337519749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394141089934755558346499 591211634902133337519749)
              ·
                refine ⟨110852181544150000784953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591211634902133337519749 110852181544150000784953)
                ·
                  refine ⟨83139136158112500588715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110852181544150000784953 83139136158112500588715)
                  ·
                    rfl

theorem cell20_182152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_182152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182152 prefixEnd_182152 := by exact prefixLift 182152
  have htrace : WordTrace (prefixWord ++ tailWord_182152) baseStart_182152 baseEnd_182152 := by
    simpa [prefixWord, tailWord_182152, baseEnd_182152] using wordTrace_append hprefix tailTrace_182152
  have hstable : (prefixWord ++ tailWord_182152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182152).length < 2 ^ (prefixWord ++ tailWord_182152).sum := by decide
  have hdescent : baseEnd_182152 < baseStart_182152 := by decide
  rcases family_descends (prefixWord ++ tailWord_182152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182180 : List Nat := [2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_182180 : Nat := 118140960795 + 182180 * 2 ^ 59
def prefixEnd_182180 : Nat := 4983230072969 + 3 ^ 40 * 182180 * 2
def baseEnd_182180 : Nat := 27717305373689615885089

theorem tailTrace_182180 : CollatzResearch.WordTrace tailWord_182180 prefixEnd_182180 27717305373689615885089 := by
  unfold tailWord_182180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322325240000224356003997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4429766986666965808005329 3322325240000224356003997)
  ·
    refine ⟨1245871965000084133501499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3322325240000224356003997 1245871965000084133501499)
    ·
      refine ⟨1868807947500126200252249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245871965000084133501499 1868807947500126200252249)
      ·
        refine ⟨1401605960625094650189187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1868807947500126200252249 1401605960625094650189187)
        ·
          refine ⟨2102408940937641975283781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401605960625094650189187 2102408940937641975283781)
          ·
            refine ⟨394201676425807870365709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2102408940937641975283781 394201676425807870365709)
            ·
              refine ⟨147825628659677951387141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394201676425807870365709 147825628659677951387141)
              ·
                refine ⟨27717305373689615885089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147825628659677951387141 27717305373689615885089)
                ·
                  rfl

theorem cell20_182180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_182180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182180 prefixEnd_182180 := by exact prefixLift 182180
  have htrace : WordTrace (prefixWord ++ tailWord_182180) baseStart_182180 baseEnd_182180 := by
    simpa [prefixWord, tailWord_182180, baseEnd_182180] using wordTrace_append hprefix tailTrace_182180
  have hstable : (prefixWord ++ tailWord_182180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182180).length < 2 ^ (prefixWord ++ tailWord_182180).sum := by decide
  have hdescent : baseEnd_182180 < baseStart_182180 := by decide
  rcases family_descends (prefixWord ++ tailWord_182180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182204 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_182204 : Nat := 118140960795 + 182204 * 2 ^ 59
def prefixEnd_182204 : Nat := 4983230072969 + 3 ^ 40 * 182204 * 2
def baseEnd_182204 : Nat := 83162870375031430855169

theorem tailTrace_182204 : CollatzResearch.WordTrace tailWord_182204 prefixEnd_182204 83162870375031430855169 := by
  unfold tailWord_182204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322762915956750405440833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4430350554609000540587777 3322762915956750405440833)
  ·
    refine ⟨2492072186967562804080625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3322762915956750405440833 2492072186967562804080625)
    ·
      refine ⟨1869054140225672103060469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2492072186967562804080625 1869054140225672103060469)
      ·
        refine ⟨175223825646156759661919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1869054140225672103060469 175223825646156759661919)
        ·
          refine ⟨262835738469235139492879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175223825646156759661919 262835738469235139492879)
          ·
            refine ⟨394253607703852709239319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262835738469235139492879 394253607703852709239319)
            ·
              refine ⟨591380411555779063858979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394253607703852709239319 591380411555779063858979)
              ·
                refine ⟨887070617333668595788469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591380411555779063858979 887070617333668595788469)
                ·
                  refine ⟨83162870375031430855169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887070617333668595788469 83162870375031430855169)
                  ·
                    rfl

theorem cell20_182204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_182204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182204 prefixEnd_182204 := by exact prefixLift 182204
  have htrace : WordTrace (prefixWord ++ tailWord_182204) baseStart_182204 baseEnd_182204 := by
    simpa [prefixWord, tailWord_182204, baseEnd_182204] using wordTrace_append hprefix tailTrace_182204
  have hstable : (prefixWord ++ tailWord_182204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182204).length < 2 ^ (prefixWord ++ tailWord_182204).sum := by decide
  have hdescent : baseEnd_182204 < baseStart_182204 := by decide
  rcases family_descends (prefixWord ++ tailWord_182204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182208 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_182208 : Nat := 118140960795 + 182208 * 2 ^ 59
def prefixEnd_182208 : Nat := 4983230072969 + 3 ^ 40 * 182208 * 2
def baseEnd_182208 : Nat := 83164696084025194721819

theorem tailTrace_182208 : CollatzResearch.WordTrace tailWord_182208 prefixEnd_182208 83164696084025194721819 := by
  unfold tailWord_182208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322835861949504747013639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4430447815932672996018185 3322835861949504747013639)
  ·
    refine ⟨4984253792924257120520459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3322835861949504747013639 4984253792924257120520459)
    ·
      refine ⟨7476380689386385680780689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984253792924257120520459 7476380689386385680780689)
      ·
        refine ⟨5607285517039789260585517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7476380689386385680780689 5607285517039789260585517)
        ·
          refine ⟨2102732068889920972719569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5607285517039789260585517 2102732068889920972719569)
          ·
            refine ⟨1577049051667440729539677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102732068889920972719569 1577049051667440729539677)
            ·
              refine ⟨591393394375290273577379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1577049051667440729539677 591393394375290273577379)
              ·
                refine ⟨887090091562935410366069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591393394375290273577379 887090091562935410366069)
                ·
                  refine ⟨83164696084025194721819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887090091562935410366069 83164696084025194721819)
                  ·
                    rfl

theorem cell20_182208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_182208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182208 prefixEnd_182208 := by exact prefixLift 182208
  have htrace : WordTrace (prefixWord ++ tailWord_182208) baseStart_182208 baseEnd_182208 := by
    simpa [prefixWord, tailWord_182208, baseEnd_182208] using wordTrace_append hprefix tailTrace_182208
  have hstable : (prefixWord ++ tailWord_182208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182208).length < 2 ^ (prefixWord ++ tailWord_182208).sum := by decide
  have hdescent : baseEnd_182208 < baseStart_182208 := by decide
  rcases family_descends (prefixWord ++ tailWord_182208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182239 : List Nat := [1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_182239 : Nat := 118140960795 + 182239 * 2 ^ 59
def prefixEnd_182239 : Nat := 4983230072969 + 3 ^ 40 * 182239 * 2
def baseEnd_182239 : Nat := 27726281776242288229453

theorem tailTrace_182239 : CollatzResearch.WordTrace tailWord_182239 prefixEnd_182239 27726281776242288229453 := by
  unfold tailWord_182239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646802386786701788405771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4431201591191134525603847 6646802386786701788405771)
  ·
    refine ⟨9970203580180052682608657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6646802386786701788405771 9970203580180052682608657)
    ·
      refine ⟨7477652685135039511956493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9970203580180052682608657 7477652685135039511956493)
      ·
        refine ⟨2804119756925639816983685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7477652685135039511956493 2804119756925639816983685)
        ·
          refine ⟨525772454423557465684441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2804119756925639816983685 525772454423557465684441)
          ·
            refine ⟨394329340817668099263331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525772454423557465684441 394329340817668099263331)
            ·
              refine ⟨591494011226502148894997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394329340817668099263331 591494011226502148894997)
              ·
                refine ⟨27726281776242288229453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591494011226502148894997 27726281776242288229453)
                ·
                  rfl

theorem cell20_182239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_182239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182239 prefixEnd_182239 := by exact prefixLift 182239
  have htrace : WordTrace (prefixWord ++ tailWord_182239) baseStart_182239 baseEnd_182239 := by
    simpa [prefixWord, tailWord_182239, baseEnd_182239] using wordTrace_append hprefix tailTrace_182239
  have hstable : (prefixWord ++ tailWord_182239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182239).length < 2 ^ (prefixWord ++ tailWord_182239).sum := by decide
  have hdescent : baseEnd_182239 < baseStart_182239 := by decide
  rcases family_descends (prefixWord ++ tailWord_182239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182276 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_182276 : Nat := 118140960795 + 182276 * 2 ^ 59
def prefixEnd_182276 : Nat := 4983230072969 + 3 ^ 40 * 182276 * 2
def baseEnd_182276 : Nat := 83195733136919180454875

theorem tailTrace_182276 : CollatzResearch.WordTrace tailWord_182276 prefixEnd_182276 83195733136919180454875 := by
  unfold tailWord_182276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324075943826328553751341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4432101258435104738335121 3324075943826328553751341)
  ·
    refine ⟨1246528478934873207656753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3324075943826328553751341 1246528478934873207656753)
    ·
      refine ⟨934896359201154905742565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1246528478934873207656753 934896359201154905742565)
      ·
        refine ⟨175293067350216544826731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 934896359201154905742565 175293067350216544826731)
        ·
          refine ⟨262939601025324817240097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175293067350216544826731 262939601025324817240097)
          ·
            refine ⟨197204700768993612930073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262939601025324817240097 197204700768993612930073)
            ·
              refine ⟨147903525576745209697555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197204700768993612930073 147903525576745209697555)
              ·
                refine ⟨221855288365117814546333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147903525576745209697555 221855288365117814546333)
                ·
                  refine ⟨83195733136919180454875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221855288365117814546333 83195733136919180454875)
                  ·
                    rfl

theorem cell20_182276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_182276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182276 prefixEnd_182276 := by exact prefixLift 182276
  have htrace : WordTrace (prefixWord ++ tailWord_182276) baseStart_182276 baseEnd_182276 := by
    simpa [prefixWord, tailWord_182276, baseEnd_182276] using wordTrace_append hprefix tailTrace_182276
  have hstable : (prefixWord ++ tailWord_182276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182276).length < 2 ^ (prefixWord ++ tailWord_182276).sum := by decide
  have hdescent : baseEnd_182276 < baseStart_182276 := by decide
  rcases family_descends (prefixWord ++ tailWord_182276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182277 : List Nat := [1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_182277 : Nat := 118140960795 + 182277 * 2 ^ 59
def prefixEnd_182277 : Nat := 4983230072969 + 3 ^ 40 * 182277 * 2
def baseEnd_182277 : Nat := 27732063188055873807179

theorem tailTrace_182277 : CollatzResearch.WordTrace tailWord_182277 prefixEnd_182277 27732063188055873807179 := by
  unfold tailWord_182277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648188360649034278289085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4432125573766022852192723 6648188360649034278289085)
  ·
    refine ⟨2493070635243387854358407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6648188360649034278289085 2493070635243387854358407)
    ·
      refine ⟨3739605952865081781537611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493070635243387854358407 3739605952865081781537611)
      ·
        refine ⟨5609408929297622672306417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739605952865081781537611 5609408929297622672306417)
        ·
          refine ⟨4207056696973217004229813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5609408929297622672306417 4207056696973217004229813)
          ·
            refine ⟨394411565341239094146545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4207056696973217004229813 394411565341239094146545)
            ·
              refine ⟨295808674005929320609909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394411565341239094146545 295808674005929320609909)
              ·
                refine ⟨27732063188055873807179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295808674005929320609909 27732063188055873807179)
                ·
                  rfl

theorem cell20_182277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_182277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182277 prefixEnd_182277 := by exact prefixLift 182277
  have htrace : WordTrace (prefixWord ++ tailWord_182277) baseStart_182277 baseEnd_182277 := by
    simpa [prefixWord, tailWord_182277, baseEnd_182277] using wordTrace_append hprefix tailTrace_182277
  have hstable : (prefixWord ++ tailWord_182277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182277).length < 2 ^ (prefixWord ++ tailWord_182277).sum := by decide
  have hdescent : baseEnd_182277 < baseStart_182277 := by decide
  rcases family_descends (prefixWord ++ tailWord_182277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182291 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_182291 : Nat := 118140960795 + 182291 * 2 ^ 59
def prefixEnd_182291 : Nat := 4983230072969 + 3 ^ 40 * 182291 * 2
def baseEnd_182291 : Nat := 83202579545645794954813

theorem tailTrace_182291 : CollatzResearch.WordTrace tailWord_182291 prefixEnd_182291 83202579545645794954813 := by
  unfold tailWord_182291
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648698982598314669298727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4432465988398876446199151 6648698982598314669298727)
  ·
    refine ⟨9973048473897472003948091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6648698982598314669298727 9973048473897472003948091)
    ·
      refine ⟨14959572710846208005922137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9973048473897472003948091 14959572710846208005922137)
      ·
        refine ⟨11219679533134656004441603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14959572710846208005922137 11219679533134656004441603)
        ·
          refine ⟨16829519299701984006662405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11219679533134656004441603 16829519299701984006662405)
          ·
            refine ⟨3155534868694122001249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16829519299701984006662405 3155534868694122001249201)
            ·
              refine ⟨2366651151520591500936901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155534868694122001249201 2366651151520591500936901)
              ·
                refine ⟨443747090910110906425669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2366651151520591500936901 443747090910110906425669)
                ·
                  refine ⟨83202579545645794954813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443747090910110906425669 83202579545645794954813)
                  ·
                    rfl

theorem cell20_182291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_182291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182291 prefixEnd_182291 := by exact prefixLift 182291
  have htrace : WordTrace (prefixWord ++ tailWord_182291) baseStart_182291 baseEnd_182291 := by
    simpa [prefixWord, tailWord_182291, baseEnd_182291] using wordTrace_append hprefix tailTrace_182291
  have hstable : (prefixWord ++ tailWord_182291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182291).length < 2 ^ (prefixWord ++ tailWord_182291).sum := by decide
  have hdescent : baseEnd_182291 < baseStart_182291 := by decide
  rcases family_descends (prefixWord ++ tailWord_182291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182318 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_182318 : Nat := 118140960795 + 182318 * 2 ^ 59
def prefixEnd_182318 : Nat := 4983230072969 + 3 ^ 40 * 182318 * 2
def baseEnd_182318 : Nat := 83214903081353701054703

theorem tailTrace_182318 : CollatzResearch.WordTrace tailWord_182318 prefixEnd_182318 83214903081353701054703 := by
  unfold tailWord_182318
  simp only [CollatzResearch.WordTrace]
  refine ⟨831210469187562285066451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4433122502333665520354405 831210469187562285066451)
  ·
    refine ⟨1246815703781343427599677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831210469187562285066451 1246815703781343427599677)
    ·
      refine ⟨467555888918003785349879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1246815703781343427599677 467555888918003785349879)
      ·
        refine ⟨701333833377005678024819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467555888918003785349879 701333833377005678024819)
        ·
          refine ⟨1052000750065508517037229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701333833377005678024819 1052000750065508517037229)
          ·
            refine ⟨394500281274565693888961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052000750065508517037229 394500281274565693888961)
            ·
              refine ⟨295875210955924270416721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394500281274565693888961 295875210955924270416721)
              ·
                refine ⟨221906408216943202812541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295875210955924270416721 221906408216943202812541)
                ·
                  refine ⟨83214903081353701054703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221906408216943202812541 83214903081353701054703)
                  ·
                    rfl

theorem cell20_182318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_182318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182318 prefixEnd_182318 := by exact prefixLift 182318
  have htrace : WordTrace (prefixWord ++ tailWord_182318) baseStart_182318 baseEnd_182318 := by
    simpa [prefixWord, tailWord_182318, baseEnd_182318] using wordTrace_append hprefix tailTrace_182318
  have hstable : (prefixWord ++ tailWord_182318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182318).length < 2 ^ (prefixWord ++ tailWord_182318).sum := by decide
  have hdescent : baseEnd_182318 < baseStart_182318 := by decide
  rcases family_descends (prefixWord ++ tailWord_182318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182370 : List Nat := [3, 3, 2, 2, 2, 1, 7]
def baseStart_182370 : Nat := 118140960795 + 182370 * 2 ^ 59
def prefixEnd_182370 : Nat := 4983230072969 + 3 ^ 40 * 182370 * 2
def baseEnd_182370 : Nat := 9248737477585847924573

theorem tailTrace_182370 : CollatzResearch.WordTrace tailWord_182370 prefixEnd_182370 9248737477585847924573 := by
  unfold tailWord_182370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662895087328027790356141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4434386899541407440949709 1662895087328027790356141)
  ·
    refine ⟨623585657748010421383553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1662895087328027790356141 623585657748010421383553)
    ·
      refine ⟨467689243311007816037665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623585657748010421383553 467689243311007816037665)
      ·
        refine ⟨350766932483255862028249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467689243311007816037665 350766932483255862028249)
        ·
          refine ⟨263075199362441896521187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350766932483255862028249 263075199362441896521187)
          ·
            refine ⟨394612799043662844781781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263075199362441896521187 394612799043662844781781)
            ·
              refine ⟨9248737477585847924573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 394612799043662844781781 9248737477585847924573)
              ·
                rfl

theorem cell20_182370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_182370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_182370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_182370 prefixEnd_182370 := by exact prefixLift 182370
  have htrace : WordTrace (prefixWord ++ tailWord_182370) baseStart_182370 baseEnd_182370 := by
    simpa [prefixWord, tailWord_182370, baseEnd_182370] using wordTrace_append hprefix tailTrace_182370
  have hstable : (prefixWord ++ tailWord_182370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182370).length < 2 ^ (prefixWord ++ tailWord_182370).sum := by decide
  have hdescent : baseEnd_182370 < baseStart_182370 := by decide
  rcases family_descends (prefixWord ++ tailWord_182370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
